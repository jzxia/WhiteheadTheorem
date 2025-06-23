import WhiteheadTheorem.Shapes.Disk
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
import Mathlib.CategoryTheory.Functor.OfSequence
-- import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# CW-complexes
This file defines (relative) CW-complexes.
## Main definitions
* `RelativeCWComplex`: A relative CW-complex is the colimit of an expanding sequence of subspaces
  `sk i` (called the $(i-1)$-skeleton) for `i ≥ 0`, where `sk 0` (i.e., the $(-1)$-skeleton) is an
  arbitrary topological space, and each `sk (n + 1)` (i.e., the $n$-skeleton) is obtained from
  `sk n` (i.e., the $(n-1)$-skeleton) by attaching `n`-disks.
* `CWComplex`: A CW-complex is a relative CW-complex whose `sk 0` (i.e., $(-1)$-skeleton) is empty.
## References
* [R. Fritsch and R. Piccinini, *Cellular Structures in Topology*][fritsch-piccinini1990]
* The definition of CW-complexes follows David Wärn's suggestion on
  [Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Do.20we.20have.20CW.20complexes.3F/near/231769080).
-/


open CategoryTheory TopCat

-- universe u

namespace RelCWComplex

/-- A type witnessing that `X'` is obtained from `X` by attaching generalized cells `f : S ⟶ D` -/
structure AttachGeneralizedCells.{u} {S D : TopCat.{u}} (f : S ⟶ D) (X X' : TopCat.{u}) where
  /-- The index type over the generalized cells -/
  cells : Type u
  /-- An attaching map for each generalized cell -/
  attachMaps : cells → (S ⟶ X)
  /-- `X'` is the pushout of `∐ S ⟶ X` and `∐ S ⟶ ∐ D`. -/
  isoPushout : X' ≅ Limits.pushout (Limits.Sigma.desc attachMaps) (Limits.Sigma.map fun _ ↦ f)

/-- A type witnessing that `X'` is obtained from `X` by attaching `(n + 1)`-disks -/
abbrev AttachCells.{u} (n : ℕ) := AttachGeneralizedCells.{u} (diskBoundaryIncl n)

end RelCWComplex


/-- A relative CW-complex consists of an expanding sequence of subspaces `sk i` (called the
$(i-1)$-skeleton) for `i ≥ 0`, where `sk 0` (i.e., the $(-1)$-skeleton) is an arbitrary topological
space, and each `sk (n + 1)` (i.e., the `n`-skeleton) is obtained from `sk n` (i.e., the
$(n-1)$-skeleton) by attaching `n`-disks. -/
structure RelCWComplex where
  /-- The skeletons. Note: `sk i` is usually called the $(i-1)$-skeleton in the math literature. -/
  sk : ℕ → TopCat.{u}
  /-- Each `sk (n + 1)` (i.e., the $n$-skeleton) is obtained from `sk n`
  (i.e., the $(n-1)$-skeleton) by attaching `n`-disks. -/
  attachCells (n : ℕ) : RelCWComplex.AttachCells n (sk n) (sk (n + 1))

/-- A CW-complex is a relative CW-complex whose `sk 0` (i.e., $(-1)$-skeleton) is empty. -/
structure CWComplex.{u} extends RelCWComplex.{u} where
  /-- `sk 0` (i.e., the $(-1)$-skeleton) is empty. -/
  isEmpty_sk_zero : IsEmpty (sk 0)


namespace RelCWComplex

noncomputable section Topology

variable {n : ℕ} {X X' : TopCat.{u}}

/-- The inclusion map from `X` to `X'`, given that `X'` is obtained from `X` by attaching
`(n + 1)`-disks -/
def AttachCells.incl (att : AttachCells n X X') : X ⟶ X' :=
  Limits.pushout.inl (Limits.Sigma.desc att.attachMaps)
    (Limits.Sigma.map fun _ ↦ diskBoundaryIncl n) ≫ att.isoPushout.inv

/-- The top side of the pushout square -/
abbrev AttachCells.sigmaAttachMaps (att : AttachCells n X X') :=
  Limits.Sigma.desc att.attachMaps

/-- The left side of the pushout square -/
abbrev AttachCells.sigmaDiskBoundaryIncl (att : AttachCells n X X') :
    (∐ fun (_ : att.cells) ↦ ∂𝔻 n) ⟶ ∐ fun (_ : att.cells) ↦ 𝔻 n :=
  Limits.Sigma.map fun (_ : att.cells) ↦ diskBoundaryIncl n

/-- The right side of the pushout square
(TODO: after updating mathlib on 2025-03-08,
using the abbreviation `att.sigmaDiskBoundaryIncl` results in type mismatch,
which seems to be a universe level issue.
So the abbreviation is temporarily replaced with the full definition.)-/
abbrev AttachCells.pushout_inl (att : AttachCells.{u} n X X') :=
  Limits.pushout.inl att.sigmaAttachMaps
    (Limits.Sigma.map fun (_ : att.cells) ↦ diskBoundaryIncl n)
--  Limits.pushout.inl att.sigmaAttachMaps att.sigmaDiskBoundaryIncl

/-- The bottom side of the pushout square -/
abbrev AttachCells.pushout_inr (att : AttachCells n X X') :=
  Limits.pushout.inr att.sigmaAttachMaps
    (Limits.Sigma.map fun (_ : att.cells) ↦ diskBoundaryIncl n)
-- Limits.pushout.inr att.sigmaAttachMaps att.sigmaDiskBoundaryIncl

/-- The pushout square is a pushout. -/
def AttachCells.pushout_isPushout (att : AttachCells n X X') :
    IsPushout att.sigmaAttachMaps (Limits.Sigma.map fun (_ : att.cells) ↦ diskBoundaryIncl n)
      att.pushout_inl att.pushout_inr :=
  IsPushout.of_hasPushout att.sigmaAttachMaps (Limits.Sigma.map fun (_ : att.cells) ↦ diskBoundaryIncl n)

/-- The inclusion map from `sk n` (i.e., the $(n-1)$-skeleton) to `sk (n + 1)` (i.e., the
$n$-skeleton) of a relative CW-complex -/
def skInclSucc (X : RelCWComplex) (n : ℕ) : X.sk n ⟶ X.sk (n + 1) :=
  (X.attachCells n).incl

/-- The inclusion map from `sk n` (i.e., the $(n-1)$-skeleton) to `sk m` (i.e., the
$(m-1)$-skeleton) of a relative CW-complex -/
def skInclToSk (X : RelCWComplex) {n : ℕ} {m : ℕ} (hnm : n ≤ m) : X.sk n ⟶ X.sk m :=
  (Functor.ofSequence X.skInclSucc).map (homOfLE hnm)
  -- Functor.OfSequence.map X.skInclSucc n m hnm

-- def sigmaAttachMaps (X : RelativeCWComplex.{u}) (n : ℕ) := (X.attachCells n).sigmaAttachMaps

-- def sigmaDiskBoundaryIncl (X : RelativeCWComplex.{u}) (n : ℕ) :=
--   (X.attachCells n).sigmaDiskBoundaryIncl

/-- The topology on a relative CW-complex -/
def toTopCat (X : RelCWComplex) : TopCat.{u} :=
  Limits.colimit (Functor.ofSequence X.skInclSucc)

instance : Coe RelCWComplex TopCat where
  coe X := toTopCat X

instance : Coe CWComplex TopCat where
  coe X := toTopCat X.toRelCWComplex

/-- The inclusion map from `sk n` (i.e., the $(n-1)$-skeleton of `X`) to `X` -/
def skIncl (X : RelCWComplex.{u}) (n : ℕ) : X.sk n ⟶ X :=
  Limits.colimit.ι (Functor.ofSequence _) n

@[simp]
lemma skInclSucc_skIncl_eq (X : RelCWComplex.{u}) (n : ℕ) :
    X.skInclSucc n ≫ X.skIncl (n + 1) = X.skIncl n := by
  unfold skInclSucc skIncl
  convert Limits.colimit.w (Functor.ofSequence X.skInclSucc) <| homOfLE <| Nat.le_succ <| n
  simp only [Nat.succ_eq_add_one, homOfLE_leOfHom, Functor.ofSequence_map_homOfLE_succ]
  rfl

end Topology


namespace AttachGeneralizedCells

variable {S D : TopCat.{u}} {f : S ⟶ D} {X X' : TopCat.{u}}
variable (att : AttachGeneralizedCells f X X') (α : att.cells)

noncomputable abbrev pushout_inl :=
  Limits.pushout.inl (Limits.Sigma.desc att.attachMaps) (Limits.Sigma.map fun _ ↦ f)
noncomputable abbrev pushout_inr :=
  Limits.pushout.inr (Limits.Sigma.desc att.attachMaps) (Limits.Sigma.map fun _ ↦ f)

lemma attachMaps_apply_eq_ι_desc : att.attachMaps α =
    Limits.Sigma.ι (fun _ ↦ S) α ≫ Limits.Sigma.desc att.attachMaps := by
  simp only [Limits.colimit.ι_desc, Limits.Cofan.mk_pt, Limits.Cofan.mk_ι_app]

/--
```
S --> ∐ S
|      |
f      |
↓      ↓
D --> ∐ D
```
-/
@[reassoc]
lemma w_sigma_cells : f ≫ Limits.Sigma.ι (fun _ ↦ D) α =
    Limits.Sigma.ι (fun _ ↦ S) α ≫ (Limits.Sigma.map fun _ ↦ f) := by
  simp only [Limits.ι_colimMap, Discrete.functor_obj_eq_as, Discrete.natTrans_app]

/--
```
S --> ∐ S --> X
|      |      |
f      |      |
↓      ↓      ↓    ≅
D --> ∐ D --> ⬝ ------> X'
```
-/
@[reassoc]
lemma w_cell' : f ≫ Limits.Sigma.ι (fun _ ↦ D) α ≫ att.pushout_inr =
    Limits.Sigma.ι (fun _ ↦ S) α ≫ Limits.Sigma.desc att.attachMaps ≫ att.pushout_inl := by
  rw [w_sigma_cells_assoc, Limits.pushout.condition]

/--
```
S ----------> X
|             |
f             |
↓             ↓    ≅
D --> ∐ D --> ⬝ ------> X'
```
-/
@[reassoc]
lemma w_cell : f ≫ Limits.Sigma.ι (fun _ ↦ D) α ≫ att.pushout_inr =
    att.attachMaps α ≫ att.pushout_inl := by
  rw [attachMaps_apply_eq_ι_desc, w_cell']; rfl

end AttachGeneralizedCells

end RelCWComplex

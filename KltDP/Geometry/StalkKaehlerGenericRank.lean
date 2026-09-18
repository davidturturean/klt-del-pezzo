import KltDP.Geometry.RationalTreePicardIntrinsicNode
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Rank of the original stalk Kähler module at the function field

The scalar tower is proved from the actual stalk generization map and
the original structure morphism. The pinned Kähler localization and
rank-localization theorems then identify the two native module ranks.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace nonZeroDivisors

universe u

namespace KltDP.Geometry.StalkKaehlerGenericRank

open IntrinsicNodal

variable {k : Type u} [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))

/-- Original base-to-stalk maps commute with actual generization. -/
theorem baseToStalkMap_specializes {x y : X} (h : x ⤳ y) :
    baseToStalkMap f y ≫ X.presheaf.stalkSpecializes h = baseToStalkMap f x := by
  let U : X.Opens := (X.affineCover.map y).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.map y)
  have hy : y ∈ U := X.affineCover.covers y
  rw [← baseToAffineSectionsMap_germ f hU y hy, Category.assoc,
    X.presheaf.germ_stalkSpecializes, baseToAffineSectionsMap_germ]

/-- The function-field scalar action is the original generic-stalk algebra. -/
theorem stalk_functionField_scalarTower [IrreducibleSpace X] (x : X) :
    letI := stalkAlgebra f x
    letI := stalkAlgebra f (genericPoint X)
    IsScalarTower k (X.presheaf.stalk x) X.functionField := by
  letI := stalkAlgebra f x
  letI := stalkAlgebra f (genericPoint X)
  apply IsScalarTower.of_algebraMap_eq'
  exact congrArg (fun g : CommRingCat.of k ⟶ X.functionField => g.hom)
    (baseToStalkMap_specializes f ((genericPoint_spec X).specializes trivial)).symm

/-- The original local Kähler rank equals its rank over the original function
field, without any regularity, smoothness, or target-rank assumption. -/
theorem rank_eq_functionField [IsIntegral X] (x : X) :
    letI := stalkAlgebra f x
    letI := stalkAlgebra f (genericPoint X)
    Module.rank (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x)) =
      Module.rank X.functionField (KaehlerDifferential k X.functionField) := by
  letI := stalkAlgebra f x
  letI := stalkAlgebra f (genericPoint X)
  letI := stalk_functionField_scalarTower f x
  calc
    Module.rank (X.presheaf.stalk x) (KaehlerDifferential k (X.presheaf.stalk x)) =
        Module.rank (X.presheaf.stalk x) (KaehlerDifferential k X.functionField) :=
      (IsLocalizedModule.rank_eq (X.presheaf.stalk x)⁰ le_rfl
        (KaehlerDifferential.map k k (X.presheaf.stalk x) X.functionField)).symm
    _ = Module.rank X.functionField (KaehlerDifferential k X.functionField) :=
      (IsLocalization.rank_eq X.functionField (X.presheaf.stalk x)⁰ le_rfl).symm

end KltDP.Geometry.StalkKaehlerGenericRank

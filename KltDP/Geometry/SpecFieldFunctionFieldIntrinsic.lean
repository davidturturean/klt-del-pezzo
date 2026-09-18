import KltDP.Geometry.RationalTreePicardIntrinsicNode
import Mathlib.AlgebraicGeometry.FunctionField

/-! The original function field of Spec k is k for the exact intrinsic
action of its identity structure map. The equivalence is obtained from
the original stalk scalar map, using the pinned closed-point stalk iso. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.SpecFieldFunctionFieldIntrinsic

open IntrinsicNodal

variable (k : Type u) [Field k]

theorem scalarMap_isIso :
    IsIso (baseToStalkMap (𝟙 (Spec (CommRingCat.of k)))
      (genericPoint (Spec (CommRingCat.of k)))) := by
  have hx : genericPoint (Spec (CommRingCat.of k)) =
      IsLocalRing.closedPoint (CommRingCat.of k) := Subsingleton.elim _ _
  rw [hx]
  have h : baseToStalkMap (𝟙 (Spec (CommRingCat.of k)))
      (IsLocalRing.closedPoint (CommRingCat.of k)) =
        (stalkClosedPointIso (CommRingCat.of k)).inv := by
    apply Spec.map_injective
    rw [Spec_map_baseToStalkMap, Category.comp_id, Spec_stalkClosedPointIso]
  rw [h]
  infer_instance

def equiv :
    letI := stalkAlgebra (𝟙 (Spec (CommRingCat.of k)))
      (genericPoint (Spec (CommRingCat.of k)))
    (Spec (CommRingCat.of k)).functionField ≃ₐ[k] k := by
  letI := stalkAlgebra (𝟙 (Spec (CommRingCat.of k)))
    (genericPoint (Spec (CommRingCat.of k)))
  letI := scalarMap_isIso k
  exact (AlgEquiv.ofBijective
    (Algebra.ofId k (Spec (CommRingCat.of k)).functionField)
    (ConcreteCategory.bijective_of_isIso
      (baseToStalkMap (𝟙 (Spec (CommRingCat.of k)))
        (genericPoint (Spec (CommRingCat.of k)))))).symm

theorem equiv_symm_toRingHom :
    letI := stalkAlgebra (𝟙 (Spec (CommRingCat.of k)))
      (genericPoint (Spec (CommRingCat.of k)))
    (equiv k).symm.toRingHom =
      (baseToStalkMap (𝟙 (Spec (CommRingCat.of k)))
        (genericPoint (Spec (CommRingCat.of k)))).hom := rfl

#print axioms equiv

end KltDP.Geometry.SpecFieldFunctionFieldIntrinsic

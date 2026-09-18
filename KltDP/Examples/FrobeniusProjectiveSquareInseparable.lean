import KltDP.Examples.FrobeniusSquareFunctionFieldComparison
import KltDP.Examples.FrobeniusSquareRationalDegree
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Degree two and pure inseparability for the original projective square map

Both extension statements use the algebra action of the original generic
stalk map of `projectivePowerMorphism 2`. The polynomial chart comparison
has already been derived for that same morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusSquareGenericMap

open KltDP.Geometry FrobeniusProjectiveMorphism FrobeniusSquareRationalMap

variable (k : Type u) [Field k]

local instance inseparableLineIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- The actual original projective generic extension has degree two. -/
theorem projectiveSquare_finrank :
    letI : Algebra (projectiveSpace k 1).functionField (projectiveSpace k 1).functionField :=
      (functionFieldMap (projectivePowerMorphism (k := k) 2)).hom.toAlgebra
    letI : Module (projectiveSpace k 1).functionField (projectiveSpace k 1).functionField :=
      Algebra.toModule
    Module.finrank (projectiveSpace k 1).functionField (projectiveSpace k 1).functionField = 2 := by
  letI : Algebra (projectiveSpace k 1).functionField (projectiveSpace k 1).functionField :=
    (functionFieldMap (projectivePowerMorphism (k := k) 2)).hom.toAlgebra
  letI : Module (projectiveSpace k 1).functionField (projectiveSpace k 1).functionField :=
    Algebra.toModule
  letI : Algebra (RatFunc k) (RatFunc k) := (squareHom k).toRingHom.toAlgebra
  letI : Module (RatFunc k) (RatFunc k) := Algebra.toModule
  have hc : (algebraMap (RatFunc k) (RatFunc k)).comp
        (projectiveFieldEquiv k).toRingHom =
      (projectiveFieldEquiv k).toRingHom.comp
        (algebraMap (projectiveSpace k 1).functionField (projectiveSpace k 1).functionField) := by
    apply RingHom.ext
    intro z
    exact (projectiveFieldMap_square k z).symm
  have hr := Algebra.rank_eq_of_equiv_equiv
    (projectiveFieldEquiv k) (projectiveFieldEquiv k) hc
  exact (congrArg Cardinal.toNat hr).trans (squareHom_finrank k)

variable [CharP k 2]

/-- Every square belongs to the image of the literal projective function-field map. -/
theorem projectiveSquare_square_mem_range (z : (projectiveSpace k 1).functionField) :
    ∃ a : (projectiveSpace k 1).functionField,
      functionFieldMap (projectivePowerMorphism (k := k) 2) a = z ^ 2 := by
  obtain ⟨a, ha⟩ := squareHom_square_mem_range k (projectiveFieldEquiv k z)
  refine ⟨(projectiveFieldEquiv k).symm a, ?_⟩
  apply (projectiveFieldEquiv k).injective
  rw [projectiveFieldMap_square, RingEquiv.apply_symm_apply, map_pow, ha]

/-- Pure inseparability for the original projective generic stalk map. -/
theorem projectiveSquare_isPurelyInseparable :
    letI : Algebra (projectiveSpace k 1).functionField (projectiveSpace k 1).functionField :=
      (functionFieldMap (projectivePowerMorphism (k := k) 2)).hom.toAlgebra
    IsPurelyInseparable (projectiveSpace k 1).functionField (projectiveSpace k 1).functionField := by
  letI : Algebra (projectiveSpace k 1).functionField (projectiveSpace k 1).functionField :=
    (functionFieldMap (projectivePowerMorphism (k := k) 2)).hom.toAlgebra
  letI : CharP (RatFunc k) 2 := charP_of_injective_algebraMap' k (RatFunc k) 2
  letI : CharP (projectiveSpace k 1).functionField 2 :=
    charP_of_injective_ringHom
      (R := RatFunc k) (A := (projectiveSpace k 1).functionField)
      (f := (projectiveFieldEquiv k).symm.toRingHom)
      (projectiveFieldEquiv k).symm.injective 2
  apply (isPurelyInseparable_iff_pow_mem (projectiveSpace k 1).functionField 2).2
  intro z
  obtain ⟨a, ha⟩ := projectiveSquare_square_mem_range k z
  exact ⟨1, a, by simpa only [pow_one] using ha⟩

end KltDP.Examples.FrobeniusSquareGenericMap

import KltDP.Geometry.EffectiveWeilCommonPart
import KltDP.Geometry.EffectiveWeilPrimeSupport

/-! Two original effective members with no common prime component yield
a nef original divisor class. Applying this to their coefficientwise
common part constructs the nef residual class without assuming nefness. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry
universe u
namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- For each prime, one of the two effective members omits it; linear
equivalence transfers that actual nonnegative degree to the original class. -/
theorem isNef_of_effective_pair_no_common_prime (D E : X.WeilDivisor)
    (hD : EffectiveDivisor D) (hE : EffectiveDivisor E)
    (hDE : X.LinearlyEquivalent D E) (hdisj : Disjoint D.support E.support) :
    Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme ((X.regularCartierWeilEquiv hX).symm D)) := by
  apply (X.isNef_iff_pairing hX _).mpr
  intro C
  by_cases hC : C ∈ D.support
  · have hCE : C ∉ E.support := fun h => Finset.disjoint_left.mp hdisj hC h
    rw [NefIntersectionSectionVanishing.intersection_eq_of_linearlyEquivalent
      X hX (X.primeCurveCartier hX C) hDE]
    exact EffectiveWeilPrimeSupport.intersection_nonneg_of_not_mem_support X hX E hE C hCE
  · exact EffectiveWeilPrimeSupport.intersection_nonneg_of_not_mem_support X hX D hD C hC

/-- The actual left residual after subtracting the actual common part is nef. -/
theorem commonWeilPart_residual_isNef (D E : X.WeilDivisor)
    (hDE : X.LinearlyEquivalent D E) :
    Positivity.IsNef X.structureMorphism (cartierDivisorInvertibleSheaf X.toScheme
      ((X.regularCartierWeilEquiv hX).symm (D - (D ⊓ E)))) :=
  X.isNef_of_effective_pair_no_common_prime hX (D - (D ⊓ E)) (E - (D ⊓ E))
    (X.commonWeilPart_left_effective D E) (X.commonWeilPart_right_effective D E)
    (X.linearlyEquivalent_sub_common hDE (D ⊓ E))
    (X.commonWeilPart_residual_supports_disjoint D E)

/-- The same original residual has nonnegative self-intersection. -/
theorem commonWeilPart_residual_square_nonneg (D E : X.WeilDivisor)
    (hDE : X.LinearlyEquivalent D E) :
    0 ≤ X.intersectionPairing hX
      ((X.regularCartierWeilEquiv hX).symm (D - (D ⊓ E)))
      ((X.regularCartierWeilEquiv hX).symm (D - (D ⊓ E))) :=
  NefIntersectionSectionVanishing.intersection_nonneg X hX _
    (X.commonWeilPart_residual_isNef hX D E hDE) (D - (D ⊓ E))
    (X.commonWeilPart_left_effective D E)

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.commonWeilPart_residual_isNef
#print axioms KltDP.Geometry.NormalProjectiveSurface.commonWeilPart_residual_square_nonneg

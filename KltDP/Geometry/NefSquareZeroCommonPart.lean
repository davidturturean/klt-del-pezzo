import KltDP.Geometry.MovingPairNef

/-! The actual common and moving divisors of two effective original
members are both null against the original nef square-zero divisor. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry
universe u
namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- Both actual effective pieces have nonnegative F-degree and their sum
has degree F-squared, so both degrees vanish. -/
theorem commonWeilPart_and_residual_null (F : CartierDivisor X.toScheme)
    (hF : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme F))
    (hFF : X.intersectionPairing hX F F = 0)
    (D E : X.WeilDivisor) (hD : EffectiveDivisor D) (hE : EffectiveDivisor E)
    (hDF : X.LinearlyEquivalent D (X.cartierToWeilHom F)) :
    X.intersectionPairing hX ((X.regularCartierWeilEquiv hX).symm (D ⊓ E)) F = 0 ∧
      X.intersectionPairing hX ((X.regularCartierWeilEquiv hX).symm (D - (D ⊓ E))) F = 0 := by
  let e := X.regularCartierWeilEquiv hX
  have hZ := NefIntersectionSectionVanishing.intersection_nonneg X hX F hF (D ⊓ E)
    (X.commonWeilPart_effective D E hD hE)
  have hM := NefIntersectionSectionVanishing.intersection_nonneg X hX F hF (D - (D ⊓ E))
    (X.commonWeilPart_left_effective D E)
  have hDzero : X.intersectionPairing hX (e.symm D) F = 0 := by
    rw [NefIntersectionSectionVanishing.intersection_eq_of_linearlyEquivalent
      X hX F hDF]
    have hrep : e.symm (X.cartierToWeilHom F) = F := e.symm_apply_apply F
    rw [hrep]
    exact hFF
  have hsum : e.symm (D ⊓ E) + e.symm (D - (D ⊓ E)) = e.symm D := by
    rw [← map_add]
    congr 1
    abel
  have hp : X.intersectionPairing hX (e.symm (D ⊓ E) + e.symm (D - (D ⊓ E))) F =
      X.intersectionPairing hX (e.symm D) F :=
    congrArg (fun A : CartierDivisor X.toScheme => X.intersectionPairing hX A F) hsum
  rw [X.intersectionPairing_add_left hX, hDzero] at hp
  change 0 ≤ X.intersectionPairing hX (e.symm (D ⊓ E)) F at hZ
  change 0 ≤ X.intersectionPairing hX (e.symm (D - (D ⊓ E))) F at hM
  change X.intersectionPairing hX (e.symm (D ⊓ E)) F = 0 ∧
    X.intersectionPairing hX (e.symm (D - (D ⊓ E))) F = 0
  constructor <;> omega

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.commonWeilPart_and_residual_null
#print axioms KltDP.Geometry.NormalProjectiveSurface.commonWeilPart_and_residual_null

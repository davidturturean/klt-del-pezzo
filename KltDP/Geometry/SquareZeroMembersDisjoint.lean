import KltDP.Geometry.SquareZeroMembersCommonPart
import KltDP.Geometry.EffectiveWeilIntersectionZero

/-! Any two distinct effective original members of the square-zero class
have disjoint actual closed supports. This is the geometric no-common-zero
step for the pencil, retaining the original finite Weil members. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
  (K : CartierDivisor X.toScheme)
  (eK : cartierDivisorModule X.toScheme K ≅
    relativeDifferentialExterior X.structureMorphism 2)

local instance membersDisjointSourceIntegral : IsIntegral X.toScheme := X.integral

include eK in
/-- The common component and isolated intersection points are both
excluded by the original geometry, rather than supplied as assumptions. -/
theorem effectiveMembers_disjoint_of_nef_squareZero (F : CartierDivisor X.toScheme)
    (hF : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme F))
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2)
    (D E : X.WeilDivisor) (hD : EffectiveDivisor D) (hE : EffectiveDivisor E)
    (hDF : X.LinearlyEquivalent D (X.cartierToWeilHom F))
    (hEF : X.LinearlyEquivalent E (X.cartierToWeilHom F)) (hne : D ≠ E) :
    Disjoint (divisorSupport D) (divisorSupport E) := by
  have hcommon := X.commonWeilPart_eq_zero_of_nef_squareZero hX K eK F hF hFF hKF
    D E hD hE hDF hEF hne
  have hcomponents : Disjoint D.support E.support := by
    simpa only [hcommon, sub_zero] using X.commonWeilPart_residual_supports_disjoint D E
  apply X.effectivePair_disjoint_divisorSupport hX D E hD hE hcomponents
  let e := X.regularCartierWeilEquiv hX
  have hrep : e.symm (X.cartierToWeilHom F) = F := e.symm_apply_apply F
  rw [NefIntersectionSectionVanishing.intersection_eq_of_linearlyEquivalent X hX _ hDF, hrep,
    X.intersectionPairing_symm hX F,
    NefIntersectionSectionVanishing.intersection_eq_of_linearlyEquivalent X hX F hEF,
    hrep, hFF]

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.effectiveMembers_disjoint_of_nef_squareZero
#print axioms KltDP.Geometry.NormalProjectiveSurface.effectiveMembers_disjoint_of_nef_squareZero

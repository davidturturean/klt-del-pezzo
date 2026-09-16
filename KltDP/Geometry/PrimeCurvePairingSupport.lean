import KltDP.Geometry.IntersectionPairingSymmetry
import KltDP.Geometry.PrimeCurveIntersectionAdditive
import KltDP.Geometry.PrimeCurveIntersectionZero

/-!
# Distinct-prime nonnegativity and disjointness for the actual intersection pairing

The range of the actual intersection scheme is `C ∩ Supp D`. Its emptiness
criterion therefore gives zero intersection exactly when these sets are disjoint.
For two distinct prime curves on a regular surface over an algebraically closed
field, the accepted prime Cartier divisor has precisely the other curve as its
support, and the accepted off-support theorem supplies the required restriction.
This yields nonnegativity and the zero criterion for the existing symmetric
Cartier and Picard pairings. No regularity or DVR condition on either curve is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PrimeCurvePairingSupport

open KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k}

section Effective

variable (C : X.PrimeCurve) (D : CartierDivisor X.toScheme)
  (hD : HasRegularCartierEquations X.toScheme D) (hC : C.NotInSupport D hD)

/-- The actual intersection scheme is empty exactly when the curve and divisor
support are disjoint as subsets of the surface. -/
theorem intersectionScheme_isEmpty_iff_disjoint_support :
    IsEmpty (C.intersectionScheme D hD hC) ↔
      Disjoint (C : Set X.toScheme)
        ((effectiveCartierIdealDataOfRegularEquations X.toScheme D hD).support :
          Set X.toScheme) := by
  constructor
  · intro h
    letI := h
    apply Set.disjoint_left.mpr
    intro x hxC hxD
    have hx : x ∈ Set.range (C.intersectionToSurface D hD hC).base := by
      rw [C.range_intersectionToSurface D hD hC]
      exact ⟨hxC, hxD⟩
    obtain ⟨z, _⟩ := hx
    exact isEmptyElim z
  · intro h
    refine ⟨fun z => ?_⟩
    have hz : (C.intersectionToSurface D hD hC).base z ∈
        (C : Set X.toScheme) ∩
          ((effectiveCartierIdealDataOfRegularEquations X.toScheme D hD).support :
            Set X.toScheme) := by
      rw [← C.range_intersectionToSurface D hD hC]
      exact Set.mem_range_self z
    exact Set.disjoint_left.mp h hz.1 hz.2

/-- The natural-valued intersection degree vanishes exactly when the actual
curve and effective divisor support are disjoint. -/
theorem intersectionDegree_eq_zero_iff_disjoint_support :
    C.intersectionDegree D hD hC = 0 ↔
      Disjoint (C : Set X.toScheme)
        ((effectiveCartierIdealDataOfRegularEquations X.toScheme D hD).support :
          Set X.toScheme) := by
  rw [C.intersectionDegree_eq_zero_iff D hD hC,
    intersectionScheme_isEmpty_iff_disjoint_support C D hD hC]

include hC in
/-- Effective Cartier intersection off the support is nonnegative. -/
theorem intersectionNumber_nonneg_of_notInSupport :
    0 ≤ C.intersectionNumber D := by
  rw [C.intersectionNumber_eq_intersectionDegree D hD hC]
  exact C.intersectionDegree_nonneg D hD hC

include hC in
/-- The integer-valued intersection number vanishes exactly when the actual
curve and effective divisor support are disjoint. -/
theorem intersectionNumber_eq_zero_iff_disjoint_support :
    C.intersectionNumber D = 0 ↔
      Disjoint (C : Set X.toScheme)
        ((effectiveCartierIdealDataOfRegularEquations X.toScheme D hD).support :
          Set X.toScheme) := by
  rw [C.intersectionNumber_eq_intersectionDegree D hD hC, Int.natCast_eq_zero,
    intersectionDegree_eq_zero_iff_disjoint_support C D hD hC]

end Effective

section PrimePairing

variable [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x) (C E : X.PrimeCurve)

/-- The symmetric pairing of the two prime Cartier divisors is restriction
degree along the first curve. This identity also holds on the diagonal. -/
theorem intersectionPairing_primeCurves_eq_intersectionNumber :
    intersectionPairing X hregular (X.primeCurveCartier hregular C)
        (X.primeCurveCartier hregular E) =
      C.intersectionNumber (X.primeCurveCartier hregular E) := by
  rw [X.intersectionPairing_symm hregular, X.intersectionPairing_primeCurve hregular]

/-- The actual symmetric Cartier pairing of distinct prime curves is nonnegative. -/
theorem intersectionPairing_primeCurves_nonneg (hCE : C ≠ E) :
    0 ≤ intersectionPairing X hregular (X.primeCurveCartier hregular C)
      (X.primeCurveCartier hregular E) := by
  rw [intersectionPairing_primeCurves_eq_intersectionNumber X hregular C E]
  exact intersectionNumber_nonneg_of_notInSupport C (X.primeCurveCartier hregular E)
    (X.primeCurveCartier_hasRegularEquations hregular E)
    (X.notInSupport_of_ne hregular hCE)

/-- Distinct prime curves have zero symmetric Cartier pairing exactly when their
actual subsets of the surface are disjoint. -/
theorem intersectionPairing_primeCurves_eq_zero_iff_disjoint (hCE : C ≠ E) :
    intersectionPairing X hregular (X.primeCurveCartier hregular C)
        (X.primeCurveCartier hregular E) = 0 ↔
      Disjoint (C : Set X.toScheme) (E : Set X.toScheme) := by
  rw [intersectionPairing_primeCurves_eq_intersectionNumber X hregular C E]
  simpa only [X.primeCurveCartier_support hregular E] using
    intersectionNumber_eq_zero_iff_disjoint_support C (X.primeCurveCartier hregular E)
      (X.primeCurveCartier_hasRegularEquations hregular E)
      (X.notInSupport_of_ne hregular hCE)

/-- The same nonnegativity theorem for the actual Picard classes of the two
prime Cartier divisors. -/
theorem picardPairing_primeCurves_nonneg (hCE : C ≠ E) :
    0 ≤ picardPairing X hregular
      (cartierPicardClass X.toScheme (X.primeCurveCartier hregular C))
      (cartierPicardClass X.toScheme (X.primeCurveCartier hregular E)) := by
  rw [X.picardPairing_class hregular]
  exact intersectionPairing_primeCurves_nonneg X hregular C E hCE

/-- The Picard pairing of distinct actual prime-curve divisor classes vanishes
exactly when the prime curves are disjoint. -/
theorem picardPairing_primeCurves_eq_zero_iff_disjoint (hCE : C ≠ E) :
    picardPairing X hregular
        (cartierPicardClass X.toScheme (X.primeCurveCartier hregular C))
        (cartierPicardClass X.toScheme (X.primeCurveCartier hregular E)) = 0 ↔
      Disjoint (C : Set X.toScheme) (E : Set X.toScheme) := by
  rw [X.picardPairing_class hregular]
  exact intersectionPairing_primeCurves_eq_zero_iff_disjoint X hregular C E hCE

end PrimePairing

end KltDP.Geometry.PrimeCurvePairingSupport

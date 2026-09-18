import KltDP.Geometry.PrimeCurvePairingSupport
import KltDP.Geometry.PrimeCurveClassPairing
import KltDP.Geometry.Positivity

/-!
# A prime curve plus a nonnegative multiple of a nef line bundle

For the original Cartier class of a prime curve B and an actual nef line
bundle H, every other prime curve has nonnegative degree against B + mH.
Consequently checking its degree on B proves nefness. If m is positive,
an off-B curve has degree zero exactly when it is disjoint from B and
has H-degree zero. These are statements about all original prime curves.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.PrimeCurveNefSum

open NormalProjectiveSurface PrimeCurvePairingSupport

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
  (B : X.PrimeCurve) (H : InvertibleSheaf X.toScheme) (m : ℕ)

/-- The original curve Cartier class plus the actual tensor-power class. -/
def curveNefSumClass : Additive X.toScheme.Pic :=
  cartierPicardHom X.toScheme (X.primeCurveCartier hregular B) +
    m • Additive.ofMul H.toPic

private theorem nef_degree_nonneg
    (hH : Positivity.IsNef X.structureMorphism H) (C : X.PrimeCurve) :
    0 ≤ X.picardRestrictionDegreeHom C (Additive.ofMul H.toPic) := by
  change 0 ≤ C.picardRestrictionDegree H.toPic
  rw [C.picardRestrictionDegree_toPic]
  exact (Positivity.isNef_iff_forall_primeCurve X H).mp hH C

/-- Restriction degree retains both original geometric summands. -/
theorem degree_eq (C : X.PrimeCurve) :
    X.picardRestrictionDegreeHom C (curveNefSumClass X hregular B H m) =
      C.intersectionNumber (X.primeCurveCartier hregular B) +
        (m : ℤ) * X.picardRestrictionDegreeHom C (Additive.ofMul H.toPic) := by
  rw [curveNefSumClass, map_add, map_nsmul,
    C.picardRestrictionDegreeHom_cartierPicardHom, nsmul_eq_mul]

private theorem curve_degree_nonneg (C : X.PrimeCurve) (hCB : C ≠ B) :
    0 ≤ C.intersectionNumber (X.primeCurveCartier hregular B) :=
  intersectionNumber_nonneg_of_notInSupport C _
    (X.primeCurveCartier_hasRegularEquations hregular B)
    (X.notInSupport_of_ne hregular hCB)

/-- Every different actual prime curve has nonnegative degree. -/
theorem degree_nonneg_of_ne
    (hH : Positivity.IsNef X.structureMorphism H)
    (C : X.PrimeCurve) (hCB : C ≠ B) :
    0 ≤ X.picardRestrictionDegreeHom C (curveNefSumClass X hregular B H m) := by
  rw [degree_eq]
  exact add_nonneg (curve_degree_nonneg X hregular B C hCB)
    (mul_nonneg (Nat.cast_nonneg m) (nef_degree_nonneg X H hH C))

/-- Only the degree on the distinguished prime curve remains to check. -/
theorem degree_nonneg
    (hH : Positivity.IsNef X.structureMorphism H)
    (hB : 0 ≤ X.picardRestrictionDegreeHom B (curveNefSumClass X hregular B H m))
    (C : X.PrimeCurve) :
    0 ≤ X.picardRestrictionDegreeHom C (curveNefSumClass X hregular B H m) := by
  by_cases hCB : C = B
  · subst C
    exact hB
  · exact degree_nonneg_of_ne X hregular B H m hH C hCB

/-- Every actual invertible sheaf of this class is nef after that one check. -/
theorem isNef_of_class (M : InvertibleSheaf X.toScheme)
    (hM : Additive.ofMul M.toPic = curveNefSumClass X hregular B H m)
    (hH : Positivity.IsNef X.structureMorphism H)
    (hB : 0 ≤ X.picardRestrictionDegreeHom B (curveNefSumClass X hregular B H m)) :
    Positivity.IsNef X.structureMorphism M := by
  apply (Positivity.isNef_iff_forall_primeCurve X M).mpr
  intro C
  have hc := degree_nonneg X hregular B H m hH hB C
  rw [← hM] at hc
  change 0 ≤ C.picardRestrictionDegree M.toPic at hc
  simpa only [C.picardRestrictionDegree_toPic] using hc

/-- Off B, a null curve is precisely a disjoint curve of zero H-degree. -/
theorem degree_eq_zero_iff_of_ne
    (hm : 0 < m) (hH : Positivity.IsNef X.structureMorphism H)
    (C : X.PrimeCurve) (hCB : C ≠ B) :
    X.picardRestrictionDegreeHom C (curveNefSumClass X hregular B H m) = 0 ↔
      Disjoint (C : Set X.toScheme) (B : Set X.toScheme) ∧
        X.picardRestrictionDegreeHom C (Additive.ofMul H.toPic) = 0 := by
  have hcurve := curve_degree_nonneg X hregular B C hCB
  have hnef := nef_degree_nonneg X H hH C
  have hmz : (0 : ℤ) < m := by exact_mod_cast hm
  have hz : C.intersectionNumber (X.primeCurveCartier hregular B) = 0 ↔
      Disjoint (C : Set X.toScheme) (B : Set X.toScheme) := by
    simpa only [intersectionPairing_primeCurves_eq_intersectionNumber] using
      intersectionPairing_primeCurves_eq_zero_iff_disjoint X hregular C B hCB
  rw [degree_eq]
  constructor
  · intro h
    have hb : C.intersectionNumber (X.primeCurveCartier hregular B) = 0 := by
      nlinarith
    have hh : X.picardRestrictionDegreeHom C (Additive.ofMul H.toPic) = 0 := by
      nlinarith
    exact ⟨hz.mp hb, hh⟩
  · rintro ⟨hb, hh⟩
    rw [hz.mpr hb, hh, mul_zero, add_zero]

end KltDP.Geometry.PrimeCurveNefSum

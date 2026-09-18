import KltDP.Geometry.SurfaceNakaiMoishezonProved
import KltDP.Geometry.NumericalIntersectionPairing

/-!
# Numerical ampleness for the original invertible sheaves

An arbitrary original invertible sheaf has an actual Cartier representative.
The complete published criterion transports along its Picard equality and
the original prime-curve degree comparisons. Numerical equivalence preserves
those degrees and the actual descended square, so it preserves ampleness.
-/

noncomputable section

open AlgebraicGeometry
open KltDP.Geometry.NormalProjectiveSurface

universe u

namespace KltDP.Geometry.SurfaceNakaiLineBundleCriterion

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

include hregular

/-- The full criterion for any original invertible sheaf, using its actual
self-intersection and restriction degree on every original prime curve. -/
theorem isAmple_iff (L : InvertibleSheaf X.toScheme) :
    AmpleSerre.IsAmple L ↔
      0 < X.selfIntersection hregular L ∧
        ∀ C : X.PrimeCurve, 0 < C.picardRestrictionDegree L.toPic := by
  let A := X.picardRepresentative L.toPic
  have hclass : cartierPicardClass X.toScheme A = L.toPic :=
    X.cartierPicardClass_picardRepresentative L.toPic
  have hself : X.selfIntersection hregular L = X.intersectionPairing hregular A A := by
    change X.picardPairing hregular L.toPic L.toPic = _
    rw [← hclass, X.picardPairing_class]
  have hcurve (C : X.PrimeCurve) :
      C.picardRestrictionDegree L.toPic =
        X.intersectionPairing hregular A (X.primeCurveCartier hregular C) := by
    rw [← hclass, ← C.intersectionNumber_eq_picardRestrictionDegree A,
      X.intersectionPairing_primeCurve]
  constructor
  · intro hL
    have hA := AmplePositivity.isAmple_of_toPic_eq hclass.symm hL
    obtain ⟨hs, hd⟩ := (SurfaceNakaiMoishezonProved.cartier_isAmple_iff X hregular A).mp hA
    exact ⟨hself.symm ▸ hs, fun C => (hcurve C).symm ▸ hd C⟩
  · rintro ⟨hs, hd⟩
    have hA := SurfaceNakaiMoishezonProved.cartier_isAmple_of_positive X hregular A
      (hself ▸ hs) (fun C => hcurve C ▸ hd C)
    exact AmplePositivity.isAmple_of_toPic_eq hclass hA

/-- Actual numerical equivalence preserves the original integral self-intersection. -/
theorem selfIntersection_eq_of_numericallyEquivalent (L M : InvertibleSheaf X.toScheme)
    (hLM : X.PicardNumericallyEquivalent L.toPic M.toPic) :
    X.selfIntersection hregular L = X.selfIntersection hregular M := by
  have hc := (X.picardNumericalClass_eq_iff L.toPic M.toPic).mpr hLM
  have hsq := congrArg (fun c => X.numericalIntersectionBilinForm hregular c c) hc
  change X.numericalIntersectionBilinForm hregular
      (X.picardNumericalMap (Additive.ofMul L.toPic))
      (X.picardNumericalMap (Additive.ofMul L.toPic)) =
    X.numericalIntersectionBilinForm hregular
      (X.picardNumericalMap (Additive.ofMul M.toPic))
      (X.picardNumericalMap (Additive.ofMul M.toPic)) at hsq
  rw [X.numericalIntersectionBilinForm_picard, X.numericalIntersectionBilinForm_picard] at hsq
  exact_mod_cast hsq

/-- Ampleness is invariant under the original all-prime-curve numerical equivalence. -/
theorem isAmple_iff_of_numericallyEquivalent (L M : InvertibleSheaf X.toScheme)
    (hLM : X.PicardNumericallyEquivalent L.toPic M.toPic) :
    AmpleSerre.IsAmple L ↔ AmpleSerre.IsAmple M := by
  rw [isAmple_iff X hregular L, isAmple_iff X hregular M,
    selfIntersection_eq_of_numericallyEquivalent X hregular L M hLM]
  exact and_congr_right fun _ => forall_congr' fun C => by rw [hLM C]

end KltDP.Geometry.SurfaceNakaiLineBundleCriterion

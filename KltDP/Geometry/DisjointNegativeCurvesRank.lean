import KltDP.Geometry.NumericalOrthogonalFamilyRank
import KltDP.Geometry.PrimeCurvePairingSupport

/-!
# Disjoint negative prime curves bound the original Picard rank

Each curve contributes the actual numerical class of its constructed prime
Cartier divisor. The existing intersection comparison identifies its square
with the original `selfIntersectionNumber`, and geometric disjointness makes
distinct-curve pairings vanish. Pairing with a supplied positive numerical
class is the already defined restriction-degree test on the original curve.

Thus no numerical intersection matrix or linear-independence premise is
supplied. The regular-surface numerical finiteness theorem enters through the
proved orthogonal-family rank bound.
-/

noncomputable section

open AlgebraicGeometry

universe u v

namespace KltDP.Geometry.DisjointNegativeCurvesRank

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- The original numerical class of the actual prime curve's Cartier divisor. -/
def curveClass (C : X.PrimeCurve) : X.NumericalClassGroup :=
  X.picardNumericalClass (cartierPicardClass X.toScheme (X.primeCurveCartier hregular C))

/-- The existing numerical pairing retains the original prime Cartier pairing. -/
theorem curveClass_pairing (C E : X.PrimeCurve) :
    X.numericalIntersectionBilinForm hregular (curveClass X hregular C) (curveClass X hregular E) =
      (X.intersectionPairing hregular (X.primeCurveCartier hregular C)
        (X.primeCurveCartier hregular E) : ℚ) := by
  change X.numericalIntersectionBilinForm hregular
    (X.picardNumericalMap (Additive.ofMul
      (cartierPicardClass X.toScheme (X.primeCurveCartier hregular C))))
    (X.picardNumericalMap (Additive.ofMul
      (cartierPicardClass X.toScheme (X.primeCurveCartier hregular E)))) = _
  rw [X.numericalIntersectionBilinForm_picard hregular]
  simp only [toMul_ofMul]
  rw [X.picardPairing_class hregular]

/-- The numerical square is the original curve self-intersection number. -/
theorem curveClass_self (C : X.PrimeCurve) :
    X.numericalIntersectionBilinForm hregular (curveClass X hregular C) (curveClass X hregular C) =
      (C.selfIntersectionNumber hregular : ℚ) := by
  rw [curveClass_pairing, X.intersectionPairing_primeCurve hregular]
  rfl

/-- Disjoint original prime curves have orthogonal numerical classes. Their
distinctness follows from the generic point of either curve. -/
theorem curveClass_pairing_eq_zero_of_disjoint (C E : X.PrimeCurve)
    (hdisjoint : Disjoint (C : Set X.toScheme) (E : Set X.toScheme)) :
    X.numericalIntersectionBilinForm hregular
      (curveClass X hregular C) (curveClass X hregular E) = 0 := by
  have hCE : C ≠ E := by
    intro hEq
    have hmem : C.genericPoint ∈ (E : Set X.toScheme) := by
      rw [← hEq]
      exact C.genericPoint_mem
    exact Set.disjoint_left.mp hdisjoint C.genericPoint_mem hmem
  rw [curveClass_pairing,
    (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
      X hregular C E hCE).mpr hdisjoint, Int.cast_zero]

/-- Orthogonality to a prime curve is exactly the existing numerical
restriction-degree test on that original curve. -/
theorem pairing_curveClass (h : X.NumericalClassGroup) (C : X.PrimeCurve) :
    X.numericalIntersectionBilinForm hregular h (curveClass X hregular C) =
      X.numericalRestrictionDegree C h :=
  X.numericalIntersectionBilinForm_primeCurve hregular h C

/-- A finite disjoint family of actual negative prime curves, together with a
positive numerical class of degree zero on each curve, bounds original Picard
rank. No numerical matrix or independence is an input. -/
theorem card_add_one_le_picardRank {ι : Type v} [Fintype ι]
    (C : ι → X.PrimeCurve)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i : Set X.toScheme) (C j : Set X.toScheme))
    (hnegative : ∀ i, (C i).selfIntersectionNumber hregular < 0)
    (h : X.NumericalClassGroup)
    (hpositive : 0 < X.numericalIntersectionBilinForm hregular h h)
    (hdegree : ∀ i, X.numericalRestrictionDegree (C i) h = 0) :
    Fintype.card ι + 1 ≤ X.picardRank := by
  apply NumericalOrthogonalFamilyRank.card_add_one_le_picardRank X hregular
    h (fun i => curveClass X hregular (C i)) hpositive
  · intro i j hij
    exact curveClass_pairing_eq_zero_of_disjoint X hregular (C i) (C j) (hdisjoint i j hij)
  · intro i
    rw [curveClass_self]
    exact_mod_cast hnegative i
  · intro i
    rw [pairing_curveClass]
    exact hdegree i

end KltDP.Geometry.DisjointNegativeCurvesRank

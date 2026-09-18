import KltDP.Geometry.DisjointNegativeCurvesRank
import KltDP.Geometry.RegularSurfaceWeilPicard
import KltDP.Geometry.CartierWeilClassMap

/-!
# Uniqueness of a negative prime curve in its numerical class

Distinct original prime curves have nonnegative intersection. If their
original numerical classes agree, that intersection is the self-intersection
of either curve. A strictly negative self-intersection therefore forces the
curves to be equal. The actual Picard, Weil linear-equivalence, and Cartier
class consequences follow through the already constructed class maps.

No negative-definite matrix, finite-dimensionality, or uniqueness premise is
used. The conclusion identifies the original prime-curve objects.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NegativePrimeCurveUniqueness

open DisjointNegativeCurvesRank

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- A negative prime curve is determined by its actual rational numerical class. -/
theorem eq_of_numericalClass_eq (C E : X.PrimeCurve)
    (hnegative : C.selfIntersectionNumber hregular < 0)
    (hclass : curveClass X hregular C = curveClass X hregular E) : C = E := by
  classical
  by_contra hCE
  have hnonneg : 0 ≤ X.numericalIntersectionBilinForm hregular
      (curveClass X hregular C) (curveClass X hregular E) := by
    rw [curveClass_pairing]
    exact_mod_cast PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg
      X hregular C E hCE
  have hneg : X.numericalIntersectionBilinForm hregular
      (curveClass X hregular C) (curveClass X hregular C) < 0 := by
    rw [curveClass_self]
    exact_mod_cast hnegative
  rw [← hclass] at hnonneg
  exact (not_lt_of_ge hnonneg) hneg

/-- The same uniqueness from the original all-prime-curve numerical tests. -/
theorem eq_of_picardNumericallyEquivalent (C E : X.PrimeCurve)
    (hnegative : C.selfIntersectionNumber hregular < 0)
    (hclass : X.PicardNumericallyEquivalent
      (cartierPicardClass X.toScheme (X.primeCurveCartier hregular C))
      (cartierPicardClass X.toScheme (X.primeCurveCartier hregular E))) : C = E :=
  eq_of_numericalClass_eq X hregular C E hnegative
    ((X.picardNumericalClass_eq_iff _ _).mpr hclass)

/-- Equality of the actual Picard classes of the prime Cartier divisors already
determines a negative prime curve. -/
theorem eq_of_picardClass_eq (C E : X.PrimeCurve)
    (hnegative : C.selfIntersectionNumber hregular < 0)
    (hclass : cartierPicardClass X.toScheme (X.primeCurveCartier hregular C) =
      cartierPicardClass X.toScheme (X.primeCurveCartier hregular E)) : C = E :=
  eq_of_numericalClass_eq X hregular C E hnegative
    (congrArg X.picardNumericalClass hclass)

/-- Original Weil linear equivalence of the prime divisors implies equality
when one curve has negative self-intersection. -/
theorem eq_of_linearlyEquivalent (C E : X.PrimeCurve)
    (hnegative : C.selfIntersectionNumber hregular < 0)
    (hlinear : X.LinearlyEquivalent (Finsupp.single C 1) (Finsupp.single E 1)) : C = E := by
  apply eq_of_picardClass_eq X hregular C E hnegative
  have hclasses := (X.regularWeilPicardClass_eq_iff hregular
    (Finsupp.single C 1) (Finsupp.single E 1)).mpr hlinear
  have hC : X.regularWeilPicardClass hregular (Finsupp.single C 1) =
      cartierPicardClass X.toScheme (X.primeCurveCartier hregular C) :=
    X.regularWeilClassPicardEquiv_representative hregular (Finsupp.single C 1)
  have hE : X.regularWeilPicardClass hregular (Finsupp.single E 1) =
      cartierPicardClass X.toScheme (X.primeCurveCartier hregular E) :=
    X.regularWeilClassPicardEquiv_representative hregular (Finsupp.single E 1)
  exact hC.symm.trans (hclasses.trans hE)

/-- Equality in the original Cartier divisor class group also determines the
negative prime curve, through the proved original Cartier-to-Weil map. -/
theorem eq_of_cartierClass_eq (C E : X.PrimeCurve)
    (hnegative : C.selfIntersectionNumber hregular < 0)
    (hclass : cartierClassMap X.toScheme (X.primeCurveCartier hregular C) =
      cartierClassMap X.toScheme (X.primeCurveCartier hregular E)) : C = E := by
  apply eq_of_linearlyEquivalent X hregular C E hnegative
  have hlinear := X.cartierToWeilHom_linearlyEquivalent_of_cartierClassMap_eq hclass
  rw [X.cartierToWeilHom_primeCurveCartier hregular,
    X.cartierToWeilHom_primeCurveCartier hregular] at hlinear
  exact hlinear

/-- There is exactly one actual prime curve in the numerical class of a
negative prime curve. -/
theorem existsUnique_in_numericalClass (C : X.PrimeCurve)
    (hnegative : C.selfIntersectionNumber hregular < 0) :
    ∃! E : X.PrimeCurve, curveClass X hregular E = curveClass X hregular C :=
  ⟨C, rfl, fun E hE => (eq_of_numericalClass_eq X hregular C E hnegative hE.symm).symm⟩

end KltDP.Geometry.NegativePrimeCurveUniqueness

import KltDP.Literature.NumericalIntersectionLiterals

/-!
# The Euler pairing is bilinear, and the two pairings agree (F03/F05)

Consumers of `KltDP.Literature.Stacks.NumericalIntersectionSurfaceLiteral` (Stacks Section 33.45,
tags 0BEP/0BEQ/0BER at `d = 2`, `Z = X`; the texts are in
`KltDP/Literature/NumericalIntersectionLiterals.lean` and `laneE/F10_LITERALS.md`).

That structure's **former** specialisation debt — the coefficient of `n₁n₂` of 0BEP versus the second
difference of `χ`, through the total-degree bound of 0BEM — is **discharged**, by
`mixedCoeff_eq_secondDifference` and `picardEulerPairing_eq_symbol`; and the structure itself is now a
*theorem*, `numericalIntersectionSurfaceLiteral_of_polynomialLiteral`, derived from the faithful
ℚ-coefficient literal `NumericalIntersectionPolynomialLiteral`. It is **not** an admission candidate
in its own right (its symbol clause is eliminable against the total accepted Euler pairing), so the
hypothesis carried by every theorem below is dischargeable rather than assumed.

* `cartierEulerPairingAdditive_of_literal`: the last named hypothesis of the E6/E7 pairing
  development follows from 0BER. It does **not** follow from the duality tags 0FVV/0FVZ.
* `cartierEulerPairing_eq_intersectionPairing_of_literal`: the accepted Euler pairing and the
  bilinear pairing agree on **every** pair of Cartier divisors (previously only when one argument was
  effective with regular equations or a prime-curve divisor).
* `picardEulerPairing_eq_picardPairing`, `selfIntersection_eq_picardEulerPairing`: the same on `Pic`,
  so `L²` in either sense is the same integer.
* `nullLocus_form_eq`: consequently the E5 null-locus description (stated with `picardEulerPairing`)
  and the E7 one (stated with `selfIntersection`) have literally the same right-hand side.

Nothing is admitted: the literal is a hypothesis of every statement below.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open KltDP.Geometry KltDP.Literature.Stacks

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- **The last named hypothesis of the pairing development, discharged from Stacks 0BER.** -/
theorem cartierEulerPairingAdditive_of_literal
    (hL : NumericalIntersectionSurfaceLiteral k) : CartierEulerPairingAdditive X := by
  obtain ⟨sym, -, hright, hval⟩ := hL.exists_symbol X
  intro D E E'
  rw [X.cartierEulerPairing_eq_picardEulerPairing D (E + E'),
    X.cartierEulerPairing_eq_picardEulerPairing D E,
    X.cartierEulerPairing_eq_picardEulerPairing D E',
    ← hval, ← hval, ← hval, cartierPicardClass_add, hright]

/-- **The accepted Euler pairing and the bilinear pairing agree on every pair.** -/
theorem cartierEulerPairing_eq_intersectionPairing_of_literal
    (hL : NumericalIntersectionSurfaceLiteral k) (D₁ D₂ : CartierDivisor X.toScheme) :
    X.cartierEulerPairing D₁ D₂ = intersectionPairing X hregular D₁ D₂ :=
  X.cartierEulerPairing_eq_intersectionPairing hregular
    (X.primeCurveIntersectionSymmetric hregular)
    (X.cartierEulerPairingAdditive_of_literal hL) D₁ D₂

/-- **The same statement on `Pic`.** -/
theorem picardEulerPairing_eq_picardPairing (hL : NumericalIntersectionSurfaceLiteral k)
    (p q : X.toScheme.Pic) :
    X.picardEulerPairing p q = picardPairing X hregular p q := by
  obtain ⟨D, rfl⟩ := cartierPicardClass_surjective X.toScheme p
  obtain ⟨E, rfl⟩ := cartierPicardClass_surjective X.toScheme q
  rw [← X.cartierEulerPairing_eq_picardEulerPairing D E,
    X.cartierEulerPairing_eq_intersectionPairing_of_literal hregular hL D E,
    ← X.picardPairing_class hregular D E]

/-- **`L²` in either sense is the same integer.** -/
theorem selfIntersection_eq_picardEulerPairing (hL : NumericalIntersectionSurfaceLiteral k)
    (L : InvertibleSheaf X.toScheme) :
    selfIntersection X hregular L = X.picardEulerPairing L.toPic L.toPic :=
  (X.picardEulerPairing_eq_picardPairing hregular hL L.toPic L.toPic).symm

/-- **The E5 and E7 null-locus descriptions coincide.** -/
theorem nullLocus_form_eq (hL : NumericalIntersectionSurfaceLiteral k)
    (L : InvertibleSheaf X.toScheme) :
    closure ((⋃ C ∈ {C : X.PrimeCurve | C.restrictionDegree L = 0}, (C : Set X.toScheme)) ∪
        ⋃ (_ : selfIntersection X hregular L = 0), (Set.univ : Set X.toScheme)) =
      closure ((⋃ C ∈ {C : X.PrimeCurve | C.restrictionDegree L = 0}, (C : Set X.toScheme)) ∪
        ⋃ (_ : X.picardEulerPairing L.toPic L.toPic = 0), (Set.univ : Set X.toScheme)) := by
  rw [X.selfIntersection_eq_picardEulerPairing hregular hL L]

end KltDP.Geometry.NormalProjectiveSurface

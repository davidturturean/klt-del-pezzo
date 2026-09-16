import KltDP.Geometry.EulerPairingBilinear
import KltDP.Geometry.EulerPairingPolynomial

/-!
# The bilinearity results over the faithful literal: composing the discharge

Review B25 recorded a real gap of the "could discharge but nothing composes" class. The accepted
`EulerPairingBilinear` proves five results, and its docstring says the hypothesis
`NumericalIntersectionSurfaceLiteral` "is dischargeable rather than assumed" — but all five
statements still **bind** that literal, and the derivation that discharges it
(`numericalIntersectionSurfaceLiteral_of_polynomialLiteral`, E9) lives in a different accepted
module and is never composed with them. The acceptance record was sharpened to "holding only in
principle". This module closes the composition.

Each of the five accepted results is restated over the **faithful ℚ-coefficient literal**
`NumericalIntersectionPolynomialLiteral` (Stacks 0BEM/0BEP/0BEQ/0BER in the source's own shape),
which is the only admission candidate of the two:

* `cartierEulerPairingAdditive_of_polynomialLiteral`
* `cartierEulerPairing_eq_intersectionPairing_of_polynomialLiteral`
* `picardEulerPairing_eq_picardPairing_of_polynomialLiteral`
* `selfIntersection_eq_picardEulerPairing_of_polynomialLiteral`
* `nullLocus_form_eq_of_polynomialLiteral`

Nothing new is proved: each is the accepted statement precomposed with the accepted discharge, so the
surface literal no longer appears in any hypothesis. **The conditionality is not removed** — it is
moved onto the faithful literal, which remains undischarged and unadmitted. What changes is that a
consumer now needs only the literal the project would actually admit, instead of the specialised one
the acceptance record flagged.

Both imports are accepted, so the import closure is accepted-only. Neither accepted module is edited:
per the frozen-module rule, the composition lives here.

Nothing is admitted and no new literal is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open KltDP.Geometry KltDP.Literature.Stacks

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- **Additivity of the accepted Euler pairing, over the faithful literal.** -/
theorem cartierEulerPairingAdditive_of_polynomialLiteral
    (hL : NumericalIntersectionPolynomialLiteral k) : CartierEulerPairingAdditive X :=
  X.cartierEulerPairingAdditive_of_literal
    (numericalIntersectionSurfaceLiteral_of_polynomialLiteral hL)

/-- **The accepted Euler pairing is the bilinear pairing, over the faithful literal.** -/
theorem cartierEulerPairing_eq_intersectionPairing_of_polynomialLiteral
    (hL : NumericalIntersectionPolynomialLiteral k) (D₁ D₂ : CartierDivisor X.toScheme) :
    X.cartierEulerPairing D₁ D₂ = intersectionPairing X hregular D₁ D₂ :=
  X.cartierEulerPairing_eq_intersectionPairing_of_literal hregular
    (numericalIntersectionSurfaceLiteral_of_polynomialLiteral hL) D₁ D₂

/-- **The same on `Pic`, over the faithful literal.** -/
theorem picardEulerPairing_eq_picardPairing_of_polynomialLiteral
    (hL : NumericalIntersectionPolynomialLiteral k) (p q : X.toScheme.Pic) :
    X.picardEulerPairing p q = picardPairing X hregular p q :=
  X.picardEulerPairing_eq_picardPairing hregular
    (numericalIntersectionSurfaceLiteral_of_polynomialLiteral hL) p q

/-- **`L²` in either sense, over the faithful literal.** -/
theorem selfIntersection_eq_picardEulerPairing_of_polynomialLiteral
    (hL : NumericalIntersectionPolynomialLiteral k) (L : InvertibleSheaf X.toScheme) :
    selfIntersection X hregular L = X.picardEulerPairing L.toPic L.toPic :=
  X.selfIntersection_eq_picardEulerPairing hregular
    (numericalIntersectionSurfaceLiteral_of_polynomialLiteral hL) L

/-- **The two null-locus descriptions coincide, over the faithful literal.** -/
theorem nullLocus_form_eq_of_polynomialLiteral
    (hL : NumericalIntersectionPolynomialLiteral k) (L : InvertibleSheaf X.toScheme) :
    closure ((⋃ C ∈ {C : X.PrimeCurve | C.restrictionDegree L = 0}, (C : Set X.toScheme)) ∪
        ⋃ (_ : selfIntersection X hregular L = 0), (Set.univ : Set X.toScheme)) =
      closure ((⋃ C ∈ {C : X.PrimeCurve | C.restrictionDegree L = 0}, (C : Set X.toScheme)) ∪
        ⋃ (_ : X.picardEulerPairing L.toPic L.toPic = 0), (Set.univ : Set X.toScheme)) :=
  X.nullLocus_form_eq hregular
    (numericalIntersectionSurfaceLiteral_of_polynomialLiteral hL) L

end KltDP.Geometry.NormalProjectiveSurface

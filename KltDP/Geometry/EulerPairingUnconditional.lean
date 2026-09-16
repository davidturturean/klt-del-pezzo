import KltDP.Geometry.CartierEulerPairingCocycle
import KltDP.Geometry.IntersectionPairingSymmetry

/-!
# The Euler and intersection pairings agree on a regular surface

The cocycle/generator proof supplies the actual Euler pairing's additivity, while the accepted
prime-curve comparison supplies symmetry. The accepted comparison theorem then identifies the
actual four-term Euler pairing with the intersection pairing for every pair of Cartier divisors.
Surjectivity of the actual Cartier-to-Picard map gives the corresponding Picard and
self-intersection statements. No numerical-intersection literal remains as a hypothesis.

The last statement identifies two displayed set expressions. It does not prove a bigness
criterion or identify either expression with the actual exceptional/null locus.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open KltDP.Geometry

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

include hregular

/-- The actual Euler and intersection pairings agree on arbitrary Cartier divisors. -/
theorem cartierEulerPairing_eq_intersectionPairing_of_regular
    (D E : CartierDivisor X.toScheme) :
    X.cartierEulerPairing D E = intersectionPairing X hregular D E :=
  X.cartierEulerPairing_eq_intersectionPairing hregular
    (X.primeCurveIntersectionSymmetric hregular)
    (X.cartierEulerPairingAdditive_of_regular hregular) D E

/-- Agreement of the pairings on the actual sheaf Picard group. -/
theorem picardEulerPairing_eq_picardPairing_of_regular (p q : X.toScheme.Pic) :
    X.picardEulerPairing p q = picardPairing X hregular p q := by
  obtain ⟨D, rfl⟩ := cartierPicardClass_surjective X.toScheme p
  obtain ⟨E, rfl⟩ := cartierPicardClass_surjective X.toScheme q
  rw [← X.cartierEulerPairing_eq_picardEulerPairing D E,
    X.cartierEulerPairing_eq_intersectionPairing_of_regular hregular D E,
    ← X.picardPairing_class hregular D E]

/-- Tensor-additivity in the first Picard argument. -/
theorem picardEulerPairing_mul_left_of_regular (p p' q : X.toScheme.Pic) :
    X.picardEulerPairing (p * p') q = X.picardEulerPairing p q + X.picardEulerPairing p' q := by
  rw [X.picardEulerPairing_eq_picardPairing_of_regular hregular,
    X.picardEulerPairing_eq_picardPairing_of_regular hregular,
    X.picardEulerPairing_eq_picardPairing_of_regular hregular,
    X.picardPairing_mul_left_of_regular hregular]

/-- Tensor-additivity in the second Picard argument. -/
theorem picardEulerPairing_mul_right_of_regular (p q q' : X.toScheme.Pic) :
    X.picardEulerPairing p (q * q') = X.picardEulerPairing p q + X.picardEulerPairing p q' := by
  rw [X.picardEulerPairing_eq_picardPairing_of_regular hregular,
    X.picardEulerPairing_eq_picardPairing_of_regular hregular,
    X.picardEulerPairing_eq_picardPairing_of_regular hregular,
    X.picardPairing_mul_right_of_regular hregular]

/-- The intersection square equals the four-term Euler expression of the same sheaf class. -/
theorem selfIntersection_eq_picardEulerPairing_of_regular
    (L : InvertibleSheaf X.toScheme) :
    selfIntersection X hregular L = X.picardEulerPairing L.toPic L.toPic :=
  (X.picardEulerPairing_eq_picardPairing_of_regular hregular L.toPic L.toPic).symm

/-- The two displayed surface null-locus forms agree, without a bigness comparison premise. -/
theorem nullLocus_form_eq_of_regular (L : InvertibleSheaf X.toScheme) :
    closure ((⋃ C ∈ {C : X.PrimeCurve | C.restrictionDegree L = 0}, (C : Set X.toScheme)) ∪
        ⋃ (_ : selfIntersection X hregular L = 0), (Set.univ : Set X.toScheme)) =
      closure ((⋃ C ∈ {C : X.PrimeCurve | C.restrictionDegree L = 0}, (C : Set X.toScheme)) ∪
        ⋃ (_ : X.picardEulerPairing L.toPic L.toPic = 0), (Set.univ : Set X.toScheme)) := by
  rw [X.selfIntersection_eq_picardEulerPairing_of_regular hregular L]

end KltDP.Geometry.NormalProjectiveSurface

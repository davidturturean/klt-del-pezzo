/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.RelativeProjectiveCoefficientMorphism

/-! # Original coefficient change commutes with homogeneous restrictions -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace KltDP.Geometry.RelativeProjectiveChart
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R S : Type u} [CommRing R] [CommRing S] (n : ℕ) (φ : R →+* S)

/-- The actual restriction from `D(a)` to `D(a*c)` commutes with the
original coefficient homomorphism, including the original denominator maps. -/
theorem coefficientMap_awayMap
    {a c x : homogeneousRing R n} {b d y : homogeneousRing S n}
    (hab : MvPolynomial.map φ a = b) (hcd : MvPolynomial.map φ c = d)
    (hxy : MvPolynomial.map φ x = y)
    {r s : ℕ} (ha : a ∈ grading R n r) (hc : c ∈ grading R n s)
    (hx : x = a * c) (hy : y = b * d) :
    (HomogeneousLocalization.awayMap (grading S n)
      (hcd ▸ (show c.IsHomogeneous s from hc).map φ) hy).comp
        (coefficientMap n φ a b hab) =
      (coefficientMap n φ x y hxy).comp
        (HomogeneousLocalization.awayMap (grading R n) hc hx) := by
  apply HomogeneousAway.ringHom_ext (grading R n) ha
  intro m p hp
  simp only [RingHom.comp_apply, coefficientMap_mk,
    HomogeneousLocalization.awayMap_mk, map_mul, map_pow, hcd]

/-- The same commuting square on the original spectra of homogeneous chart rings. -/
theorem SpecMap_coefficientMap_awayMap
    {a c x : homogeneousRing R n} {b d y : homogeneousRing S n}
    (hab : MvPolynomial.map φ a = b) (hcd : MvPolynomial.map φ c = d)
    (hxy : MvPolynomial.map φ x = y)
    {r s : ℕ} (ha : a ∈ grading R n r) (hc : c ∈ grading R n s)
    (hx : x = a * c) (hy : y = b * d) :
    Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (grading S n)
        (hcd ▸ (show c.IsHomogeneous s from hc).map φ) hy)) ≫
      Spec.map (CommRingCat.ofHom (coefficientMap n φ a b hab)) =
    Spec.map (CommRingCat.ofHom (coefficientMap n φ x y hxy)) ≫
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (grading R n) hc hx)) := by
  simpa only [CommRingCat.ofHom_comp, Spec.map_comp] using
    congrArg (fun g : HomogeneousLocalization.Away (grading R n) a →+*
        HomogeneousLocalization.Away (grading S n) y => Spec.map (CommRingCat.ofHom g))
      (coefficientMap_awayMap n φ hab hcd hxy ha hc hx hy)

end KltDP.Geometry.RelativeProjectiveChart

#print axioms KltDP.Geometry.RelativeProjectiveChart.coefficientMap_awayMap

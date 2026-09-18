/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Compatibility.HomogeneousLocalizationBaseMap
import KltDP.Geometry.RelativeProjectiveCoordinateCharts

/-!
# Original coefficient maps on projective charts and overlaps

Coefficient change acts on the actual homogeneous numerator and denominator.
The two original restrictions to each coordinate overlap commute with this map.
Thus the original chart morphisms can be glued without a supplied global Proj
map or any projective-bundle premise.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.RelativeProjectiveChart
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R S : Type u} [CommRing R] [CommRing S] (n : ℕ) (φ : R →+* S)

/-- Coefficient change on any actual homogeneous-localization chart whose
original denominator is carried to the displayed target denominator. -/
def coefficientMap (a : homogeneousRing R n) (b : homogeneousRing S n)
    (hab : MvPolynomial.map φ a = b) :
    HomogeneousLocalization.Away (grading R n) a →+*
      HomogeneousLocalization.Away (grading S n) b :=
  KltDP.HomogeneousLocalizationBaseMap.map (grading R n) (grading S n)
    (MvPolynomial.map φ)
    (by
      apply Submonoid.powers_le.mpr
      change MvPolynomial.map φ a ∈ Submonoid.powers b
      rw [hab]
      exact Submonoid.mem_powers b)
    (fun d p hp => (show p.IsHomogeneous d from hp).map φ)

/-- The original fraction is sent to the fraction of its original coefficient image. -/
theorem coefficientMap_mk {a : homogeneousRing R n} {b : homogeneousRing S n}
    (hab : MvPolynomial.map φ a = b) {d : ℕ} (ha : a ∈ grading R n d)
    (m : ℕ) (p : homogeneousRing R n) (hp : p ∈ grading R n (m • d)) :
    coefficientMap n φ a b hab (HomogeneousLocalization.Away.mk (grading R n) ha m p hp) =
      HomogeneousLocalization.Away.mk (grading S n)
        (by simpa only [hab] using (show a.IsHomogeneous d from ha).map φ)
        m (MvPolynomial.map φ p) ((show p.IsHomogeneous (m • d) from hp).map φ) := by
  apply HomogeneousLocalization.val_injective
  change Localization.mk (MvPolynomial.map φ p) ⟨MvPolynomial.map φ (a ^ m), _⟩ =
    Localization.mk (MvPolynomial.map φ p) ⟨b ^ m, _⟩
  apply congrArg (Localization.mk (MvPolynomial.map φ p))
  apply Subtype.ext
  change MvPolynomial.map φ (a ^ m) = b ^ m
  rw [map_pow, hab]

/-- Coefficient change on the literal chart at coordinate i. -/
def coefficientChartMap (i : Fin (n + 1)) :
    coordinateChartRing R n i →+* coordinateChartRing S n i :=
  coefficientMap n φ (MvPolynomial.X i) (MvPolynomial.X i) (by simp)

/-- Coefficient change on the literal two-coordinate overlap. -/
def coefficientOverlapMap (i j : Fin (n + 1)) :
    coordinateOverlapRing R n i j →+* coordinateOverlapRing S n i j :=
  coefficientMap n φ (MvPolynomial.X i * MvPolynomial.X j)
    (MvPolynomial.X i * MvPolynomial.X j) (by simp)

@[simp] theorem coefficientChartMap_constants (i : Fin (n + 1)) (r : R) :
    coefficientChartMap n φ i (coordinateChartConstants R n i r) =
      coordinateChartConstants S n i (φ r) := by
  apply HomogeneousLocalization.val_injective
  change Localization.mk (MvPolynomial.map φ (MvPolynomial.C r))
      ⟨MvPolynomial.map φ 1, _⟩ = Localization.mk (MvPolynomial.C (φ r)) 1
  simp only [MvPolynomial.map_C, map_one]
  rfl

/-- Coefficient change commutes with the actual first overlap restriction. -/
theorem coefficientChartMap_toOverlapLeft (i j : Fin (n + 1)) :
    (toOverlapLeft S n i j).comp (coefficientChartMap n φ i) =
      (coefficientOverlapMap n φ i j).comp (toOverlapLeft R n i j) := by
  apply HomogeneousAway.ringHom_ext (grading R n) (coordinate_mem R n i)
  intro m p hp
  simp only [RingHom.comp_apply, coefficientChartMap, coefficientOverlapMap,
    toOverlapLeft, coefficientMap_mk, HomogeneousLocalization.awayMap_mk,
    map_mul, map_pow, MvPolynomial.map_X]

/-- Coefficient change commutes with the actual second overlap restriction. -/
theorem coefficientChartMap_toOverlapRight (i j : Fin (n + 1)) :
    (toOverlapRight S n i j).comp (coefficientChartMap n φ j) =
      (coefficientOverlapMap n φ i j).comp (toOverlapRight R n i j) := by
  apply HomogeneousAway.ringHom_ext (grading R n) (coordinate_mem R n j)
  intro m p hp
  simp only [RingHom.comp_apply, coefficientChartMap, coefficientOverlapMap,
    toOverlapRight, coefficientMap_mk, HomogeneousLocalization.awayMap_mk,
    map_mul, map_pow, MvPolynomial.map_X]

end KltDP.Geometry.RelativeProjectiveChart

#print axioms KltDP.Geometry.RelativeProjectiveChart.coefficientMap_mk
#print axioms KltDP.Geometry.RelativeProjectiveChart.coefficientChartMap_toOverlapLeft
#print axioms KltDP.Geometry.RelativeProjectiveChart.coefficientChartMap_toOverlapRight

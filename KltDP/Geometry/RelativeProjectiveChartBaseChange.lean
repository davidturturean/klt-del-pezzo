/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.RelativeProjectiveChart
import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Base change of the original projective standard chart

The chart ring is the actual homogeneous localization at the first coordinate.
Its base-change map is characterized by the original constants and coordinate
ratios. The corresponding square of affine schemes is cartesian over any
commutative rings, in particular for an affine-base localization. No relative
projectivization or its transition squares are assumed.
-/

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u
namespace KltDP.Geometry.RelativeProjectiveChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] (n : ℕ)

@[simp] theorem coordinateRingEquiv_ratio (i : Fin n) :
    coordinateRingEquiv R n (ratio R n i) = MvPolynomial.X i :=
  dehomogenize_ratio R n i

/-- Base change on the literal degree-zero localization chart. -/
def chartMap (φ : R →+* S) : chartRing R n →+* chartRing S n :=
  (coordinateRingEquiv S n).symm.toRingHom.comp
    ((MvPolynomial.map φ).comp (coordinateRingEquiv R n).toRingHom)

@[simp] theorem chartMap_constants (φ : R →+* S) (r : R) :
    chartMap n φ (constants R n r) = constants S n (φ r) := by
  apply (coordinateRingEquiv S n).injective
  simp [chartMap]

@[simp] theorem chartMap_ratio (φ : R →+* S) (i : Fin n) :
    chartMap n φ (ratio R n i) = ratio S n i := by
  apply (coordinateRingEquiv S n).injective
  simp [chartMap]

/-- The spectrum of the polynomial coordinates is the original chart spectrum. -/
def polynomialChartSpecIso (R : Type u) [CommRing R] :
    Spec (.of (affineRing R n)) ≅ Spec (.of (chartRing R n)) :=
  Scheme.Spec.mapIso (coordinateRingEquiv R n).toCommRingCatIso.op

/-- Polynomial affine space has its original coefficient-base cartesian square. -/
theorem isPullback_polynomialSpec (φ : R →+* S) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin n) φ)))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : S →+* affineRing S n)))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* affineRing R n)))
      (Spec.map (CommRingCat.ofHom φ)) := by
  refine (AffineSpace.isPullback_map (n := Fin n)
    (Spec.map (CommRingCat.ofHom φ))).of_iso
      (AffineSpace.SpecIso (Fin n) (.of S))
      (AffineSpace.SpecIso (Fin n) (.of R))
      (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [AffineSpace.map_Spec_map, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [← cancel_epi (AffineSpace.SpecIso (Fin n) (.of S)).inv]
    simpa only [Iso.inv_hom_id_assoc] using
      (AffineSpace.SpecIso_inv_over (n := Fin n) (.of S))
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [← cancel_epi (AffineSpace.SpecIso (Fin n) (.of R)).inv]
    simpa only [Iso.inv_hom_id_assoc] using
      (AffineSpace.SpecIso_inv_over (n := Fin n) (.of R))
  · simp

/-- The actual standard projective chart commutes with arbitrary base change.
For rank two, take `n = 1`; for restriction to a distinguished affine base open,
take `φ` to be the original localization map. -/
theorem isPullback_chartSpec (φ : R →+* S) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (chartMap n φ)))
      (Spec.map (CommRingCat.ofHom (constants S n)))
      (Spec.map (CommRingCat.ofHom (constants R n)))
      (Spec.map (CommRingCat.ofHom φ)) := by
  refine (isPullback_polynomialSpec n φ).of_iso
    (polynomialChartSpecIso n S) (polynomialChartSpecIso n R)
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin n) φ)) ≫
        Spec.map (CommRingCat.ofHom (coordinateRingEquiv R n).toRingHom) =
      Spec.map (CommRingCat.ofHom (coordinateRingEquiv S n).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (chartMap n φ))
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext z
    simp [chartMap]
  · simp only [Iso.refl_hom, Category.comp_id]
    change Spec.map (CommRingCat.ofHom (MvPolynomial.C : S →+* affineRing S n)) =
      Spec.map (CommRingCat.ofHom (coordinateRingEquiv S n).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (constants S n))
    rw [← Spec.map_comp]
    congr 1
    ext s
    simp
  · simp only [Iso.refl_hom, Category.comp_id]
    change Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* affineRing R n)) =
      Spec.map (CommRingCat.ofHom (coordinateRingEquiv R n).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (constants R n))
    rw [← Spec.map_comp]
    congr 1
    ext r
    simp
  · simp

end KltDP.Geometry.RelativeProjectiveChart

#print axioms KltDP.Geometry.RelativeProjectiveChart.chartMap_constants
#print axioms KltDP.Geometry.RelativeProjectiveChart.chartMap_ratio
#print axioms KltDP.Geometry.RelativeProjectiveChart.isPullback_chartSpec

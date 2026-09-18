/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.RelativeProjectiveCoefficientMorphism
import KltDP.Geometry.RelativeProjectiveCoordinateBaseChange

/-!
# Functor laws for the original projective coefficient morphisms

Identity and composition are first proved on original homogeneous numerators
and denominators. The original chart-cover restrictions then prove the same
laws for the constructed whole-Proj morphisms. These are the same morphisms
whose original degree-zero/base triangles have already been proved.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace KltDP.Geometry.RelativeProjectiveChart
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] (n : ℕ)

/-- Identity coefficient change is identity on the original homogeneous
localization, without a homogeneity restriction on the chosen denominator. -/
@[simp] theorem coefficientMap_id (a : homogeneousRing R n) :
    coefficientMap n (RingHom.id R) a a (MvPolynomial.map_id a) =
      RingHom.id (HomogeneousLocalization.Away (grading R n) a) := by
  apply RingHom.ext
  intro z
  obtain ⟨x, rfl⟩ := HomogeneousLocalization.mk_surjective z
  apply HomogeneousLocalization.val_injective
  change Localization.mk (MvPolynomial.map (RingHom.id R) (x.num : homogeneousRing R n))
      ⟨MvPolynomial.map (RingHom.id R) (x.den : homogeneousRing R n), _⟩ =
    Localization.mk (x.num : homogeneousRing R n) ⟨(x.den : homogeneousRing R n), _⟩
  simp only [MvPolynomial.map_id]

/-- Successive coefficient changes compose on the original fractions. -/
theorem coefficientMap_comp (φ : R →+* S) (ψ : S →+* T)
    (a : homogeneousRing R n) (b : homogeneousRing S n) (c : homogeneousRing T n)
    (hab : MvPolynomial.map φ a = b) (hbc : MvPolynomial.map ψ b = c) :
    (coefficientMap n ψ b c hbc).comp (coefficientMap n φ a b hab) =
      coefficientMap n (ψ.comp φ) a c (by rw [← MvPolynomial.map_map, hab, hbc]) := by
  apply RingHom.ext
  intro z
  obtain ⟨x, rfl⟩ := HomogeneousLocalization.mk_surjective z
  apply HomogeneousLocalization.val_injective
  change Localization.mk
      (MvPolynomial.map ψ (MvPolynomial.map φ (x.num : homogeneousRing R n)))
      ⟨MvPolynomial.map ψ (MvPolynomial.map φ (x.den : homogeneousRing R n)), _⟩ =
    Localization.mk (MvPolynomial.map (ψ.comp φ) (x.num : homogeneousRing R n))
      ⟨MvPolynomial.map (ψ.comp φ) (x.den : homogeneousRing R n), _⟩
  simp only [MvPolynomial.map_map]

/-- Identity coefficient change is identity on each literal coordinate chart. -/
@[simp] theorem coefficientChartMap_id (i : Fin (n + 1)) :
    coefficientChartMap n (RingHom.id R) i = RingHom.id (coordinateChartRing R n i) :=
  coefficientMap_id n (MvPolynomial.X i)

/-- Composition law on each literal coordinate chart. -/
theorem coefficientChartMap_comp (φ : R →+* S) (ψ : S →+* T) (i : Fin (n + 1)) :
    (coefficientChartMap n ψ i).comp (coefficientChartMap n φ i) =
      coefficientChartMap n (ψ.comp φ) i :=
  coefficientMap_comp n φ ψ (MvPolynomial.X i) (MvPolynomial.X i) (MvPolynomial.X i)
    (MvPolynomial.map_X φ i) (MvPolynomial.map_X ψ i)

/-- The original first-chart map has the same identity law. -/
@[simp] theorem chartMap_id :
    chartMap n (RingHom.id R) = RingHom.id (chartRing R n) := by
  simpa only [coefficientChartMap_zero] using coefficientChartMap_id (R := R) n 0

/-- The original first-chart map has the same composition law. -/
theorem chartMap_comp (φ : R →+* S) (ψ : S →+* T) :
    (chartMap n ψ).comp (chartMap n φ) = chartMap n (ψ.comp φ) := by
  simpa only [coefficientChartMap_zero] using coefficientChartMap_comp n φ ψ 0

/-- The constructed whole-Proj morphism for identity coefficients is identity. -/
@[simp] theorem coefficientMorphism_id :
    coefficientMorphism n (RingHom.id R) = 𝟙 (freeProjectivization R n) := by
  apply (coordinateChartCover R n).hom_ext
  intro i
  change coordinateChartMorphism R n i.down ≫ coefficientMorphism n (RingHom.id R) =
    coordinateChartMorphism R n i.down ≫ 𝟙 _
  rw [coordinateChartMorphism_coefficientMorphism]
  simp only [coefficientChartMap_id, CommRingCat.ofHom_id, Spec.map_id,
    Category.id_comp, Category.comp_id]

/-- The actual whole-Proj construction is contravariantly functorial in its
original coefficient ring homomorphism. -/
@[reassoc] theorem coefficientMorphism_comp (φ : R →+* S) (ψ : S →+* T) :
    coefficientMorphism n ψ ≫ coefficientMorphism n φ =
      coefficientMorphism n (ψ.comp φ) := by
  apply (coordinateChartCover T n).hom_ext
  intro i
  change coordinateChartMorphism T n i.down ≫
      (coefficientMorphism n ψ ≫ coefficientMorphism n φ) =
    coordinateChartMorphism T n i.down ≫ coefficientMorphism n (ψ.comp φ)
  rw [← Category.assoc, coordinateChartMorphism_coefficientMorphism n ψ i.down,
    Category.assoc, coordinateChartMorphism_coefficientMorphism n φ i.down,
    coordinateChartMorphism_coefficientMorphism n (ψ.comp φ) i.down,
    ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    coefficientChartMap_comp]

end KltDP.Geometry.RelativeProjectiveChart

#print axioms KltDP.Geometry.RelativeProjectiveChart.coefficientMap_comp
#print axioms KltDP.Geometry.RelativeProjectiveChart.coefficientMorphism_id
#print axioms KltDP.Geometry.RelativeProjectiveChart.coefficientMorphism_comp

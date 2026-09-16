import KltDP.Examples.FrobeniusGraphPicardClassRulingCoordinates

/-!
# Original projective coordinate sections on both polynomial charts

This specializes the existing original-overlap section normalization to
each standard chart. The proof uses `Proj.basicOpenToSpec_app_top`, its
actual scheme isomorphism, and Gamma-Spec naturality. It identifies the
sections used for the ruling coordinates with X under the existing
polynomial chart maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassChartSections

open KltDP.Geometry ProjectiveLineComparison ProjectiveLineSections
open FrobeniusGraphPicardClassRulingCoordinates

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

private def homogeneousOpenIso (i : Fin 2) :
    (chartOpen k i).toScheme ≅ Spec (CommRingCat.of (chartRing k i)) :=
  Proj.basicOpenIsoSpec (grading k) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X k i) (by decide)

private theorem homogeneousOpenIso_inv_ι (i : Fin 2) :
    (homogeneousOpenIso (k := k) i).inv ≫ (chartOpen k i).ι = chartImmersion k i := rfl

theorem homogeneousChart_preimage_top (i : Fin 2) :
    ⊤ ≤ chartImmersion k i ⁻¹ᵁ chartOpen k i := by
  intro x _
  change (chartImmersion k i).base x ∈ chartOpen k i
  rw [← chartImmersion_opensRange]
  exact ⟨x, rfl⟩

theorem polynomialChart_preimage_top (i : Fin 2) :
    ⊤ ≤ polynomialChartMap k i ⁻¹ᵁ chartOpen k i := by
  intro x _
  change (polynomialChartMap k i).base x ∈ chartOpen k i
  rw [← polynomialChartMap_opensRange]
  exact ⟨x, rfl⟩

private theorem homogeneousChart_appLE_eq (i : Fin 2) :
    (chartImmersion k i).appLE (chartOpen k i) ⊤ (homogeneousChart_preimage_top i) =
      (chartOpen k i).topIso.inv ≫ (homogeneousOpenIso (k := k) i).inv.appTop := by
  have H := Scheme.appLE_comp_appLE (homogeneousOpenIso (k := k) i).inv
    (chartOpen k i).ι (chartOpen k i) ⊤ ⊤ (chartOpen k i).ι_preimage_self.ge le_rfl
  simp only [homogeneousOpenIso_inv_ι] at H
  simpa only [Scheme.Hom.appLE_eq_app, Scheme.Opens.ι_appLE,
    Scheme.Opens.topIso_inv, eqToHom_op] using H.symm

/-- The original homogeneous coordinate ring maps through the actual chart as Gamma-Spec. -/
theorem awayToSection_homogeneous_appLE (i : Fin 2) :
    Proj.awayToSection (grading k) (MvPolynomial.X i) ≫
      (chartImmersion k i).appLE (chartOpen k i) ⊤ (homogeneousChart_preimage_top i) =
        (Scheme.ΓSpecIso (CommRingCat.of (chartRing k i))).inv := by
  have hc : Proj.awayToSection (grading k) (MvPolynomial.X i) ≫
      (chartOpen k i).topIso.inv =
        (Scheme.ΓSpecIso (CommRingCat.of (chartRing k i))).inv ≫
          (homogeneousOpenIso (k := k) i).hom.appTop := by
    rw [homogeneousOpenIso, Proj.basicOpenIsoSpec_hom, Scheme.Hom.appTop,
      Proj.basicOpenToSpec_app_top, Iso.inv_hom_id_assoc]
    rfl
  rw [homogeneousChart_appLE_eq, ← Category.assoc, hc, Category.assoc,
    ← Scheme.comp_appTop, Iso.inv_hom_id, Scheme.id_appTop, Category.comp_id]

/-- The original polynomial chart section map is the prescribed coordinate equivalence. -/
theorem awayToSection_polynomial_appLE (i : Fin 2) :
    Proj.awayToSection (grading k) (MvPolynomial.X i) ≫
      (polynomialChartMap k i).appLE (chartOpen k i) ⊤ (polynomialChart_preimage_top i) =
        CommRingCat.ofHom (chartPolynomialEquiv k i).toRingHom ≫
          (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv := by
  have H := Scheme.appLE_comp_appLE (chartPolynomialIso k i).inv (chartImmersion k i)
    (chartOpen k i) ⊤ ⊤ (homogeneousChart_preimage_top i) le_rfl
  simp only [Scheme.Hom.appLE_eq_app] at H
  change (chartImmersion k i).appLE (chartOpen k i) ⊤ _ ≫
    (chartPolynomialIso k i).inv.appTop =
      (polynomialChartMap k i).appLE (chartOpen k i) ⊤ _ at H
  rw [← H, ← Category.assoc, awayToSection_homogeneous_appLE]
  change (Scheme.ΓSpecIso (CommRingCat.of (chartRing k i))).inv ≫
    (Spec.map (CommRingCat.ofHom (chartPolynomialEquiv k i).toRingHom)).appTop = _
  exact (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (chartPolynomialEquiv k i).toRingHom)).symm

/-- One definition of the actual coordinate section works on each original chart. -/
def lineCoordinateSection (i : Fin 2) : Γ(projectiveSpace k 1, chartOpen k i) :=
  (Proj.awayToSection (grading k) (MvPolynomial.X i))
    ((chartPolynomialEquiv k i).symm Polynomial.X)

theorem lineCoordinateSection_zero :
    lineCoordinateSection (k := k) 0 = leftCoordinateSection := by
  apply (leftSectionsEquiv k).injective
  rw [lineCoordinateSection, leftSectionsEquiv_awayToSection]
  change firstChartPolynomialEquiv k
      ((firstChartPolynomialEquiv k).symm Polynomial.X) =
    leftSectionsEquiv k ((leftSectionsEquiv k).symm Polynomial.X)
  simp only [RingEquiv.apply_symm_apply]

theorem lineCoordinateSection_one :
    lineCoordinateSection (k := k) 1 = rightCoordinateSection := by
  apply (rightSectionsEquiv k).injective
  rw [lineCoordinateSection, rightSectionsEquiv_awayToSection]
  change secondChartPolynomialEquiv k
      ((secondChartPolynomialEquiv k).symm Polynomial.X) =
    rightSectionsEquiv k ((rightSectionsEquiv k).symm Polynomial.X)
  simp only [RingEquiv.apply_symm_apply]

/-- The original section pulls back to exactly X, with no unspecified unit factor. -/
theorem polynomialChart_coordinate (i : Fin 2) :
    (polynomialChartMap k i).appLE (chartOpen k i) ⊤ (polynomialChart_preimage_top i)
      (lineCoordinateSection i) =
        (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv Polynomial.X := by
  have H := ConcreteCategory.congr_hom (awayToSection_polynomial_appLE (k := k) i)
    ((chartPolynomialEquiv k i).symm Polynomial.X)
  change (polynomialChartMap k i).appLE (chartOpen k i) ⊤ _ (lineCoordinateSection i) =
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv
      ((chartPolynomialEquiv k i) ((chartPolynomialEquiv k i).symm Polynomial.X)) at H
  simpa only [RingEquiv.apply_symm_apply] using H

end KltDP.Examples.FrobeniusGraphPicardClassChartSections

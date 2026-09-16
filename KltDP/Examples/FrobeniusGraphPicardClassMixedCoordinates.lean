import KltDP.Examples.FrobeniusGraphPicardClassMixedBasicOpens
import KltDP.Examples.FrobeniusGraphPicardClassCoordinateComparison

/-!
# Original coordinate comparison on all four product charts

This extends the existing diagonal projection-section comparison to the
four original product charts. Both polynomial coordinates are identified
with the original projection-stalk coordinates in the actual function
field. Their reciprocal identity proves the mixed equation h=v*g_ii,
where h=1-u^p*v and g_ii is the original diagonal graph equation.

The argument uses original scheme maps and actual section isomorphisms.
An equality of abstract rational lattices is not used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassMixedCoordinates

open KltDP.Geometry ProjectiveLineComparison
open FrobeniusProjectivePoints FrobeniusBlowupContact FrobeniusProductPlaneChart
open FrobeniusGraphPicardClassCharts FrobeniusGraphPicardClassPowerCharts
open FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassIntegral
open FrobeniusGraphPicardClassRational FrobeniusGraphPicardClassRulingCoordinates
open FrobeniusGraphPicardClassChartSections FrobeniusGraphPicardClassCoordinateComparison

variable {k : Type u} [Field k]

local instance productIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

def productOpen (i j : Fin 2) : (projectiveProduct k).Opens := productChart i j ''ᵁ ⊤

instance productOpen_nonempty (i j : Fin 2) : Nonempty (productOpen (k := k) i j) := by
  let z : Spec (CommRingCat.of (planeRing k)) := Nonempty.some inferInstance
  refine ⟨⟨(productChart i j).base z, ?_⟩⟩
  rw [productOpen, Scheme.Hom.image_top_eq_opensRange]
  exact ⟨z, rfl⟩

def productFunctionFieldMap (i j : Fin 2) : planeRing k →+* (projectiveProduct k).functionField :=
  ((projectiveProduct k).germToFunctionField (productOpen i j)).hom.comp
    (((productChart i j).appIso ⊤).inv.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv.hom)

def productIndex (d i j : Fin 2) : Fin 2 := if d = 0 then i else j

theorem productChart_ruling_all (d i j : Fin 2) :
    productChart (k := k) i j ≫ rulingProjection d =
      Spec.map (CommRingCat.ofHom (rulingPolynomialMap d)) ≫
        polynomialChartMap k (productIndex d i j) := by
  fin_cases d
  · simpa [rulingProjection, rulingPolynomialMap, productIndex] using productChart_fst (k := k) i j
  · simpa [rulingProjection, rulingPolynomialMap, productIndex] using productChart_snd (k := k) i j

theorem productOpen_le_rulingChart (d i j : Fin 2) :
    productOpen (k := k) i j ≤ rulingProjection d ⁻¹ᵁ chartOpen k (productIndex d i j) := by
  intro x hx
  rw [productOpen, Scheme.Hom.image_top_eq_opensRange] at hx
  change x ∈ Set.range (productChart i j).base at hx
  rw [productChart_range] at hx
  fin_cases d
  · simpa [rulingProjection, productIndex] using hx.1
  · simpa [rulingProjection, productIndex] using hx.2

/-- Equality of the original scheme maps gives equality of their section maps
without expanding a dependent rewrite at the geometric use site. -/
private theorem appLE_of_hom_eq {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (U : Y.Opens) (V : X.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

/-- The section-map square is proved for abstract schemes and maps, before
any of the original projective product definitions are substituted. -/
private theorem appLE_square_top {A B X Y : Scheme.{u}}
    (c : A ⟶ X) [IsOpenImmersion c] (r : X ⟶ Y) (f : A ⟶ B) (j : B ⟶ Y)
    (U : Y.Opens) (hr : c ''ᵁ ⊤ ≤ r ⁻¹ᵁ U) (hj : ⊤ ≤ j ⁻¹ᵁ U)
    (h : c ≫ r = f ≫ j) :
    r.appLE U (c ''ᵁ ⊤) hr ≫ (c.appIso ⊤).hom =
      j.appLE U ⊤ hj ≫ f.appTop := by
  have hc : ⊤ ≤ c ⁻¹ᵁ (c ''ᵁ ⊤) := by
    rw [Scheme.Hom.preimage_image_eq]
  have H₁ := Scheme.appLE_comp_appLE c r U (c ''ᵁ ⊤) ⊤ hr hc
  have H₂ := Scheme.appLE_comp_appLE f j U ⊤ ⊤ hj le_rfl
  have Htop : f.appLE ⊤ ⊤ le_rfl = f.appTop :=
    Scheme.Hom.appLE_eq_app f (U := ⊤)
  rw [Htop] at H₂
  rw [Scheme.Hom.appIso_hom']
  exact H₁.trans ((appLE_of_hom_eq h U ⊤ _ _).trans H₂.symm)

/-- Evaluation and cancellation of the original chart-section isomorphism
are also proved while all scheme maps and sections remain abstract. -/
private theorem appLE_section_of_square {A B X Y : Scheme.{u}}
    (c : A ⟶ X) [IsOpenImmersion c] (r : X ⟶ Y) (f : A ⟶ B) (j : B ⟶ Y)
    (U : Y.Opens) (hr : c ''ᵁ ⊤ ≤ r ⁻¹ᵁ U) (hj : ⊤ ≤ j ⁻¹ᵁ U)
    (h : c ≫ r = f ≫ j) (s : Γ(Y, U)) (t : Γ(A, ⊤))
    (ht : f.appTop (j.appLE U ⊤ hj s) = t) :
    r.appLE U (c ''ᵁ ⊤) hr s = (c.appIso ⊤).inv t := by
  apply ((c.appIso ⊤).commRingCatIsoToRingEquiv).injective
  change (c.appIso ⊤).hom (r.appLE U (c ''ᵁ ⊤) hr s) =
    (c.appIso ⊤).hom ((c.appIso ⊤).inv t)
  rw [Iso.inv_hom_id_apply]
  exact (ConcreteCategory.congr_hom (appLE_square_top c r f j U hr hj h) s).trans ht

/-- The polynomial-coordinate computation is isolated from the product-chart
section comparison and uses the original Spec naturality map. -/
private theorem rulingPolynomial_coordinate_section (d i : Fin 2) :
    (Spec.map (CommRingCat.ofHom (rulingPolynomialMap (k := k) d))).appTop
        ((polynomialChartMap k i).appLE (chartOpen k i) ⊤
          (polynomialChart_preimage_top i) (lineCoordinateSection i)) =
      (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv (rulingPlaneCoordinate d) := by
  rw [polynomialChart_coordinate]
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (rulingPolynomialMap (k := k) d)))
    (Polynomial.X : Polynomial k)).symm

/-- Both original projection sections are the actual specified polynomial coordinates. -/
theorem projection_coordinate_section_all (d i j : Fin 2) :
    (rulingProjection d).appLE (chartOpen k (productIndex d i j)) (productOpen i j)
        (productOpen_le_rulingChart d i j) (lineCoordinateSection (productIndex d i j)) =
      ((productChart i j).appIso ⊤).inv
        ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv (rulingPlaneCoordinate d)) :=
  appLE_section_of_square (productChart (k := k) i j) (rulingProjection d)
    (Spec.map (CommRingCat.ofHom (rulingPolynomialMap d)))
    (polynomialChartMap k (productIndex d i j)) (chartOpen k (productIndex d i j))
    (productOpen_le_rulingChart d i j) (polynomialChart_preimage_top (productIndex d i j))
    (productChart_ruling_all d i j) (lineCoordinateSection (productIndex d i j))
    ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv (rulingPlaneCoordinate d))
    (rulingPolynomial_coordinate_section d (productIndex d i j))

theorem rulingCoordinate_eq_productChart (d i j : Fin 2) :
    rulingCoordinate (k := k) d (productIndex d i j) =
      productFunctionFieldMap i j (rulingPlaneCoordinate d) := by
  have h : rulingCoordinate d (productIndex d i j) =
      (projectiveProduct k).germToFunctionField (productOpen i j)
        ((rulingProjection d).appLE (chartOpen k (productIndex d i j)) (productOpen i j)
          (productOpen_le_rulingChart d i j) (lineCoordinateSection (productIndex d i j))) := by
    simp only [rulingCoordinate, Scheme.Hom.appLE, ConcreteCategory.comp_apply,
      Scheme.germToFunctionField, TopCat.Presheaf.germ_res_apply, Scheme.stalkMap_germ_apply]
  rw [h, projection_coordinate_section_all]
  rfl

theorem productFunctionFieldMap_u (i j : Fin 2) :
    productFunctionFieldMap (k := k) i j uCoord = rulingCoordinate 0 i := by
  simpa [rulingPlaneCoordinate, rulingPolynomialMap, productIndex] using
    (rulingCoordinate_eq_productChart (k := k) 0 i j).symm

theorem productFunctionFieldMap_v (i j : Fin 2) :
    productFunctionFieldMap (k := k) i j vCoord = rulingCoordinate 1 j := by
  simpa [rulingPlaneCoordinate, rulingPolynomialMap, productIndex] using
    (rulingCoordinate_eq_productChart (k := k) 1 i j).symm

theorem productFunctionFieldMap_diagonal (i : Fin 2) :
    productFunctionFieldMap (k := k) i i = chartFunctionFieldMap i := rfl

private theorem rulingCoordinate_other_mul (d i : Fin 2) :
    rulingCoordinate (k := k) d (otherIndex i) * rulingCoordinate d i = 1 := by
  fin_cases i
  · simpa only [otherIndex, Equiv.swap_apply_left, rulingCoordinate_zero, rulingCoordinate_one,
      mul_comm] using rulingCoordinates_mul (k := k) d
  · simpa only [otherIndex, Equiv.swap_apply_right, rulingCoordinate_zero, rulingCoordinate_one]
      using rulingCoordinates_mul (k := k) d

/-- The actual rational mixed equation is v times the original diagonal graph equation. -/
theorem mixed_equation_factor (p : ℕ) (i : Fin 2) :
    productFunctionFieldMap (k := k) i (otherIndex i) (1 - uCoord ^ p * vCoord) =
      productFunctionFieldMap i (otherIndex i) vCoord *
        chartFunctionFieldMap i (vCoord - uCoord ^ p) := by
  rw [← productFunctionFieldMap_diagonal]
  simp only [map_sub, map_one, map_mul, map_pow,
    productFunctionFieldMap_u, productFunctionFieldMap_v]
  rw [mul_sub, rulingCoordinate_other_mul, mul_comm (rulingCoordinate 1 (otherIndex i))]

end KltDP.Examples.FrobeniusGraphPicardClassMixedCoordinates

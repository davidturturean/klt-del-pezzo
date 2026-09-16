import KltDP.Examples.FrobeniusGraphPicardClassChartSections

/-!
# Identification of ruling germs with the original polynomial-plane coordinates

The comparison uses the actual product projections, polynomial charts,
section maps and stalk maps. Both representations therefore give the
same functions in the original product's function field. In particular,
the second diagonal chart has coordinates x⁻¹ and y⁻¹, where x and y are
the functions previously used in the original graph equation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassCoordinateComparison

open KltDP.Geometry ProjectiveLineComparison
open FrobeniusProjectivePoints FrobeniusBlowupContact FrobeniusProductPlaneChart
open FrobeniusGraphPicardClassCharts FrobeniusGraphPicardClassFrames
open FrobeniusGraphPicardClassIntegral FrobeniusGraphPicardClassRational
open FrobeniusGraphPicardClassRulingCoordinates FrobeniusGraphPicardClassChartSections

variable {k : Type u} [Field k]

local instance productIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

def rulingPolynomialMap (d : Fin 2) : Polynomial k →+* planeRing k :=
  if d = 0 then firstCoordinateMap else secondCoordinateMap

def rulingPlaneCoordinate (d : Fin 2) : planeRing k :=
  rulingPolynomialMap d Polynomial.X

theorem productChart_ruling (d i : Fin 2) :
    productChart (k := k) i i ≫ rulingProjection d =
      Spec.map (CommRingCat.ofHom (rulingPolynomialMap d)) ≫ polynomialChartMap k i := by
  fin_cases d
  · simpa [rulingProjection, rulingPolynomialMap] using productChart_fst (k := k) i i
  · simpa [rulingProjection, rulingPolynomialMap] using productChart_snd (k := k) i i

theorem diagonalOpen_le_rulingChart (d i : Fin 2) :
    diagonalOpen (k := k) i ≤ rulingProjection d ⁻¹ᵁ chartOpen k i := by
  intro x hx
  rw [diagonalOpen, Scheme.Hom.image_top_eq_opensRange] at hx
  change x ∈ Set.range (productChart i i).base at hx
  rw [productChart_range] at hx
  fin_cases d
  · simpa [rulingProjection] using hx.1
  · simpa [rulingProjection] using hx.2

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

/-- The original pulled-back ruling section has exactly the corresponding plane coordinate. -/
theorem projection_coordinate_section (d i : Fin 2) :
    (rulingProjection d).appLE (chartOpen k i) (diagonalOpen i)
        (diagonalOpen_le_rulingChart d i) (lineCoordinateSection i) =
      ((productChart i i).appIso ⊤).inv
        ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv (rulingPlaneCoordinate d)) :=
  appLE_section_of_square (productChart (k := k) i i) (rulingProjection d)
    (Spec.map (CommRingCat.ofHom (rulingPolynomialMap d))) (polynomialChartMap k i)
    (chartOpen k i) (diagonalOpen_le_rulingChart d i) (polynomialChart_preimage_top i)
    (productChart_ruling d i) (lineCoordinateSection i)
    ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv (rulingPlaneCoordinate d))
    (rulingPolynomial_coordinate_section d i)

/-- Both coordinate sections can be evaluated through their original projection stalk. -/
def rulingCoordinate (d i : Fin 2) : (projectiveProduct k).functionField :=
  (rulingProjection d).stalkMap (genericPoint (projectiveProduct k))
    ((projectiveSpace k 1).presheaf.germ (chartOpen k i)
      ((rulingProjection d).base (genericPoint (projectiveProduct k)))
      (rulingGeneric_mem d i) (lineCoordinateSection i))

/-- Restricting to the original diagonal open preserves that actual germ. -/
theorem rulingCoordinate_eq_section_germ (d i : Fin 2) :
    rulingCoordinate (k := k) d i =
      (projectiveProduct k).germToFunctionField (diagonalOpen i)
        ((rulingProjection d).appLE (chartOpen k i) (diagonalOpen i)
          (diagonalOpen_le_rulingChart d i) (lineCoordinateSection i)) := by
  simp only [rulingCoordinate, Scheme.Hom.appLE, ConcreteCategory.comp_apply,
    Scheme.germToFunctionField, TopCat.Presheaf.germ_res_apply, Scheme.stalkMap_germ_apply]

/-- The actual projection and actual plane chart give the same function. -/
theorem rulingCoordinate_eq_chart (d i : Fin 2) :
    rulingCoordinate (k := k) d i = chartFunctionFieldMap i (rulingPlaneCoordinate d) := by
  rw [rulingCoordinate_eq_section_germ, projection_coordinate_section]
  rfl

theorem rulingCoordinate_zero (d : Fin 2) :
    rulingCoordinate (k := k) d 0 = rulingLeft d := by
  simp only [rulingCoordinate, lineCoordinateSection_zero, rulingLeft]

theorem rulingCoordinate_one (d : Fin 2) :
    rulingCoordinate (k := k) d 1 = rulingRight d := by
  simp only [rulingCoordinate, lineCoordinateSection_one, rulingRight]

/-- The x in the original graph function is the first original ruling coordinate. -/
theorem rationalX_eq_rulingLeft : rationalX (k := k) = rulingLeft 0 := by
  have h := rulingCoordinate_eq_chart (k := k) 0 0
  simpa [rulingCoordinate_zero, rulingPlaneCoordinate, rulingPolynomialMap, rationalX] using h.symm

/-- The y in the original graph function is the second original ruling coordinate. -/
theorem rationalY_eq_rulingLeft : rationalY (k := k) = rulingLeft 1 := by
  have h := rulingCoordinate_eq_chart (k := k) 1 0
  simpa [rulingCoordinate_zero, rulingPlaneCoordinate, rulingPolynomialMap, rationalY] using h.symm

theorem reverse_chart_u : chartFunctionFieldMap (k := k) 1 uCoord = (rationalX)⁻¹ := by
  have h := rulingCoordinate_eq_chart (k := k) 0 1
  rw [rationalX_eq_rulingLeft, ← rulingRight_eq_inverse]
  simpa [rulingCoordinate_one, rulingPlaneCoordinate, rulingPolynomialMap] using h.symm

theorem reverse_chart_v : chartFunctionFieldMap (k := k) 1 vCoord = (rationalY)⁻¹ := by
  have h := rulingCoordinate_eq_chart (k := k) 1 1
  rw [rationalY_eq_rulingLeft, ← rulingRight_eq_inverse]
  simpa [rulingCoordinate_one, rulingPlaneCoordinate, rulingPolynomialMap] using h.symm

end KltDP.Examples.FrobeniusGraphPicardClassCoordinateComparison

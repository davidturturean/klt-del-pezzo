import KltDP.Geometry.ProjectiveLineTranslation

/-!
# The translation `τ_a × τ_b` of `P¹ ×_k P¹` and the translated Frobenius chart

The product `productTranslation a b := τ_a × τ_b` of two translations of the projective line
(`ProjectiveLineTranslation`) is an automorphism of the actual product `projectiveProduct k` over
`k` (`productTranslationIso`), and on the affine plane chart it is the accepted affine translation
`(u, v) ↦ (u + a, v + b)`: `planeChart ≫ productTranslation a b = (planeTranslationIso a b).hom ≫
planeChart` (`planeChart_productTranslation`). Hence the accepted translated chart of the contact
tower at `(a, a^p)` is the origin chart moved by the product translation:
`translatedPlaneChart p a = planeChart ≫ productTranslation a (a^p)` (`translatedPlaneChart_eq`),
which sends the origin to the graph point `(a, a^p)` (`productTranslation_center`). In
characteristic `p` the translation `τ_a × τ_{a^p}` preserves the Frobenius graph `y = x^p`
(`graphTranslation`, `graphTranslation_ι`: `(x + a)^p = x^p + a^p`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.ProjectiveProductTranslation

open KltDP.Geometry KltDP.Geometry.ProjectiveLineTranslation ProjectiveLineComparison
open FrobeniusProjectivePoints FrobeniusProductPlaneChart FrobeniusGlobalBlowupStages
  FrobeniusTranslatedCharts FrobeniusGraphClosed FrobeniusBlowupContact
  FrobeniusBlowupChartIteration

variable {k : Type u} [Field k]

/-- **The translation `τ_a × τ_b` of `P¹ ×_k P¹`.** -/
def productTranslation (a b : k) : projectiveProduct k ⟶ projectiveProduct k :=
  pullback.map (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)
    (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)
    (projectiveTranslation a) (projectiveTranslation b) (𝟙 _)
    (by rw [Category.comp_id, projectiveTranslation_over_base])
    (by rw [Category.comp_id, projectiveTranslation_over_base])

@[reassoc] theorem productTranslation_fst (a b : k) :
    productTranslation a b ≫ pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) =
      pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) ≫
        projectiveTranslation a :=
  pullback.lift_fst _ _ _

@[reassoc] theorem productTranslation_snd (a b : k) :
    productTranslation a b ≫ pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) =
      pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) ≫
        projectiveTranslation b :=
  pullback.lift_snd _ _ _

/-- The product translation is over `k`. -/
theorem productTranslation_over_base (a b : k) :
    productTranslation a b ≫ projectiveProductToSpec = projectiveProductToSpec := by
  rw [projectiveProductToSpec, ← Category.assoc, productTranslation_fst, Category.assoc,
    projectiveTranslation_over_base]

theorem productTranslation_comp (a b a' b' : k) :
    productTranslation a b ≫ productTranslation a' b' = productTranslation (a + a') (b + b') := by
  apply pullback.hom_ext
  · rw [Category.assoc, productTranslation_fst, productTranslation_fst_assoc, productTranslation_fst,
      projectiveTranslation_comp]
  · rw [Category.assoc, productTranslation_snd, productTranslation_snd_assoc, productTranslation_snd,
      projectiveTranslation_comp]

theorem productTranslation_zero : productTranslation (0 : k) 0 = 𝟙 (projectiveProduct k) := by
  apply pullback.hom_ext
  · rw [productTranslation_fst, projectiveTranslation_zero, Category.comp_id, Category.id_comp]
  · rw [productTranslation_snd, projectiveTranslation_zero, Category.comp_id, Category.id_comp]

/-- **The translation automorphism `τ_a × τ_b : P¹ × P¹ ≅ P¹ × P¹`**, with inverse
`τ_{−a} × τ_{−b}`. -/
def productTranslationIso (a b : k) : projectiveProduct k ≅ projectiveProduct k where
  hom := productTranslation a b
  inv := productTranslation (-a) (-b)
  hom_inv_id := by
    rw [productTranslation_comp, add_neg_cancel, add_neg_cancel, productTranslation_zero]
  inv_hom_id := by
    rw [productTranslation_comp, neg_add_cancel, neg_add_cancel, productTranslation_zero]

instance productTranslation_isIso (a b : k) : IsIso (productTranslation a b) :=
  ⟨productTranslation (-a) (-b), (productTranslationIso a b).hom_inv_id,
    (productTranslationIso a b).inv_hom_id⟩

/-! ## The affine plane chart -/

theorem coordinateTranslation_comp_first (a b : k) :
    (coordinateTranslation a b).toRingHom.comp firstCoordinateMap =
      firstCoordinateMap.comp (parameterTranslation a).toRingHom := by
  apply RingHom.ext
  intro f
  change coordinateTranslation a b (Polynomial.C f) = Polynomial.C (parameterTranslation a f)
  exact coordinateTranslation_C a b f

theorem coordinateTranslation_comp_second (a b : k) :
    (coordinateTranslation a b).toRingHom.comp secondCoordinateMap =
      secondCoordinateMap.comp (parameterTranslation b).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    change coordinateTranslation a b (secondCoordinateMap (Polynomial.C r)) =
      secondCoordinateMap (parameterTranslation b (Polynomial.C r))
    rw [secondCoordinateMap_C, coordinateTranslation_constants, parameterTranslation_C,
      secondCoordinateMap_C]
  · change coordinateTranslation a b (secondCoordinateMap Polynomial.X) =
      secondCoordinateMap (parameterTranslation b Polynomial.X)
    rw [secondCoordinateMap_X, coordinateTranslation_v, parameterTranslation_X, map_add,
      secondCoordinateMap_X, secondCoordinateMap_C]

theorem planeTranslationIso_hom_first (a b : k) :
    (planeTranslationIso a b).hom ≫ Spec.map (CommRingCat.ofHom (firstCoordinateMap (k := k))) =
      Spec.map (CommRingCat.ofHom (firstCoordinateMap (k := k))) ≫
        (parameterTranslationIso a).hom := by
  change Spec.map (CommRingCat.ofHom (coordinateTranslation a b).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (firstCoordinateMap (k := k))) =
    Spec.map (CommRingCat.ofHom (firstCoordinateMap (k := k))) ≫
      Spec.map (CommRingCat.ofHom (parameterTranslation a).toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    coordinateTranslation_comp_first]

theorem planeTranslationIso_hom_second (a b : k) :
    (planeTranslationIso a b).hom ≫ Spec.map (CommRingCat.ofHom (secondCoordinateMap (k := k))) =
      Spec.map (CommRingCat.ofHom (secondCoordinateMap (k := k))) ≫
        (parameterTranslationIso b).hom := by
  change Spec.map (CommRingCat.ofHom (coordinateTranslation a b).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (secondCoordinateMap (k := k))) =
    Spec.map (CommRingCat.ofHom (secondCoordinateMap (k := k))) ≫
      Spec.map (CommRingCat.ofHom (parameterTranslation b).toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    coordinateTranslation_comp_second]

/-- **On the affine plane chart the product translation is the accepted affine translation
`(u, v) ↦ (u + a, v + b)`.** -/
theorem planeChart_productTranslation (a b : k) :
    planeChart ≫ productTranslation a b = (planeTranslationIso a b).hom ≫ planeChart := by
  apply pullback.hom_ext
  · have hL : planeChart ≫ productTranslation a b ≫
        pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) =
        Spec.map (CommRingCat.ofHom (firstCoordinateMap (k := k))) ≫
          ((parameterTranslationIso a).hom ≫ polynomialChartMap k 0) := by
      rw [productTranslation_fst, ← Category.assoc, planeChart_fst, Category.assoc,
        polynomialChartMap_projectiveTranslation]
    have hR : ((planeTranslationIso a b).hom ≫ planeChart) ≫
        pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) =
        Spec.map (CommRingCat.ofHom (firstCoordinateMap (k := k))) ≫
          ((parameterTranslationIso a).hom ≫ polynomialChartMap k 0) := by
      rw [Category.assoc, planeChart_fst, ← Category.assoc, planeTranslationIso_hom_first,
        Category.assoc]
    rw [Category.assoc, hL, hR]
  · have hL : planeChart ≫ productTranslation a b ≫
        pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) =
        Spec.map (CommRingCat.ofHom (secondCoordinateMap (k := k))) ≫
          ((parameterTranslationIso b).hom ≫ polynomialChartMap k 0) := by
      rw [productTranslation_snd, ← Category.assoc, planeChart_snd, Category.assoc,
        polynomialChartMap_projectiveTranslation]
    have hR : ((planeTranslationIso a b).hom ≫ planeChart) ≫
        pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) =
        Spec.map (CommRingCat.ofHom (secondCoordinateMap (k := k))) ≫
          ((parameterTranslationIso b).hom ≫ polynomialChartMap k 0) := by
      rw [Category.assoc, planeChart_snd, ← Category.assoc, planeTranslationIso_hom_second,
        Category.assoc]
    rw [Category.assoc, hL, hR]

/-- **The accepted translated chart is the origin chart moved by the product translation.** -/
theorem translatedPlaneChart_eq (p : ℕ) (a : k) :
    translatedPlaneChart p a = planeChart ≫ productTranslation a (a ^ p) := by
  rw [translatedPlaneChart, planeChart_productTranslation]

/-- The product translation sends the origin of the plane chart to the graph point `(a, a^p)`. -/
theorem productTranslation_center (p : ℕ) (a : k) :
    (productTranslation a (a ^ p)).base (planeChart.base (originPoint (k := k))) =
      graphPoint p a := by
  change (planeChart ≫ productTranslation a (a ^ p)).base (originPoint (k := k)) = _
  rw [← translatedPlaneChart_eq]
  exact translatedInitial_centerPoint p a

/-! ## The Frobenius graph is preserved -/

section Frobenius

variable (p : ℕ) [Fact p.Prime] [CharP k p]

theorem productTranslation_graph_condition (a : k) :
    (graphι p ≫ productTranslation a (a ^ p)) ≫
        (firstProjection ≫ KltDP.Examples.FrobeniusProjectiveMorphism.projectivePowerMorphism p) =
      (graphι p ≫ productTranslation a (a ^ p)) ≫ secondProjection := by
  have h1 : productTranslation a (a ^ p) ≫
      (firstProjection ≫ KltDP.Examples.FrobeniusProjectiveMorphism.projectivePowerMorphism p) =
      (firstProjection ≫ KltDP.Examples.FrobeniusProjectiveMorphism.projectivePowerMorphism p) ≫
        projectiveTranslation (a ^ p) := by
    rw [← Category.assoc, productTranslation_fst, Category.assoc, projectiveTranslation_power,
      Category.assoc]
  have h2 : productTranslation a (a ^ p) ≫ secondProjection =
      secondProjection ≫ projectiveTranslation (a ^ p) := productTranslation_snd a (a ^ p)
  have hL : (graphι p ≫ productTranslation a (a ^ p)) ≫
      (firstProjection ≫ KltDP.Examples.FrobeniusProjectiveMorphism.projectivePowerMorphism p) =
      (graphι p ≫
        (firstProjection ≫ KltDP.Examples.FrobeniusProjectiveMorphism.projectivePowerMorphism p)) ≫
        projectiveTranslation (a ^ p) := by
    rw [Category.assoc, h1, ← Category.assoc]
  have hR : (graphι p ≫ productTranslation a (a ^ p)) ≫ secondProjection =
      (graphι p ≫ secondProjection) ≫ projectiveTranslation (a ^ p) := by
    rw [Category.assoc, h2, ← Category.assoc]
  rw [hL, hR, graphι, equalizer.condition]

/-- **The translation `τ_a × τ_{a^p}` preserves the Frobenius graph** (`(x + a)^p = x^p + a^p`):
the induced automorphism of the closed graph `y = x^p`. -/
def graphTranslation (a : k) : graph (k := k) p ⟶ graph (k := k) p :=
  equalizer.lift (graphι p ≫ productTranslation a (a ^ p)) (productTranslation_graph_condition p a)

@[reassoc] theorem graphTranslation_ι (a : k) :
    graphTranslation p a ≫ graphι p = graphι p ≫ productTranslation a (a ^ p) :=
  equalizer.lift_ι _ _

/-- Points of the graph are sent to points of the graph. -/
theorem productTranslation_mem_range_graphι (a : k) (x : projectiveProduct k)
    (hx : x ∈ Set.range (graphι (k := k) p).base) :
    (productTranslation a (a ^ p)).base x ∈ Set.range (graphι (k := k) p).base := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨(graphTranslation p a).base y, ?_⟩
  change (graphTranslation p a ≫ graphι p).base y = (graphι p ≫ productTranslation a (a ^ p)).base y
  rw [graphTranslation_ι]

end Frobenius

end KltDP.Examples.ProjectiveProductTranslation

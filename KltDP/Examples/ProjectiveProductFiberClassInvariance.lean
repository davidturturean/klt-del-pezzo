import KltDP.Examples.FrobeniusFiberZeroClass
import KltDP.Examples.FrobeniusFiberTranslation
import KltDP.Examples.ProjectiveLinePointAtInfinity
import KltDP.Geometry.ProjectiveLineChartFunctions
import KltDP.Geometry.SpecHomRingHom
import KltDP.Geometry.SchematicImageToImageIso
import KltDP.Examples.FrobeniusMultiCentreIsoOpenClasses

/-!
# Translation invariance of the fibre classes of `P¹ × P¹`

For every `c : k` the horizontal fibre `y = c` (`horizontalFiberMorphism c`) and the vertical fibre
`x = c` (`verticalFiberMorphismAt c`) of `P¹ ×_k P¹` have the accepted fibre classes:
`−[I(y = c)] = b = secondFiberClass` and `−[I(x = c)] = a = firstFiberClass` in `Additive Pic`
(`horizontalFiberClass_eq_secondFiberClass`, `verticalFiberClass_eq_firstFiberClass`).

Route (the principal-divisor route of F28 and of the accepted `FrobeniusFiberZeroClass`):
* `fiberAtDivisor c := R_∞ + div(y − c)` (the accepted `rulingInfinityDivisor 1` plus the principal
  divisor of the function `y − c`); on the two ruling opens it has the equations `y − c` and
  `y⁻¹·(y − c)` (`fiberAtDivisor_restrict_ruling`), hence the regular equations `v − c` on the product
  charts `(i, 0)` and `1 − c·v` on `(i, 1)` (`fiberAtChartZero`, `fiberAtChartOne`); the germ of the
  constant `c` is the same on every product chart (`productFunctionFieldMap_C_C_eq`, through the
  structure morphism of `P¹ × P¹`);
* its ideal sheaf is the kernel of the fibre (`fiberAtIdealData_eq`): on the chart `(i, 0)` the fibre is
  the line `v = c` of the chart (`fiberCurveAt_productChart_zero`); on the chart `(i, 1)` it is the line
  `v = c⁻¹` for `c ≠ 0` (`fiberCurveAt_productChart_one`, from the point identity
  `Spec(t ↦ c⁻¹) ≫ chart₁ = [1 : c]`, `polynomialChartMap_one_evaluation`, proved with the accepted
  chart-function relation `chart_function_relation`), and it is absent for `c = 0` (accepted);
* `O(−fiberAtDivisor c)` is the kernel module of the fibre (`effectiveCartierKernelIso`, `toImageIso`),
  so `−[I(y = c)] = cartierPicardHom R_∞ = secondFiberClass`; the vertical fibre is the swap of the
  horizontal one (`verticalFiberMorphismAt_eq_swap`, accepted `swap_inv_rulingPicard`).

Consequences on `S_{p,n} = multiSurface (q+1) n a`: the pulled-back translated fibre classes of
`FrobeniusMultiCentreCurveKernels` are the accepted classes (`multiTranslatedFirstFiberClass_eq`,
`multiTranslatedSecondFiberClass_eq`), so the graph row of the class table on every cluster open holds with
`multiFirstFiberClass`, `multiSecondFiberClass` (`clusterGraphClass_accepted`), and on the isomorphism
open `U₀` of the composite blowdown the class of `F_i` is the restriction of `multiSecondFiberClass`
(`isoOpenFiberKernelLine_toPic_accepted`). No statement in `Pic S_{p,n}` itself is made here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Examples.ProjectiveProductFiberClassInvariance

open KltDP.Geometry KltDP.Geometry.ProjectiveLineComparison
  KltDP.Geometry.SchemeKernelIdealIsoTransport KltDP.Geometry.SchematicImageToImageIso
open FrobeniusProjectivePoints FrobeniusBlowupContact FrobeniusBlowupChartIteration
  FrobeniusProductPlaneChart FrobeniusGraphPicardClassCharts FrobeniusGraphPicardClassIntegral
  FrobeniusGraphPicardClassMixedCoordinates FrobeniusGraphPicardClassCoordinateComparison
  FrobeniusGraphPicardClassRulingCoordinates FrobeniusGraphPicardClassRulingDivisors
  FrobeniusGraphPicardClassZeroFiber FrobeniusGraphPicardClassFiberClasses
  FrobeniusGraphPicardClassSwap FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassRational
  FrobeniusGraphPicardClassMixedOverlap FrobeniusGraphClosed FrobeniusFiberZeroInvertible
  FrobeniusFiberZeroClass FrobeniusFiberTranslation FrobeniusTranslatedCharts
  ProjectiveLinePointAtInfinity FrobeniusGraphStalkContact FrobeniusGraphContact
  FrobeniusUnaffectedFibers

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

local instance fiberClassProductIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

local instance fiberClassLineIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-! ## The rational point `[1 : c]` on the second chart of `P¹` -/

theorem X_not_mem_parameterPointIdeal {c : k} (hc : c ≠ 0) :
    (Polynomial.X : Polynomial k) ∉ parameterPointIdeal c := by
  intro hX
  have h : (Polynomial.X : Polynomial k) ∈ RingHom.ker (Polynomial.evalRingHom c) := by
    rw [Polynomial.ker_evalRingHom]
    exact hX
  rw [RingHom.mem_ker, Polynomial.coe_evalRingHom, Polynomial.eval_X] at h
  exact hc h

/-- For `c ≠ 0` the point `[1 : c]` lies on the second polynomial chart. -/
theorem pointMorphism_range_subset_chartOne {c : k} (hc : c ≠ 0) :
    Set.range (pointMorphism c).base ⊆ Set.range (polynomialChartMap k 1).base := by
  rintro _ ⟨z, rfl⟩
  have hz : (pointMorphism c).base z = FrobeniusProjectivePoints.point c := by
    unfold FrobeniusProjectivePoints.point fieldMorphismPoint
    exact congrArg (pointMorphism c).base (Subsingleton.elim _ _)
  have hmem : FrobeniusProjectivePoints.point c ∈ chartOpen k 1 := by
    rw [point_eq_chart]
    exact (polynomialChart_mem_other_iff (k := k) 0 (parameterSchemePoint c)).mpr
      (X_not_mem_parameterPointIdeal hc)
  rw [hz]
  rw [← polynomialChartMap_opensRange] at hmem
  exact hmem

/-- The lift of `[1 : c]` (`c ≠ 0`) to the second polynomial chart. -/
def chartOnePoint {c : k} (hc : c ≠ 0) :
    Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Polynomial k)) :=
  IsOpenImmersion.lift (polynomialChartMap k 1) (pointMorphism c)
    (pointMorphism_range_subset_chartOne hc)

theorem chartOnePoint_fac {c : k} (hc : c ≠ 0) :
    chartOnePoint hc ≫ polynomialChartMap k 1 = pointMorphism c :=
  IsOpenImmersion.lift_fac _ _ _

theorem specHomRingHom_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    specHomRingHom (Spec.map φ) = φ ≫ specHomRingHom (𝟙 (Spec S)) := by
  rw [← specHomRingHom_comp_specMap, Category.id_comp]

/-- The lift of `[1 : c]` to the second chart is evaluation at `c⁻¹`. -/
theorem chartOnePoint_eq {c : k} (hc : c ≠ 0) :
    chartOnePoint hc = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c⁻¹)) := by
  have hbase : chartOnePoint hc ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) =
      𝟙 (Spec (CommRingCat.of k)) ≫ Spec.map (𝟙 (CommRingCat.of k)) := by
    rw [← polynomialChartMap_structureMap k 1, ← Category.assoc, chartOnePoint_fac,
      pointMorphism_over_base, Spec.map_id, Category.comp_id]
  have hC := specHomRingHom_congr hbase
  have hrel := (chart_function_relation k (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c)))
    (chartOnePoint hc) 0 1
    ((polynomialChartMap_evaluation c).trans (chartOnePoint_fac hc).symm)).2 (by decide)
  rw [specHomRingHom_specMap] at hrel
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
    Polynomial.coe_evalRingHom, Polynomial.eval_X] at hrel
  have hX : (specHomRingHom (chartOnePoint hc)).hom Polynomial.X =
      (specHomRingHom (𝟙 (Spec (CommRingCat.of k)))).hom c⁻¹ := by
    calc (specHomRingHom (chartOnePoint hc)).hom Polynomial.X
        = (specHomRingHom (𝟙 (Spec (CommRingCat.of k)))).hom (c⁻¹ * c) *
            (specHomRingHom (chartOnePoint hc)).hom Polynomial.X := by
          rw [inv_mul_cancel₀ hc, map_one, one_mul]
      _ = (specHomRingHom (𝟙 (Spec (CommRingCat.of k)))).hom c⁻¹ *
            ((specHomRingHom (𝟙 (Spec (CommRingCat.of k)))).hom c *
              (specHomRingHom (chartOnePoint hc)).hom Polynomial.X) := by
          rw [map_mul, mul_assoc]
      _ = (specHomRingHom (𝟙 (Spec (CommRingCat.of k)))).hom c⁻¹ := by
          rw [hrel, mul_one]
  have hring : specHomRingHom (chartOnePoint hc) =
      specHomRingHom (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c⁻¹))) := by
    rw [specHomRingHom_specMap]
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro r
      have h := congrArg (fun φ => φ.hom r) hC
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_id,
        RingHom.comp_apply, RingHom.id_apply, Category.id_comp] at h
      rw [h]
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
        Polynomial.coe_evalRingHom, Polynomial.eval_C]
    · rw [hX]
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
        Polynomial.coe_evalRingHom, Polynomial.eval_X]
  rw [specHom_eq_toSpecΓ (chartOnePoint hc), hring, ← specHom_eq_toSpecΓ]

/-- **The point `[1 : c]` (`c ≠ 0`) is the parameter `c⁻¹` of the second chart.** -/
theorem polynomialChartMap_one_evaluation {c : k} (hc : c ≠ 0) :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c⁻¹)) ≫ polynomialChartMap k 1 =
      pointMorphism c := by
  rw [← chartOnePoint_eq hc, chartOnePoint_fac]

/-! ## The ideal of the fibre `y = c` on the four product charts -/

instance fiberLineAt_chart_quasiCompact (b : k) (i j : Fin 2) :
    QuasiCompact (fiberCurveAt (k := k) b ≫ productChart i j) :=
  quasiCompact_of_noetherianSpace _

/-- The line `v = c` of the chart `(i, 0)` is the horizontal fibre `y = c` over the `i`-th chart. -/
@[reassoc] theorem fiberCurveAt_productChart_zero (c : k) (i : Fin 2) :
    fiberCurveAt c ≫ productChart i 0 = polynomialChartMap k i ≫ horizontalFiberMorphism c := by
  apply pullback.hom_ext
  · simp only [Category.assoc, horizontalFiberMorphism, pullback.lift_fst, Category.comp_id]
    rw [productChart_fst, ← Category.assoc, fiberCurveAt_firstCoordinate, Category.id_comp]
  · simp only [Category.assoc, horizontalFiberMorphism, pullback.lift_snd]
    rw [productChart_snd, ← Category.assoc, fiberCurveAt_secondCoordinate, ← Category.assoc,
      polynomialChartMap_structureMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      polynomialChartMap_evaluation]

/-- For `c ≠ 0` the line `v = c⁻¹` of the chart `(i, 1)` is the horizontal fibre `y = c` over the
`i`-th chart. -/
@[reassoc] theorem fiberCurveAt_productChart_one {c : k} (hc : c ≠ 0) (i : Fin 2) :
    fiberCurveAt c⁻¹ ≫ productChart i 1 = polynomialChartMap k i ≫ horizontalFiberMorphism c := by
  apply pullback.hom_ext
  · simp only [Category.assoc, horizontalFiberMorphism, pullback.lift_fst, Category.comp_id]
    rw [productChart_fst, ← Category.assoc, fiberCurveAt_firstCoordinate, Category.id_comp]
  · simp only [Category.assoc, horizontalFiberMorphism, pullback.lift_snd]
    rw [productChart_snd, ← Category.assoc, fiberCurveAt_secondCoordinate, ← Category.assoc,
      polynomialChartMap_structureMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      polynomialChartMap_one_evaluation hc]

theorem horizontalFiber_ker_eq_chartZero (c : k) (i : Fin 2) :
    (horizontalFiberMorphism c).ker = (fiberCurveAt c ≫ productChart i 0).ker := by
  rw [fiberCurveAt_productChart_zero]
  exact (SchematicImageOpenImmersion.ker_precompose_openImmersion (polynomialChartMap k i)
    (horizontalFiberMorphism c)).symm

theorem horizontalFiber_ker_eq_chartOne {c : k} (hc : c ≠ 0) (i : Fin 2) :
    (horizontalFiberMorphism c).ker = (fiberCurveAt c⁻¹ ≫ productChart i 1).ker := by
  rw [fiberCurveAt_productChart_one hc]
  exact (SchematicImageOpenImmersion.ker_precompose_openImmersion (polynomialChartMap k i)
    (horizontalFiberMorphism c)).symm

/-- The line `v = b` and the chart `(i, j)` form a pullback square with the identity. -/
theorem fiberCurveAt_productChart_isPullback (b : k) (i j : Fin 2) :
    IsPullback (fiberCurveAt (k := k) b) (𝟙 _) (productChart i j)
      (fiberCurveAt b ≫ productChart i j) := by
  have hr : Set.range (fiberCurveAt (k := k) b ≫ productChart i j).base ⊆
      Set.range (productChart (k := k) i j).base := by
    rintro _ ⟨t, rfl⟩
    exact ⟨(fiberCurveAt (k := k) b).base t,
      (Scheme.comp_base_apply (fiberCurveAt b) (productChart i j) t).symm⟩
  have hLift : IsOpenImmersion.lift (productChart (k := k) i j)
      (fiberCurveAt b ≫ productChart i j) hr = fiberCurveAt b :=
    (IsOpenImmersion.lift_uniq _ _ hr (fiberCurveAt b) rfl).symm
  simpa only [hLift] using
    IsOpenImmersion.isPullback_lift_id (fiberCurveAt (k := k) b ≫ productChart i j)
      (productChart i j) hr

/-- The kernel of the line `v = b`, in the coordinates `k[u][v]` of the plane, is `(v − b)`. -/
theorem fiberCurveAt_coordinateKernel (b : k) :
    RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv ≫
        (fiberCurveAt (k := k) b).appTop).hom) =
      Ideal.span {Polynomial.X - Polynomial.C (Polynomial.C b)} := by
  have hΓ : Function.Injective
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom) :=
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).symm.commRingCatIsoToRingEquiv.injective
  rw [fiberCurveAt, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.hom_comp,
    RingHom.ker_comp_of_injective _ hΓ, CommRingCat.hom_ofHom, Polynomial.ker_evalRingHom]

/-- The section ring map of the product chart `(i, j)`. -/
def chartSectionHom (i j : Fin 2) :
    planeRing k →+* Γ(projectiveProduct k, (fiberChartAffineOpen (k := k) i j).1) :=
  ((productChart (k := k) i j).appIso ⊤).inv.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv.hom

/-- A closed immersion from `P¹` whose kernel is the kernel of the line `v = b` of the chart `(i, j)`
has the chart ideal `(v − b)`. -/
theorem ideal_chart_of_line (g : projectiveSpace k 1 ⟶ projectiveProduct k) [QuasiCompact g]
    (b : k) (i j : Fin 2) (hg : g.ker = (fiberCurveAt b ≫ productChart i j).ker) :
    g.ker.ideal (fiberChartAffineOpen i j) =
      Ideal.span {chartSectionHom i j (vCoord - Polynomial.C (Polynomial.C b))} := by
  have hcomap : Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv.hom
      (Ideal.comap ((productChart (k := k) i j).appIso ⊤).inv.hom
        (g.ker.ideal (fiberChartAffineOpen i j))) =
      Ideal.span {vCoord - Polynomial.C (Polynomial.C b)} := by
    unfold fiberChartAffineOpen
    rw [hg, ← Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
      (fiberCurveAt b ≫ productChart i j) (fiberCurveAt b) (𝟙 _) (productChart i j)
      (fiberCurveAt_productChart_isPullback b i j) ⟨⊤, isAffineOpen_top (plane k)⟩,
      Scheme.Hom.ker_apply]
    change RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv ≫
      (fiberCurveAt (k := k) b).appTop).hom) = _
    exact fiberCurveAt_coordinateKernel b
  have e1 : Function.Surjective ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv.hom) :=
    (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).symm.commRingCatIsoToRingEquiv.surjective
  have e2 : Function.Surjective (((productChart (k := k) i j).appIso ⊤).inv.hom) :=
    ((productChart (k := k) i j).appIso ⊤).symm.commRingCatIsoToRingEquiv.surjective
  calc g.ker.ideal (fiberChartAffineOpen i j)
      = Ideal.map (((productChart (k := k) i j).appIso ⊤).inv.hom)
          (Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv.hom)
            (Ideal.comap ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv.hom)
              (Ideal.comap (((productChart (k := k) i j).appIso ⊤).inv.hom)
                (g.ker.ideal (fiberChartAffineOpen i j))))) := by
        rw [Ideal.map_comap_of_surjective _ e1, Ideal.map_comap_of_surjective _ e2]
    _ = Ideal.span {chartSectionHom i j (vCoord - Polynomial.C (Polynomial.C b))} := by
        rw [hcomap, Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
        rfl

/-- On the chart `(i, 0)` the ideal of the fibre `y = c` is generated by `v − c`. -/
theorem horizontalFiber_ideal_chartZero (c : k) (i : Fin 2) :
    (horizontalFiberMorphism c).ker.ideal (fiberChartAffineOpen i 0) =
      Ideal.span {chartSectionHom i 0 (vCoord - Polynomial.C (Polynomial.C c))} :=
  ideal_chart_of_line _ c i 0 (horizontalFiber_ker_eq_chartZero c i)

theorem chartOne_equation_factor {c : k} (hc : c ≠ 0) :
    (1 - Polynomial.C (Polynomial.C c) * vCoord : planeRing k) =
      Polynomial.C (Polynomial.C (-c)) * (vCoord - Polynomial.C (Polynomial.C c⁻¹)) := by
  have h : (Polynomial.C (Polynomial.C c) * Polynomial.C (Polynomial.C c⁻¹) : planeRing k) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one]
  simp only [map_neg]
  linear_combination (-1 : planeRing k) * h

/-- On the chart `(i, 1)` the ideal of the fibre `y = c` is generated by `1 − c·v`. -/
theorem horizontalFiber_ideal_chartOne (c : k) (i : Fin 2) :
    (horizontalFiberMorphism c).ker.ideal (fiberChartAffineOpen i 1) =
      Ideal.span {chartSectionHom i 1 (1 - Polynomial.C (Polynomial.C c) * vCoord)} := by
  by_cases hc : c = 0
  · subst hc
    rw [horizontalFiber_ideal_chart_one i]
    simp only [map_zero, zero_mul, sub_zero, map_one]
  · rw [ideal_chart_of_line _ c⁻¹ i 1 (horizontalFiber_ker_eq_chartOne hc i),
      chartOne_equation_factor hc, map_mul, Ideal.span_singleton_mul_left_unit]
    exact (Polynomial.isUnit_C.mpr (Polynomial.isUnit_C.mpr
      (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hc)))).map _

/-! ## Constants in the function field -/

theorem productChart_structure (i j : Fin 2) :
    productChart (k := k) i j ≫ projectiveProductToSpec =
      Spec.map (CommRingCat.ofHom
        ((Polynomial.C : Polynomial k →+* planeRing k).comp Polynomial.C)) := by
  unfold projectiveProductToSpec
  rw [← Category.assoc, productChart_fst, Category.assoc, polynomialChartMap_structureMap k i,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- The chart section of a constant is the restriction of the global constant. -/
theorem chartSectionHom_C_C (i j : Fin 2) (c : k) :
    chartSectionHom (k := k) i j (Polynomial.C (Polynomial.C c)) =
      ((projectiveProduct k).presheaf.map
        (homOfLE (le_top : (fiberChartAffineOpen (k := k) i j).1 ≤ ⊤)).op).hom
        ((projectiveProductToSpec (k := k)).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) := by
  have h1 := congrArg (fun φ => φ.hom c) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom ((Polynomial.C : Polynomial k →+* planeRing k).comp Polynomial.C)))
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h1
  rw [← productChart_structure i j, Scheme.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply] at h1
  have h2 := congrArg (fun φ => φ.hom ((projectiveProductToSpec (k := k)).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)))
    (Scheme.Hom.appLE_appIso_inv (productChart (k := k) i j) (U := ⊤) (V := ⊤) le_rfl)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  have htop : (productChart (k := k) i j).appLE ⊤ ⊤ le_rfl = (productChart (k := k) i j).appTop :=
    Scheme.Hom.appLE_eq_app _ (U := ⊤)
  rw [htop, ← h1] at h2
  exact h2

theorem productFunctionFieldMap_C_C (i j : Fin 2) (c : k) :
    productFunctionFieldMap (k := k) i j (Polynomial.C (Polynomial.C c)) =
      (projectiveProduct k).presheaf.germ ⊤ (genericPoint (projectiveProduct k)) trivial
        ((projectiveProductToSpec (k := k)).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) := by
  change (projectiveProduct k).germToFunctionField (productOpen i j)
    (chartSectionHom i j (Polynomial.C (Polynomial.C c))) = _
  rw [chartSectionHom_C_C]
  change (projectiveProduct k).presheaf.germ (productOpen i j) (genericPoint (projectiveProduct k)) _
      ((projectiveProduct k).presheaf.map
        (homOfLE (le_top : productOpen (k := k) i j ≤ ⊤)).op
        ((projectiveProductToSpec (k := k)).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))) = _
  rw [TopCat.Presheaf.germ_res_apply]

/-- **The germ of a constant does not depend on the product chart.** -/
theorem productFunctionFieldMap_C_C_eq (i j : Fin 2) (c : k) :
    productFunctionFieldMap (k := k) i j (Polynomial.C (Polynomial.C c)) =
      productFunctionFieldMap (k := k) 0 0 (Polynomial.C (Polynomial.C c)) := by
  rw [productFunctionFieldMap_C_C, productFunctionFieldMap_C_C]

/-! ## The effective Cartier divisor of the fibre `y = c` -/

/-- The function `y − c`, read through the chart `(0, 0)`. -/
def yMinus (c : k) : (projectiveProduct k).functionField :=
  productFunctionFieldMap (k := k) 0 0 (vCoord - Polynomial.C (Polynomial.C c))

theorem yMinus_ne_zero (c : k) : yMinus (k := k) c ≠ 0 := by
  intro h
  have h' : chartFunctionFieldMap (k := k) 0 (vCoord - Polynomial.C (Polynomial.C c)) =
      chartFunctionFieldMap (k := k) 0 0 := by
    rw [map_zero]
    exact h
  exact Polynomial.X_sub_C_ne_zero (Polynomial.C c) (chartFunctionFieldMap_injective (k := k) 0 h')

/-- `y − c` as a unit of the function field. -/
def yMinusUnit (c : k) : (projectiveProduct k).functionFieldˣ :=
  Units.mk0 (yMinus c) (yMinus_ne_zero c)

/-- **The divisor `R_∞ + div(y − c)`.** -/
def fiberAtDivisor (c : k) : CartierDivisor (projectiveProduct k) :=
  rulingInfinityDivisor 1 +
    principalCartierDivisorHom (projectiveProduct k) (Additive.ofMul (yMinusUnit c))

/-- Its equations on the two ruling opens: `y − c` and `y⁻¹·(y − c)`. -/
def fiberAtEquation (c : k) (j : Fin 2) : (projectiveProduct k).functionFieldˣ :=
  rulingInfinityEquation 1 j * yMinusUnit c

theorem fiberAtDivisor_restrict_ruling (c : k) (j : Fin 2) :
    cartierEquationClassHom (projectiveProduct k) (rulingOpen 1 j)
        (Additive.ofMul (fiberAtEquation c j)) =
      (cartierDivisorSheaf (projectiveProduct k)).val.map
        (homOfLE (show rulingOpen (k := k) 1 j ≤ ⊤ from le_top)).op (fiberAtDivisor c) := by
  rw [fiberAtDivisor, map_add, rulingInfinityDivisor_restrict, principalCartierDivisorHom,
    cartierEquationClassHom_restrict, ← map_add, ← ofMul_mul, fiberAtEquation]

/-- On the chart `(i, 0)` the divisor has the regular equation `v − c`. -/
def fiberAtChartZero (c : k) (i : Fin 2) :
    RegularCartierEquationChart (projectiveProduct k) (fiberAtDivisor (k := k) c) where
  chart :=
    { openSet := productOpen i 0
      nonempty := productOpen_nonempty i 0
      equation := fiberAtEquation c 0
      represents := cartierGlobalEquation_restrict (projectiveProduct k) (fiberAtDivisor c)
        (homOfLE (productOpen_le_rulingOpen i 0)) (fiberAtEquation c 0)
        (fiberAtDivisor_restrict_ruling c 0) }
  coefficient := chartSectionHom i 0 (vCoord - Polynomial.C (Polynomial.C c))
  germ_eq := by
    change productFunctionFieldMap (k := k) i 0 (vCoord - Polynomial.C (Polynomial.C c)) =
      ((rulingInfinityEquation 1 0 : (projectiveProduct k).functionFieldˣ) :
        (projectiveProduct k).functionField) *
        productFunctionFieldMap (k := k) 0 0 (vCoord - Polynomial.C (Polynomial.C c))
    have h1 : rulingInfinityEquation (k := k) 1 0 = 1 := if_pos rfl
    rw [h1, Units.val_one, one_mul, map_sub, map_sub, productFunctionFieldMap_v,
      productFunctionFieldMap_v, productFunctionFieldMap_C_C_eq i 0 c]

/-- On the chart `(i, 1)` the divisor has the regular equation `1 − c·v`. -/
def fiberAtChartOne (c : k) (i : Fin 2) :
    RegularCartierEquationChart (projectiveProduct k) (fiberAtDivisor (k := k) c) where
  chart :=
    { openSet := productOpen i 1
      nonempty := productOpen_nonempty i 1
      equation := fiberAtEquation c 1
      represents := cartierGlobalEquation_restrict (projectiveProduct k) (fiberAtDivisor c)
        (homOfLE (productOpen_le_rulingOpen i 1)) (fiberAtEquation c 1)
        (fiberAtDivisor_restrict_ruling c 1) }
  coefficient := chartSectionHom i 1 (1 - Polynomial.C (Polynomial.C c) * vCoord)
  germ_eq := by
    change productFunctionFieldMap (k := k) i 1 (1 - Polynomial.C (Polynomial.C c) * vCoord) =
      ((rulingInfinityEquation 1 1 : (projectiveProduct k).functionFieldˣ) :
        (projectiveProduct k).functionField) *
        productFunctionFieldMap (k := k) 0 0 (vCoord - Polynomial.C (Polynomial.C c))
    have h1 : rulingInfinityEquation (k := k) 1 1 = (rulingCoordinateUnit 1)⁻¹ := if_neg (by decide)
    have h2 : (((rulingCoordinateUnit (k := k) 1)⁻¹ : (projectiveProduct k).functionFieldˣ) :
        (projectiveProduct k).functionField) = rulingRight 1 := rfl
    rw [h1, h2, map_sub, map_one, map_mul, map_sub, productFunctionFieldMap_v,
      productFunctionFieldMap_v, productFunctionFieldMap_C_C_eq i 1 c, rulingCoordinate_one,
      rulingCoordinate_zero]
    have h3 := rulingCoordinates_mul (k := k) 1
    linear_combination (-1 : (projectiveProduct k).functionField) * h3

theorem fiberAtDivisor_hasRegularEquations (c : k) :
    HasRegularCartierEquations (projectiveProduct k) (fiberAtDivisor (k := k) c) := by
  intro x
  obtain ⟨i, j, hx⟩ := productCharts_cover x
  have hx' := mem_productOpen_of_mem_range i j x hx
  fin_cases j
  · exact ⟨fiberAtChartZero c i, hx'⟩
  · exact ⟨fiberAtChartOne c i, hx'⟩

/-! ## The ideal sheaf of the divisor is the ideal sheaf of the fibre -/

theorem fiberAt_chart_ideal_eq (c : k) (i j : Fin 2) :
    (effectiveCartierIdealDataOfRegularEquations (projectiveProduct k) (fiberAtDivisor c)
        (fiberAtDivisor_hasRegularEquations c)).ideal (fiberChartAffineOpen (k := k) i j) =
      (horizontalFiberMorphism c).ker.ideal (fiberChartAffineOpen i j) := by
  fin_cases j
  · exact (effectiveCartierIdealDataOfRegularEquations_ideal_chart (projectiveProduct k)
      (fiberAtDivisor c) (fiberAtDivisor_hasRegularEquations c) (fiberAtChartZero c i)
      (fiberChartAffineOpen (k := k) i 0).2).trans (horizontalFiber_ideal_chartZero c i).symm
  · exact (effectiveCartierIdealDataOfRegularEquations_ideal_chart (projectiveProduct k)
      (fiberAtDivisor c) (fiberAtDivisor_hasRegularEquations c) (fiberAtChartOne c i)
      (fiberChartAffineOpen (k := k) i 1).2).trans (horizontalFiber_ideal_chartOne c i).symm

/-- **The ideal sheaf of the effective Cartier divisor `fiberAtDivisor c` is the kernel of the fibre
`y = c`.** -/
theorem fiberAtIdealData_eq (c : k) :
    effectiveCartierIdealDataOfRegularEquations (projectiveProduct k) (fiberAtDivisor c)
        (fiberAtDivisor_hasRegularEquations c) =
      (horizontalFiberMorphism c).ker := by
  rw [← effectiveCartierIdealDataOfRegularEquations_ker (projectiveProduct k) (fiberAtDivisor c)
    (fiberAtDivisor_hasRegularEquations c), horizontalFiber_ker_eq_chartZero c 0]
  apply Scheme.Hom.ker_eq_of_cover _ _
    (fun ij : Fin 2 × Fin 2 => (fiberChartAffineOpen (k := k) ij.1 ij.2).1)
  · intro y
    obtain ⟨i, j, hy⟩ := productCharts_cover y
    exact ⟨(i, j), mem_fiberChartAffineOpen_of_mem_range i j y hy⟩
  · rintro ⟨i, j⟩ W hW
    dsimp only at hW
    rw [effectiveCartierIdealDataOfRegularEquations_ker, ← horizontalFiber_ker_eq_chartZero c 0,
      ← Scheme.IdealSheafData.map_ideal _ hW, ← Scheme.IdealSheafData.map_ideal _ hW,
      fiberAt_chart_ideal_eq c i j]

/-! ## Picard classes -/

/-- `O(−fiberAtDivisor c)` is the kernel module of the fibre `y = c`. -/
def fiberAtKernelIso (c : k) :
    cartierDivisorModule (projectiveProduct k) (-fiberAtDivisor c) ≅
      (FrobeniusMultiCentreIsoOpenClasses.horizontalFiberLine c).obj :=
  effectiveCartierKernelIso (projectiveProduct k) (fiberAtDivisor c)
      (fiberAtDivisor_hasRegularEquations c) ≪≫
    eqToIso (congrArg (fun I : (projectiveProduct k).IdealSheafData => schemeKernelIdeal I.gluedTo)
      (fiberAtIdealData_eq c)) ≪≫
    (schemeKernelPrecompIso (toImageIso (horizontalFiberMorphism c))
      (SchematicImageGlued.inclusion (horizontalFiberMorphism c))).symm ≪≫
    schemeKernelIdealEqIso (toImageIso_hom_inclusion (horizontalFiberMorphism c))

theorem horizontalFiberLine_toPic (c : k) :
    (FrobeniusMultiCentreIsoOpenClasses.horizontalFiberLine (k := k) c).toPic =
      cartierPicardClass (projectiveProduct k) (-fiberAtDivisor c) := by
  letI := Scheme.Modules.monoidalCategory (projectiveProduct k)
  apply Units.ext
  rw [InvertibleSheaf.toPic_val, cartierPicardClass_val]
  exact Quotient.sound ⟨(fiberAtKernelIso c).symm⟩

/-- **`−[I(y = c)] = b`**: the class of every horizontal fibre is the accepted second fibre class. -/
theorem horizontalFiberClass_eq_secondFiberClass (c : k) :
    -Additive.ofMul (FrobeniusMultiCentreIsoOpenClasses.horizontalFiberLine (k := k) c).toPic =
      secondFiberClass := by
  have hdef : cartierPicardHom (projectiveProduct k) (fiberAtDivisor (k := k) c) =
      Additive.ofMul (cartierPicardClass (projectiveProduct k) (fiberAtDivisor c)) := rfl
  rw [horizontalFiberLine_toPic, cartierPicardClass_neg, ofMul_inv, neg_neg, ← hdef, fiberAtDivisor,
    map_add, cartierPicardHom_principal, add_zero, secondFiberClass_eq_ruling]

/-- The vertical fibre `x = c` is the swap of the horizontal fibre `y = c`. -/
theorem verticalFiberMorphismAt_eq_swap (c : k) :
    verticalFiberMorphismAt c = horizontalFiberMorphism c ≫ (productSwapIso (k := k)).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    change verticalFiberMorphismAt c ≫ firstProjection =
      horizontalFiberMorphism c ≫ ((pullbackSymmetry _ _).hom ≫ pullback.fst _ _)
    rw [verticalFiberMorphismAt_fst, pullbackSymmetry_hom_comp_fst]
    exact (horizontalFiberMorphism_snd c).symm
  · rw [Category.assoc]
    change verticalFiberMorphismAt c ≫ secondProjection =
      horizontalFiberMorphism c ≫ ((pullbackSymmetry _ _).hom ≫ pullback.snd _ _)
    rw [verticalFiberMorphismAt_snd, pullbackSymmetry_hom_comp_snd]
    exact (horizontalFiberMorphism_fst c).symm

theorem vertical_swap_square (c : k) :
    (Iso.refl (projectiveSpace k 1)).hom ≫ verticalFiberMorphismAt c =
      horizontalFiberMorphism c ≫ (productSwapIso (k := k)).hom := by
  rw [Iso.refl_hom, Category.id_comp, verticalFiberMorphismAt_eq_swap]

theorem verticalFiberKernel_isInvertible (c : k) :
    KltDP.SheafOfModules.IsInvertible (R := (projectiveProduct k).ringCatSheaf)
      (schemeKernelIdeal (verticalFiberMorphismAt c)) :=
  isInvertible_schemeKernelIdeal_transport (horizontalFiberMorphism c) productSwapIso
    (verticalFiberMorphismAt c) (Iso.refl _) (vertical_swap_square c)
    (FrobeniusMultiCentreIsoOpenClasses.horizontalFiberKernel_isInvertible c)

/-- The kernel line of the vertical fibre `x = c`. -/
def verticalFiberLine (c : k) : InvertibleSheaf (projectiveProduct k) :=
  ⟨schemeKernelIdeal (verticalFiberMorphismAt c), verticalFiberKernel_isInvertible c⟩

/-- **`−[I(x = c)] = a`**: the class of every vertical fibre is the accepted first fibre class. -/
theorem verticalFiberClass_eq_firstFiberClass (c : k) :
    -Additive.ofMul (verticalFiberLine (k := k) c).toPic = firstFiberClass := by
  let P := schemePicardPullbackHom (productSwapIso (k := k)).inv
  have h := kernelLine_toPic_transport (horizontalFiberMorphism c) productSwapIso
    (verticalFiberMorphismAt c) (Iso.refl _) (vertical_swap_square c)
    (FrobeniusMultiCentreIsoOpenClasses.horizontalFiberKernel_isInvertible c)
    (verticalFiberKernel_isInvertible c)
  calc -Additive.ofMul (verticalFiberLine (k := k) c).toPic
      = -Additive.ofMul (P (FrobeniusMultiCentreIsoOpenClasses.horizontalFiberLine c).toPic) :=
        congrArg (fun x => -Additive.ofMul x) h
    _ = P.toAdditive
          (-Additive.ofMul (FrobeniusMultiCentreIsoOpenClasses.horizontalFiberLine c).toPic) :=
        (map_neg P.toAdditive
          (Additive.ofMul (FrobeniusMultiCentreIsoOpenClasses.horizontalFiberLine c).toPic)).symm
    _ = P.toAdditive secondFiberClass := by rw [horizontalFiberClass_eq_secondFiberClass]
    _ = P.toAdditive (cartierPicardHom (projectiveProduct k) (rulingInfinityDivisor 1)) := by
        rw [secondFiberClass_eq_ruling]
    _ = cartierPicardHom (projectiveProduct k) (rulingInfinityDivisor 0) :=
        congrArg Additive.ofMul (swap_inv_rulingPicard (k := k))
    _ = firstFiberClass := firstFiberClass_eq_ruling.symm

/-! ## Consequences on `S_{p,n}` -/

section MultiCentre

open FrobeniusContactTowerSelectedPoint FrobeniusMultiCentreSurface FrobeniusMultiCentreGraphNewest
  FrobeniusMultiCentreCurveKernels FrobeniusMultiCentreIsoOpenClasses FrobeniusTowerTransportClasses

theorem translatedHorizontalIdealLine_toPic (p : ℕ) (a : k) :
    (translatedHorizontalIdealLine p a).toPic = (graphIdealLine (k := k) 0).toPic := by
  have h1 : translatedHorizontalIdealLine p a = horizontalFiberLine (1 + a ^ p) := rfl
  have h2 := horizontalFiberClass_eq_secondFiberClass (k := k) (1 + a ^ p)
  unfold secondFiberClass at h2
  rw [h1]
  exact Additive.ofMul.injective (neg_injective h2)

theorem translatedVerticalIdealLine_toPic (p : ℕ) (a : k) :
    (translatedVerticalIdealLine p a).toPic = (verticalFiberIdealLine (k := k)).toPic := by
  have h1 : translatedVerticalIdealLine p a = verticalFiberLine (1 + a) := rfl
  have h2 := verticalFiberClass_eq_firstFiberClass (k := k) (1 + a)
  unfold firstFiberClass at h2
  rw [h1]
  exact Additive.ofMul.injective (neg_injective h2)

variable (q n : ℕ) (a : Fin n → k) (i : Fin n)

/-- **The pulled-back translated fibre class `b_i` is the accepted `multiSecondFiberClass`.** -/
theorem multiTranslatedSecondFiberClass_eq :
    multiTranslatedSecondFiberClass q n a i = multiSecondFiberClass (q + 1) n a := by
  unfold multiTranslatedSecondFiberClass multiSecondFiberClass
  rw [← schemePicardPullbackHom_toPic, ← schemePicardPullbackHom_toPic,
    translatedHorizontalIdealLine_toPic]

/-- **The pulled-back translated fibre class `a_i` is the accepted `multiFirstFiberClass`.** -/
theorem multiTranslatedFirstFiberClass_eq :
    multiTranslatedFirstFiberClass q n a i = multiFirstFiberClass (q + 1) n a := by
  unfold multiTranslatedFirstFiberClass multiFirstFiberClass
  rw [← schemePicardPullbackHom_toPic, ← schemePicardPullbackHom_toPic,
    translatedVerticalIdealLine_toPic]

/-- **The graph row of the class table on the cluster open, with the accepted classes of `S_{p,n}`:**
`−[B] = (q+1)·a + b − Σ_j E_{ij}` restricted to `isoPreimage q n a i`. -/
theorem clusterGraphClass_accepted [Fact (q + 1).Prime] [CharP k (q + 1)] :
    -Additive.ofMul (clusterGraphKernelLine q n a i).toPic =
      (q + 1) • (schemePicardPullbackHom (isoPreimage q n a i).ι).toAdditive
          (multiFirstFiberClass (q + 1) n a) +
        (schemePicardPullbackHom (isoPreimage q n a i).ι).toAdditive
          (multiSecondFiberClass (q + 1) n a) -
        ∑ j : Fin (q + 1), (schemePicardPullbackHom (isoPreimage q n a i).ι).toAdditive
          (exceptionalClass (q + 1) n a i j) := by
  rw [← multiTranslatedFirstFiberClass_eq q n a i, ← multiTranslatedSecondFiberClass_eq q n a i]
  exact (clusterClassTable_own q n a i).1

/-- **On the isomorphism open `U₀` the class of `F_i` is the restriction of `multiSecondFiberClass`.** -/
theorem isoOpenFiberKernelLine_toPic_accepted :
    -Additive.ofMul (isoOpenFiberKernelLine q n a i).toPic =
      (schemePicardPullbackHom (blowdownIsoOpen q n a).ι).toAdditive
        (multiSecondFiberClass (q + 1) n a) := by
  rw [isoOpenFiberKernelLine_toPic, horizontalFiberClass_eq_secondFiberClass, blowdownMap_eq]
  unfold multiSecondFiberClass secondFiberClass
  rw [map_neg, map_neg, ← schemePicardPullbackHom_toPic, schemePicardPullbackHom_comp]
  rfl

end MultiCentre

end KltDP.Examples.ProjectiveProductFiberClassInvariance

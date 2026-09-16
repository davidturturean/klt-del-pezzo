import KltDP.Examples.FrobeniusTowerPrincipalFiber
import KltDP.Examples.FrobeniusExceptionalSuccessorChart

/-!
# The second Rees chart of the last blowup in the tower's function field

A generic *chart transport* lemma (`transport_eq`) abstracts the argument of `pulledBack_eq`: for a morphism
`f : Y ⟶ X` of integral schemes that is an isomorphism over a nonempty open `P`, the function fields are
identified (`transportIso`), and for open immersions `c : plane k ⟶ Y`, `d : plane k ⟶ X` with
`c ≫ f = Spec.map φ ≫ d`, the rational function of `φ a` on `c` is the transport of the rational function of
`a` on `d`.

Applied to the one-step blowdown `(A.stage n).nextProjection` over its puncture with the two Rees charts of
the last blowup — the selected chart `(A.stage (n+1)).chart` (blowdown `chartSubstitution : u ↦ u, v ↦ u·v`)
and the second chart `secondChart A n`, entering through its accepted polynomial model
`vChartPolynomialEquiv` (blowdown `secondSubstitution : u ↦ u·v, v ↦ u`) — this gives the overlap
relations in `(A.stage (n+1)).carrier.functionField`:

`u_sel = u₂ · v₂`, `u_sel · v_sel = u₂`, `v_sel · v₂ = 1`

(`selected_u_eq`, `selected_uv_eq`, `selected_v_mul_second_v`), i.e. BRIEF9 step 2's unit ratios on
`W_0 ⊓ W_1` as identities of rational functions on the whole tower.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusTowerSecondChart

open KltDP.Geometry KltDP.Geometry.AffineBlowup KltDP.Geometry.OpenImmersionRational
  FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusBlowupSmooth
  FrobeniusExceptionalCharts FrobeniusExceptionalSuccessorChart FrobeniusGlobalBlowupStages
  FrobeniusStageComplement FrobeniusStageComplement.PlaneChartedScheme FrobeniusFiberCartierCharts
  FrobeniusTowerFunctionField FrobeniusTowerFunctionField.PlaneChartedScheme

variable {k : Type u} [Field k]

/-! ## Generic chart transport -/

section transport

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X) (P : X.Opens)
  [Nonempty P.toScheme] [IsIso (f ∣_ P)]

instance target_isIntegral : IsIntegral P.toScheme := isIntegral_of_isOpenImmersion P.ι

/-- The isomorphism over the open. -/
def complementIso : (f ⁻¹ᵁ P).toScheme ≅ P.toScheme := asIso (f ∣_ P)

omit [IsIntegral X] [IsIntegral Y] [Nonempty P.toScheme] in
theorem complementIso_hom : (complementIso f P).hom = f ∣_ P := rfl

instance source_nonempty : Nonempty (f ⁻¹ᵁ P).toScheme :=
  ⟨(complementIso f P).inv.base (Classical.choice inferInstance)⟩

instance source_nonempty' : Nonempty (f ⁻¹ᵁ P) := ⟨Classical.choice (source_nonempty f P)⟩

instance source_isIntegral : IsIntegral (f ⁻¹ᵁ P).toScheme :=
  isIntegral_of_isOpenImmersion (f ⁻¹ᵁ P).ι

/-- The function-field identification along a morphism that is an isomorphism over a nonempty open. -/
def transportIso : Y.functionField ≅ X.functionField :=
  functionFieldIso (f ⁻¹ᵁ P).ι ≪≫ (functionFieldIso (complementIso f P).hom).symm ≪≫
    (functionFieldIso P.ι).symm

/-- For any open `V` of the plane on which `V.ι ≫ Spec.map φ` is an open immersion, the generic-stalk map
acts on rational functions of polynomials by `φ`. -/
theorem germ_transport (φ : planeRing k →+* planeRing k) (V : (plane k).Opens) [Nonempty V.toScheme]
    [IsIntegral V.toScheme] [IsOpenImmersion (V.ι ≫ Spec.map (CommRingCat.ofHom φ))]
    (a : planeRing k) :
    (functionFieldIso (V.ι ≫ Spec.map (CommRingCat.ofHom φ))).hom (planeGerm a) =
      (functionFieldIso V.ι).hom (planeGerm (φ a)) := by
  letI : Nonempty ((V.ι ≫ Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ (⊤ : (plane k).Opens)) :=
    preimage_nonempty _ ⊤
  letI : Nonempty (V.ι ⁻¹ᵁ (⊤ : (plane k).Opens)) := preimage_nonempty V.ι ⊤
  rw [planeGerm_apply, planeGerm_apply, functionFieldIso_germ, functionFieldIso_germ]
  change V.toScheme.germToFunctionField ⊤
      ((V.ι ≫ Spec.map (CommRingCat.ofHom φ)).appTop (planeSectionHom a)) =
    V.toScheme.germToFunctionField ⊤ (V.ι.appTop (planeSectionHom (φ a)))
  congr 1
  rw [Scheme.comp_appTop]
  change V.ι.appTop ((Spec.map (CommRingCat.ofHom φ)).appTop (planeSectionHom a)) = _
  congr 1
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)) a).symm

variable (c : plane k ⟶ Y) [IsOpenImmersion c]

/-- The part of the chart `c` over the open. -/
abbrev chartPart : (plane k).Opens := c ⁻¹ᵁ (f ⁻¹ᵁ P)

instance chartPart_nonempty : Nonempty (chartPart f P c) := preimage_nonempty c (f ⁻¹ᵁ P)

instance chartPart_nonempty' : Nonempty (chartPart f P c).toScheme :=
  ⟨Classical.choice (chartPart_nonempty f P c)⟩

instance chartPart_isIntegral : IsIntegral (chartPart f P c).toScheme :=
  isIntegral_of_isOpenImmersion (chartPart f P c).ι

/-- The chart restricted over the open. -/
abbrev chartPartToSource : (chartPart f P c).toScheme ⟶ (f ⁻¹ᵁ P).toScheme := c ∣_ (f ⁻¹ᵁ P)

omit [IsIntegral X] [IsIntegral Y] [Nonempty P.toScheme] [IsIso (f ∣_ P)] [IsOpenImmersion c] in
theorem chartPartToSource_ι :
    chartPartToSource f P c ≫ (f ⁻¹ᵁ P).ι = (chartPart f P c).ι ≫ c :=
  morphismRestrict_ι _ _

variable (d : plane k ⟶ X) [IsOpenImmersion d] (φ : planeRing k →+* planeRing k)

/-- The chart blowdown on the part over the open. -/
abbrev chartPartMap : (chartPart f P c).toScheme ⟶ plane k :=
  (chartPart f P c).ι ≫ Spec.map (CommRingCat.ofHom φ)

omit [IsIntegral X] [IsIntegral Y] [Nonempty P.toScheme] [IsOpenImmersion c] [IsOpenImmersion d] in
theorem chartPartMap_d (hsq : c ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ d) :
    chartPartMap f P c φ ≫ d = (chartPartToSource f P c ≫ (complementIso f P).hom) ≫ P.ι := by
  rw [Category.assoc, ← hsq, ← Category.assoc, ← chartPartToSource_ι, Category.assoc,
    Category.assoc, complementIso_hom, morphismRestrict_ι]

omit [IsIntegral X] [IsIntegral Y] [Nonempty P.toScheme] in
theorem chartPartMap_isOpenImmersion (hsq : c ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ d) :
    IsOpenImmersion (chartPartMap f P c φ) := by
  haveI : IsOpenImmersion (chartPartMap f P c φ ≫ d) := by
    rw [chartPartMap_d f P c d φ hsq]
    infer_instance
  exact IsOpenImmersion.of_comp _ d

/-- **Chart transport**: the rational function of `φ a` on the chart `c` of `Y` is the transport of the
rational function of `a` on the chart `d` of `X`. -/
theorem transport_eq (hsq : c ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ d) (a : planeRing k) :
    (functionFieldIso c).inv (planeGerm (φ a)) =
      (transportIso f P).inv ((functionFieldIso d).inv (planeGerm a)) := by
  haveI := chartPartMap_isOpenImmersion f P c d φ hsq
  have key : ((functionFieldIso d).inv ≫ (transportIso f P).inv) ≫
      ((functionFieldIso (f ⁻¹ᵁ P).ι).hom ≫ (functionFieldIso (chartPartToSource f P c)).hom) =
        (functionFieldIso (chartPartMap f P c φ)).hom := by
    simp only [transportIso, Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← functionFieldIso_comp_hom (complementIso f P).hom (chartPartToSource f P c),
      ← functionFieldIso_comp_hom P.ι (chartPartToSource f P c ≫ (complementIso f P).hom),
      ← functionFieldIso_congr (chartPartMap_d f P c d φ hsq), functionFieldIso_comp_hom,
      Iso.inv_hom_id_assoc]
  have key' : (functionFieldIso c).inv ≫
      ((functionFieldIso (f ⁻¹ᵁ P).ι).hom ≫ (functionFieldIso (chartPartToSource f P c)).hom) =
        (functionFieldIso (chartPart f P c).ι).hom := by
    rw [← functionFieldIso_comp_hom, functionFieldIso_congr (chartPartToSource_ι f P c),
      functionFieldIso_comp_hom, Iso.inv_hom_id_assoc]
  apply (functionFieldIso (f ⁻¹ᵁ P).ι ≪≫
    functionFieldIso (chartPartToSource f P c)).commRingCatIsoToRingEquiv.injective
  have e1 : (functionFieldIso (f ⁻¹ᵁ P).ι ≪≫
      functionFieldIso (chartPartToSource f P c)).commRingCatIsoToRingEquiv
        ((functionFieldIso c).inv (planeGerm (φ a))) =
      ((functionFieldIso c).inv ≫ ((functionFieldIso (f ⁻¹ᵁ P).ι).hom ≫
        (functionFieldIso (chartPartToSource f P c)).hom)) (planeGerm (φ a)) := rfl
  have e2 : (functionFieldIso (f ⁻¹ᵁ P).ι ≪≫
      functionFieldIso (chartPartToSource f P c)).commRingCatIsoToRingEquiv
        ((transportIso f P).inv ((functionFieldIso d).inv (planeGerm a))) =
      (((functionFieldIso d).inv ≫ (transportIso f P).inv) ≫
        ((functionFieldIso (f ⁻¹ᵁ P).ι).hom ≫
          (functionFieldIso (chartPartToSource f P c)).hom)) (planeGerm a) := rfl
  rw [e1, e2, key, key']
  exact (germ_transport φ (chartPart f P c) a).symm

end transport

/-! ## The second Rees chart of the last blowup -/

/-- The polynomial model of the second Rees chart, as a scheme isomorphism. -/
def vChartIso : plane k ≅ Spec (CommRingCat.of (reesVChartRing k)) :=
  Scheme.Spec.mapIso (vChartPolynomialEquiv (k := k)).toCommRingCatIso.op

/-- The second-chart blowdown in the polynomial model: `u ↦ u·v`, `v ↦ u`. -/
def secondSubstitution : planeRing k →+* planeRing k :=
  (vChartPolynomialEquiv (k := k)).toRingHom.comp (chartBaseMap centerIdeal centerV)

theorem secondSubstitution_v : secondSubstitution (vCoord (k := k)) = uCoord := by
  change (vChartPolynomialEquiv (k := k)) (chartBaseMap centerIdeal centerV vCoord) = uCoord
  exact vChart_selected_equation

theorem secondSubstitution_u : secondSubstitution (uCoord (k := k)) = uCoord * vCoord := by
  have h : chartBaseMap centerIdeal centerV vCoord * chartFraction centerIdeal centerV centerU =
      chartBaseMap centerIdeal centerV (uCoord (k := k)) :=
    chartBaseMap_mul_chartFraction (centerIdeal (k := k)) centerV centerU
  change (vChartPolynomialEquiv (k := k)) (chartBaseMap centerIdeal centerV uCoord) = _
  rw [← h, map_mul]
  exact congrArg₂ (· * ·) vChart_selected_equation vChartPolynomialEquiv_coordinate

namespace PlaneChartedScheme

variable (A : PlaneChartedScheme k) [IsIntegral A.carrier] (n : ℕ)

/-- The second Rees chart of the last blowup, as an open immersion of its polynomial model into the
stage-`n+1` tower. -/
def secondChart : plane k ⟶ (A.stage (n + 1)).carrier :=
  vChartIso.hom ≫ chartι centerIdeal centerV ≫ (A.stage n).nextAffineBlowup

instance secondChart_isOpenImmersion : IsOpenImmersion (secondChart A n) := by
  unfold secondChart
  infer_instance

omit [IsIntegral A.carrier] in
theorem secondChart_projection :
    secondChart A n ≫ (A.stage n).nextProjection =
      Spec.map (CommRingCat.ofHom secondSubstitution) ≫ (A.stage n).chart := by
  have h : chartι centerIdeal centerV ≫ toSpec centerIdeal ≫ (A.stage n).chart =
      Spec.map (CommRingCat.ofHom (chartBaseMap (centerIdeal (k := k)) centerV)) ≫
        (A.stage n).chart := by
    rw [← Category.assoc, chartι_toSpec]
    rfl
  rw [secondChart, Category.assoc, Category.assoc, (A.stage n).nextAffineBlowup_projection, h,
    ← Category.assoc]
  change (Spec.map (CommRingCat.ofHom (vChartPolynomialEquiv (k := k)).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (chartBaseMap centerIdeal centerV))) ≫ (A.stage n).chart = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

omit [IsIntegral A.carrier] in
theorem selectedChart_projection :
    (A.stage (n + 1)).chart ≫ (A.stage n).nextProjection =
      Spec.map (CommRingCat.ofHom chartSubstitution) ≫ (A.stage n).chart := by
  rw [← coordinateBlowdown_eq]
  exact (A.stage n).nextChart_projection

instance step_restrict_isIso : IsIso ((A.stage n).nextProjection ∣_ initialPuncture (A.stage n)) :=
  nextProjection_restrict_isIso (A.stage n)

instance nextScheme_isIntegral : IsIntegral (A.stage n).nextScheme := instStageIsIntegral A (n + 1)

/-- The one-step function-field identification. -/
def stepIso : (A.stage (n + 1)).carrier.functionField ≅ (A.stage n).carrier.functionField :=
  transportIso (A.stage n).nextProjection (initialPuncture (A.stage n))

/-- Polynomials of the second chart as rational functions on the stage-`n+1` tower. -/
def secondCoordinate : planeRing k →+* (A.stage (n + 1)).carrier.functionField :=
  (functionFieldIso (secondChart A n)).inv.hom.comp planeGerm

theorem chartCoordinate_succ (a : planeRing k) :
    chartCoordinate A (n + 1) (chartSubstitution a) = (stepIso A n).inv (chartCoordinate A n a) :=
  transport_eq (A.stage n).nextProjection (initialPuncture (A.stage n)) (A.stage (n + 1)).chart
    (A.stage n).chart chartSubstitution (selectedChart_projection A n) a

theorem secondCoordinate_eq (a : planeRing k) :
    secondCoordinate A n (secondSubstitution a) = (stepIso A n).inv (chartCoordinate A n a) :=
  transport_eq (A.stage n).nextProjection (initialPuncture (A.stage n)) (secondChart A n)
    (A.stage n).chart secondSubstitution (secondChart_projection A n) a

/-- Overlap relation: `u` of the selected chart is `u · v` of the second chart. -/
theorem selected_u_eq :
    chartCoordinate A (n + 1) uCoord = secondCoordinate A n uCoord * secondCoordinate A n vCoord := by
  have h1 := chartCoordinate_succ A n uCoord
  rw [chartSubstitution_u] at h1
  have h2 := secondCoordinate_eq A n uCoord
  rw [secondSubstitution_u, map_mul] at h2
  rw [h1, h2]

/-- Overlap relation: `u · v` of the selected chart is `u` of the second chart. -/
theorem selected_uv_eq :
    chartCoordinate A (n + 1) uCoord * chartCoordinate A (n + 1) vCoord =
      secondCoordinate A n uCoord := by
  have h1 := chartCoordinate_succ A n vCoord
  rw [chartSubstitution_v, map_mul] at h1
  have h2 := secondCoordinate_eq A n vCoord
  rw [secondSubstitution_v] at h2
  rw [h1, h2]

theorem secondCoordinate_injective : Function.Injective (secondCoordinate A n) := fun _ _ hab =>
  FrobeniusTowerPrincipalFiber.planeGerm_injective
    ((functionFieldIso (secondChart A n)).symm.commRingCatIsoToRingEquiv.injective hab)

theorem secondCoordinate_ne_zero {a : planeRing k} (ha : a ≠ 0) : secondCoordinate A n a ≠ 0 :=
  fun h => ha (secondCoordinate_injective A n (h.trans (map_zero _).symm))

/-- Overlap relation: `v` of the selected chart is the inverse of `v` (the ratio `u/v`) of the second
chart. -/
theorem selected_v_mul_second_v :
    chartCoordinate A (n + 1) vCoord * secondCoordinate A n vCoord = 1 := by
  have hsu : secondCoordinate A n uCoord ≠ 0 :=
    secondCoordinate_ne_zero A n FrobeniusFiberCartierCharts.uCoord_ne_zero
  have h := selected_uv_eq A n
  rw [selected_u_eq] at h
  apply mul_left_cancel₀ hsu
  rw [mul_one]
  calc secondCoordinate A n uCoord * (chartCoordinate A (n + 1) vCoord * secondCoordinate A n vCoord)
      = secondCoordinate A n uCoord * secondCoordinate A n vCoord *
          chartCoordinate A (n + 1) vCoord := by ring
    _ = secondCoordinate A n uCoord := h

end PlaneChartedScheme

end KltDP.Examples.FrobeniusTowerSecondChart

namespace KltDP.Examples

open FrobeniusGlobalBlowupStages FrobeniusTowerFunctionField.PlaneChartedScheme
  FrobeniusTowerSecondChart.PlaneChartedScheme FrobeniusBlowupContact

/-- Bundle: the overlap relations of the two Rees charts of the last blowup in the tower's function
field. -/
theorem f29_tower_second_chart {k : Type u} [Field k] (A : PlaneChartedScheme k)
    [IsIntegral A.carrier] (n : ℕ) :
    chartCoordinate A (n + 1) uCoord = secondCoordinate A n uCoord * secondCoordinate A n vCoord ∧
    chartCoordinate A (n + 1) uCoord * chartCoordinate A (n + 1) vCoord =
      secondCoordinate A n uCoord ∧
    chartCoordinate A (n + 1) vCoord * secondCoordinate A n vCoord = 1 :=
  ⟨selected_u_eq A n, selected_uv_eq A n, selected_v_mul_second_v A n⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_tower_second_chart_universe_check {k : Type u} [Field k] (A : PlaneChartedScheme k)
    [IsIntegral A.carrier] : True := by
  have _ := f29_tower_second_chart.{u} A 0
  trivial

end KltDP.Examples

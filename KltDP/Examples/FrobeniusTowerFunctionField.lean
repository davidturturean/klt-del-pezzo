import KltDP.Examples.FrobeniusStageComplement
import KltDP.Examples.FrobeniusFiberCartierCharts
import KltDP.Geometry.OpenImmersionFunctionFieldFunctorial
import KltDP.Geometry.PointBlowupIntegral

/-!
# The function field of the blowup tower

For an integral charted plane `A`, every stage `(A.stage n).carrier` of the accepted blowup tower is
integral (`stage_isIntegral`: each step is the accepted gluing of an integral affine blowup with the
puncture). The blowdown `A.toInitial n` is an isomorphism over the puncture of the original centre
(accepted `toInitial_restrict_isIso`), which identifies the function fields
(`towerFunctionFieldIso : (A.stage n).carrier.functionField ≅ A.carrier.functionField`).

The selected polynomial chart `(A.stage n).chart` identifies the tower's function field with that of the
plane (`chartFunctionFieldIso`); a polynomial `a` of the plane gives the rational function
`chartCoordinate A n a` on the tower, and a polynomial of the *initial* chart gives its pull-back
`pulledBack A n a`. The compatibility `pulledBack_eq : pulledBack A n a = chartCoordinate A n
(stageSubstitution n a)` is proved on the open `chartPuncture` of the chart lying over the puncture,
where the chart projection `stageProjection n` is an open immersion (cancelling `A.chart` in the
accepted `stage_chart_toInitial`), by the accepted functoriality of the generic-stalk maps and the
naturality of `ΓSpecIso`. In particular the pulled-back fibre equation is
`pulledBack_vCoord : pulledBack A n v = (chartCoordinate A n u) ^ n * chartCoordinate A n v`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusTowerFunctionField

open KltDP.Geometry KltDP.Geometry.OpenImmersionRational FrobeniusBlowupContact
  FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages FrobeniusStageComplement
  FrobeniusStageComplement.PlaneChartedScheme FrobeniusFiberCartierCharts

variable {k : Type u} [Field k]

/-- The centre ideal `(u, v)` is nonzero. -/
theorem centerIdeal_ne_bot : (centerIdeal (k := k)) ≠ ⊥ := by
  intro h
  have hu : uCoord (k := k) ∈ centerIdeal := Ideal.subset_span (Set.mem_insert _ _)
  rw [h, Ideal.mem_bot] at hu
  exact FrobeniusBlowupContact.uCoord_ne_zero hu

/-- The rational function of a polynomial on the plane chart. -/
def planeGerm : planeRing k →+* (plane k).functionField :=
  ((plane k).germToFunctionField ⊤).hom.comp planeSectionHom

theorem planeGerm_apply (a : planeRing k) :
    planeGerm a = (plane k).germToFunctionField ⊤ (planeSectionHom a) := rfl

/-- Generic-stalk maps of equal open immersions agree. -/
theorem functionFieldIso_congr {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] {f g : Y ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (hfg : f = g) :
    (functionFieldIso f).hom = (functionFieldIso g).hom := by
  subst hfg
  rfl

namespace PlaneChartedScheme

variable (A : PlaneChartedScheme k) [IsIntegral A.carrier]

/-- Every stage of the tower is integral. -/
theorem stage_isIntegral : ∀ n : ℕ, IsIntegral (A.stage n).carrier
  | 0 => (inferInstance : IsIntegral A.carrier)
  | n + 1 => by
      letI := stage_isIntegral n
      letI : (originPoint (k := k)).asIdeal.IsMaximal :=
        FrobeniusBlowupChartIteration.centerIdeal_isMaximal
      exact PointBlowupGluing.scheme_isIntegral (A.stage n).chart (originPoint (k := k))
        (A.stage n).center_closed centerIdeal_ne_bot

instance instStageIsIntegral (n : ℕ) : IsIntegral (A.stage n).carrier := stage_isIntegral A n

instance initialPuncture_nonempty : Nonempty (initialPuncture A).toScheme := by
  letI : (originPoint (k := k)).asIdeal.IsMaximal :=
    FrobeniusBlowupChartIteration.centerIdeal_isMaximal
  exact PointBlowupGluing.puncture_nonempty A.chart (originPoint (k := k)) A.center_closed
    centerIdeal_ne_bot

instance initialPuncture_isIntegral : IsIntegral (initialPuncture A).toScheme :=
  isIntegral_of_isOpenImmersion (initialPuncture A).ι

instance stagePuncture_nonempty (n : ℕ) : Nonempty (stagePuncture A n).toScheme :=
  ⟨(stageComplementIso A n).inv.base (Classical.choice (initialPuncture_nonempty A))⟩

instance stagePuncture_nonempty' (n : ℕ) : Nonempty (stagePuncture A n) :=
  ⟨Classical.choice (stagePuncture_nonempty A n)⟩

instance stagePuncture_isIntegral (n : ℕ) : IsIntegral (stagePuncture A n).toScheme :=
  isIntegral_of_isOpenImmersion (stagePuncture A n).ι

/-- The function field of the stage-`n` tower, identified with that of the base through the dense
open over which the blowdown is an isomorphism. -/
def towerFunctionFieldIso (n : ℕ) :
    (A.stage n).carrier.functionField ≅ A.carrier.functionField :=
  functionFieldIso (stagePuncture A n).ι ≪≫
    (functionFieldIso (stageComplementIso A n).hom).symm ≪≫
      (functionFieldIso (initialPuncture A).ι).symm

/-- The function field of the stage-`n` tower through its selected polynomial chart. -/
def chartFunctionFieldIso (n : ℕ) : (A.stage n).carrier.functionField ≅ (plane k).functionField :=
  functionFieldIso (A.stage n).chart

/-- Polynomials of the selected chart of stage `n`, as rational functions on the whole tower. -/
def chartCoordinate (n : ℕ) : planeRing k →+* (A.stage n).carrier.functionField :=
  (chartFunctionFieldIso A n).inv.hom.comp planeGerm

/-- Polynomials of the initial chart, pulled back to rational functions on the stage-`n` tower. -/
def pulledBack (n : ℕ) : planeRing k →+* (A.stage n).carrier.functionField :=
  ((towerFunctionFieldIso A n).inv.hom.comp (functionFieldIso A.chart).inv.hom).comp planeGerm

section compatibility

variable (n : ℕ)

/-- The part of the selected chart of stage `n` lying over the puncture. -/
abbrev chartPuncture : (plane k).Opens := (A.stage n).chart ⁻¹ᵁ stagePuncture A n

instance chartPuncture_nonempty : Nonempty (chartPuncture A n) :=
  preimage_nonempty (A.stage n).chart (stagePuncture A n)

instance chartPuncture_nonempty' : Nonempty (chartPuncture A n).toScheme :=
  ⟨Classical.choice (chartPuncture_nonempty A n)⟩

instance chartPuncture_isIntegral : IsIntegral (chartPuncture A n).toScheme :=
  isIntegral_of_isOpenImmersion (chartPuncture A n).ι

/-- The selected chart restricted over the puncture. -/
abbrev chartToPuncture : (chartPuncture A n).toScheme ⟶ (stagePuncture A n).toScheme :=
  (A.stage n).chart ∣_ stagePuncture A n

omit [IsIntegral A.carrier] in
theorem chartToPuncture_ι :
    chartToPuncture A n ≫ (stagePuncture A n).ι = (chartPuncture A n).ι ≫ (A.stage n).chart :=
  morphismRestrict_ι _ _

/-- The chart projection on the part over the puncture. -/
def chartPunctureMap : (chartPuncture A n).toScheme ⟶ plane k :=
  (chartPuncture A n).ι ≫ stageProjection n

omit [IsIntegral A.carrier] in
theorem chartPunctureMap_chart :
    chartPunctureMap A n ≫ A.chart =
      (chartToPuncture A n ≫ (stageComplementIso A n).hom) ≫ (initialPuncture A).ι := by
  rw [chartPunctureMap, Category.assoc, ← A.stage_chart_toInitial, ← Category.assoc,
    ← chartToPuncture_ι, Category.assoc, Category.assoc, stageComplementIso_hom_ι]

instance chartPunctureMap_isOpenImmersion : IsOpenImmersion (chartPunctureMap A n) := by
  haveI : IsOpenImmersion (chartPunctureMap A n ≫ A.chart) := by
    rw [chartPunctureMap_chart]
    infer_instance
  exact IsOpenImmersion.of_comp _ A.chart

/-- On the part of the chart over the puncture, the chart projection acts on the rational functions
of polynomials by the stage substitution `v ↦ u^n v`. -/
theorem germ_compat (a : planeRing k) :
    (functionFieldIso (chartPunctureMap A n)).hom (planeGerm a) =
      (functionFieldIso (chartPuncture A n).ι).hom (planeGerm (stageSubstitution n a)) := by
  letI : Nonempty (chartPunctureMap A n ⁻¹ᵁ (⊤ : (plane k).Opens)) :=
    preimage_nonempty (chartPunctureMap A n) ⊤
  letI : Nonempty ((chartPuncture A n).ι ⁻¹ᵁ (⊤ : (plane k).Opens)) :=
    preimage_nonempty (chartPuncture A n).ι ⊤
  rw [planeGerm_apply, planeGerm_apply, functionFieldIso_germ, functionFieldIso_germ]
  change (chartPuncture A n).toScheme.germToFunctionField ⊤
      ((chartPunctureMap A n).appTop (planeSectionHom a)) =
    (chartPuncture A n).toScheme.germToFunctionField ⊤
      ((chartPuncture A n).ι.appTop (planeSectionHom (stageSubstitution n a)))
  congr 1
  rw [chartPunctureMap, Scheme.comp_appTop, stageProjection_eq]
  change (chartPuncture A n).ι.appTop
      ((Spec.map (CommRingCat.ofHom (stageSubstitution n))).appTop (planeSectionHom a)) = _
  congr 1
  exact (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (stageSubstitution (k := k) n))) a).symm

/-- The pulled-back rational function of a polynomial of the initial chart is the rational function
of its stage substitution on the selected chart. -/
theorem pulledBack_eq (a : planeRing k) :
    pulledBack A n a = chartCoordinate A n (stageSubstitution n a) := by
  -- the two generic-stalk isomorphisms down to the part of the chart over the puncture
  have key : ((functionFieldIso A.chart).inv ≫ (towerFunctionFieldIso A n).inv) ≫
      ((functionFieldIso (stagePuncture A n).ι).hom ≫ (functionFieldIso (chartToPuncture A n)).hom) =
        (functionFieldIso (chartPunctureMap A n)).hom := by
    simp only [towerFunctionFieldIso, Iso.trans_inv, Iso.symm_inv, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [← functionFieldIso_comp_hom (stageComplementIso A n).hom (chartToPuncture A n),
      ← functionFieldIso_comp_hom (initialPuncture A).ι
        (chartToPuncture A n ≫ (stageComplementIso A n).hom),
      ← functionFieldIso_congr (chartPunctureMap_chart A n), functionFieldIso_comp_hom,
      Iso.inv_hom_id_assoc]
  have key' : (chartFunctionFieldIso A n).inv ≫
      ((functionFieldIso (stagePuncture A n).ι).hom ≫ (functionFieldIso (chartToPuncture A n)).hom) =
        (functionFieldIso (chartPuncture A n).ι).hom := by
    rw [← functionFieldIso_comp_hom, functionFieldIso_congr (chartToPuncture_ι A n),
      functionFieldIso_comp_hom, chartFunctionFieldIso, Iso.inv_hom_id_assoc]
  apply (functionFieldIso (stagePuncture A n).ι ≪≫
    functionFieldIso (chartToPuncture A n)).commRingCatIsoToRingEquiv.injective
  have e1 : (functionFieldIso (stagePuncture A n).ι ≪≫
      functionFieldIso (chartToPuncture A n)).commRingCatIsoToRingEquiv (pulledBack A n a) =
        (((functionFieldIso A.chart).inv ≫ (towerFunctionFieldIso A n).inv) ≫
          ((functionFieldIso (stagePuncture A n).ι).hom ≫
            (functionFieldIso (chartToPuncture A n)).hom)) (planeGerm a) := rfl
  have e2 : (functionFieldIso (stagePuncture A n).ι ≪≫
      functionFieldIso (chartToPuncture A n)).commRingCatIsoToRingEquiv
        (chartCoordinate A n (stageSubstitution n a)) =
        ((chartFunctionFieldIso A n).inv ≫
          ((functionFieldIso (stagePuncture A n).ι).hom ≫
            (functionFieldIso (chartToPuncture A n)).hom)) (planeGerm (stageSubstitution n a)) := rfl
  rw [e1, e2, key, key']
  exact germ_compat A n a

/-- The pulled-back fibre equation `v` of the initial chart is `u^n · v` on the stage-`n` tower. -/
theorem pulledBack_vCoord :
    pulledBack A n vCoord = chartCoordinate A n uCoord ^ n * chartCoordinate A n vCoord := by
  rw [pulledBack_eq, stageSubstitution_v, map_mul, map_pow]

theorem pulledBack_uCoord : pulledBack A n uCoord = chartCoordinate A n uCoord := by
  rw [pulledBack_eq, stageSubstitution_u]

end compatibility

end PlaneChartedScheme

end KltDP.Examples.FrobeniusTowerFunctionField

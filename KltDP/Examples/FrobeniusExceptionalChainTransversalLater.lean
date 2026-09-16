import KltDP.Examples.FrobeniusExceptionalChainTransversal
import KltDP.Examples.FrobeniusStageComplement
import KltDP.Geometry.Surface

/-!
# The older adjacent pairs cross transversally: `ChainTransversal` for every `q`

BRIEF21, task 1 (lane F). For a charted plane `A`, the older pair `C_j, C_{j+1}` (`j + 1 < q`) of the
exceptional chain of stage `q+1` meets at the point `crossingPointN`, the image of the accepted
`adjacentPoint (A.stage j)`, which lies over the birth-stage crossing `C_j ∩ P` of stage `j+2` in the
isomorphism locus of the projection `between`. The birth-stage second Rees chart is lifted to stage `q+1`
(`liftedChart`, through the complement inclusion of the blowup of stage `j+2` and the inverse of the
restricted projection `between ∣_ initialPuncture`, an isomorphism by the accepted
`toInitial_restrict_isIso`); on it the kernel ideals of `C_j` and `C_{j+1}` are `(u/v)` and `(v)`
(`old_ideal_lifted`, `newer_ideal_lifted`, by the generic transport `ker_ideal_map_eq_of_isPullback`
along the accepted pullback squares `finalOldMap_isPullback`; for `C_{j+1}` through the accepted
`wholePreviousLift`, quasi-compact because the punctured exceptional curve is Noetherian), and all other
components miss the chart (the older ones by `old_not_mem_secondOpen`, the later ones and `P` because they
project to the centre of stage `j+2`, which is not in the chart: `between_center`). Hence the vanishing
ideal of the locus on the chart is `(u/v · v)` (`chainIdeal_liftedOpen`), and BRIEF20's
`transversalCrossing_of_chart` gives the transversal crossing (`transversalCrossing_later`).

**Exports**: `chainTransversal A q : ChainTransversal q A (chainSinglePoints A q)` for every `q`, and the
unconditional `chainPicardEquivFin_unconditional : Pic(C_1 ∪ ⋯ ∪ C_q ∪ P) ≃* ℤ^{q+1}` (lane A1's
`chainPicardEquivFin` with both hypotheses discharged).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing

universe u

namespace KltDP.Examples.FrobeniusExceptionalChainTransversalLater

open KltDP.Geometry KltDP.Geometry.RationalTreePicard
open FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
  FrobeniusGlobalExceptionalSuccessor FrobeniusExceptionalChainPicard FrobeniusSecondChartCrossing
  FrobeniusExceptionalSuccessorChart FrobeniusBlowupChartIteration FrobeniusBlowupSmooth
  FrobeniusExceptionalChainTransversal FrobeniusStageComplement.PlaneChartedScheme

variable {k : Type u} [Field k]

local instance laterOriginPoint_isMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-! ## Generic lemmas -/

/-- Points over an open on which `f` restricts to an isomorphism are determined by their images. -/
theorem eq_of_restrict_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)]
    (y y' : X) (hy : f.base y ∈ V) (hy' : f.base y' ∈ V) (h : f.base y = f.base y') : y = y' := by
  let a : (f ⁻¹ᵁ V).toScheme := ⟨y, hy⟩
  let b : (f ⁻¹ᵁ V).toScheme := ⟨y', hy'⟩
  have ha : V.ι.base ((f ∣_ V).base a) = f.base y :=
    congrArg (fun g => g.base a) (morphismRestrict_ι f V)
  have hb : V.ι.base ((f ∣_ V).base b) = f.base y' :=
    congrArg (fun g => g.base b) (morphismRestrict_ι f V)
  have hab : (f ∣_ V).base a = (f ∣_ V).base b :=
    V.ι.isOpenEmbedding.injective (ha.trans (h.trans hb.symm))
  have hab' : a = b := (f ∣_ V).isOpenEmbedding.injective hab
  exact congrArg Subtype.val hab'

section Primality

variable {Γ : Type u} [CommRing Γ] (θ : Γ ≃+* reesVChartRing k)

theorem span_symm_vEquation_isPrime' : (Ideal.span {θ.symm vEquation}).IsPrime := by
  rw [show ({θ.symm vEquation} : Set Γ) = θ.symm '' {vEquation} from Set.image_singleton.symm,
    ← Ideal.map_span, Ideal.map_symm]
  haveI hp : (Ideal.span {vEquation (k := k)}).IsPrime := span_vEquation_isPrime
  exact Ideal.IsPrime.comap θ

theorem span_symm_oldRatio_isPrime' : (Ideal.span {θ.symm oldRatio}).IsPrime := by
  rw [show ({θ.symm oldRatio} : Set Γ) = θ.symm '' {oldRatio} from Set.image_singleton.symm,
    ← Ideal.map_span, Ideal.map_symm]
  haveI hp : (Ideal.span {oldRatio (k := k)}).IsPrime := span_oldRatio_isPrime
  exact Ideal.IsPrime.comap θ

theorem symm_oldRatio_not_mem' : θ.symm oldRatio ∉ Ideal.span {θ.symm vEquation} := by
  intro h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp h
  apply oldRatio_not_mem_span_vEquation (k := k)
  rw [Ideal.mem_span_singleton]
  refine ⟨θ c, ?_⟩
  have h' := congrArg θ hc
  rwa [RingEquiv.apply_symm_apply, map_mul, RingEquiv.apply_symm_apply] at h'

theorem span_symm_inf' :
    Ideal.span {θ.symm oldRatio} ⊓ Ideal.span {θ.symm vEquation} =
      Ideal.span {θ.symm (oldRatio * vEquation)} := by
  rw [span_singleton_inf_span_singleton_of_prime (span_symm_vEquation_isPrime' θ)
    (symm_oldRatio_not_mem' θ), map_mul]

end Primality

section ChartStalk

variable {Y : Scheme.{u}} (jc : Spec (CommRingCat.of (reesVChartRing k)) ⟶ Y) [IsOpenImmersion jc]

/-- The stalk at the origin of a chart with coordinates `reesVChartRing k`. -/
def chartStalkEquiv : Y.presheaf.stalk (jc.base secondOrigin) ≃+* originLocal (k := k) :=
  openImmersionStalkLocalizationEquiv jc secondOrigin

theorem chart_regularLocal : RegularLocal (Y.presheaf.stalk (jc.base secondOrigin)) :=
  regularLocal_of_ringEquiv (chartStalkEquiv jc).symm originLocal_regularLocal

theorem chart_ringKrullDim : ringKrullDim (Y.presheaf.stalk (jc.base secondOrigin)) = 2 :=
  (ringKrullDim_eq_of_ringEquiv (chartStalkEquiv jc)).trans ringKrullDim_originLocal

theorem chart_map_symm_maximalIdeal :
    Ideal.map (chartStalkEquiv jc).symm (maximalIdeal (originLocal (k := k))) =
      maximalIdeal (Y.presheaf.stalk (jc.base secondOrigin)) := by
  apply IsLocalRing.eq_maximalIdeal
  rw [← Ideal.comap_symm, RingEquiv.symm_symm]
  exact Ideal.comap_isMaximal_of_surjective (f := chartStalkEquiv jc) (chartStalkEquiv jc).surjective

/-- The germ of `u/v` at the chart origin. -/
def chartU : Y.presheaf.stalk (jc.base secondOrigin) :=
  (chartStalkEquiv jc).symm (algebraMap (reesVChartRing k) (originLocal (k := k)) oldRatio)

/-- The germ of `v` at the chart origin. -/
def chartV : Y.presheaf.stalk (jc.base secondOrigin) :=
  (chartStalkEquiv jc).symm (algebraMap (reesVChartRing k) (originLocal (k := k)) vEquation)

theorem span_chartU_chartV :
    Ideal.span {chartU jc, chartV jc} = maximalIdeal (Y.presheaf.stalk (jc.base secondOrigin)) := by
  rw [← chart_map_symm_maximalIdeal, ← span_eq_maximalIdeal_originLocal, Ideal.map_span,
    Set.image_insert_eq, Set.image_singleton]
  rfl

theorem chartU_eq_germ :
    chartU jc = Y.presheaf.germ (jc ''ᵁ ⊤) (jc.base secondOrigin) (mem_chart_image_top jc _)
      ((chartSectionsEquiv jc).symm oldRatio) :=
  openImmersionStalkLocalizationEquiv_symm_algebraMap jc secondOrigin oldRatio

theorem chartV_eq_germ :
    chartV jc = Y.presheaf.germ (jc ''ᵁ ⊤) (jc.base secondOrigin) (mem_chart_image_top jc _)
      ((chartSectionsEquiv jc).symm vEquation) :=
  openImmersionStalkLocalizationEquiv_symm_algebraMap jc secondOrigin vEquation

theorem chart_span_germs :
    Ideal.span {Y.presheaf.germ (jc ''ᵁ ⊤) (jc.base secondOrigin) (mem_chart_image_top jc _)
        ((chartSectionsEquiv jc).symm oldRatio),
      Y.presheaf.germ (jc ''ᵁ ⊤) (jc.base secondOrigin) (mem_chart_image_top jc _)
        ((chartSectionsEquiv jc).symm vEquation)} =
      maximalIdeal (Y.presheaf.stalk (jc.base secondOrigin)) := by
  rw [← chartU_eq_germ, ← chartV_eq_germ]
  exact span_chartU_chartV jc

theorem chart_mem_of_eq (y : Y) (hy : y = jc.base secondOrigin) : y ∈ jc ''ᵁ ⊤ := by
  subst hy
  exact mem_chart_image_top jc _

theorem chart_regularLocal_of_eq (y : Y) (hy : y = jc.base secondOrigin) :
    RegularLocal (Y.presheaf.stalk y) := by
  subst hy
  exact chart_regularLocal jc

theorem chart_ringKrullDim_of_eq (y : Y) (hy : y = jc.base secondOrigin) :
    ringKrullDim (Y.presheaf.stalk y) = 2 := by
  subst hy
  exact chart_ringKrullDim jc

theorem chart_span_germs_of_eq (y : Y) (hy : y = jc.base secondOrigin) :
    Ideal.span {Y.presheaf.germ (jc ''ᵁ ⊤) y (chart_mem_of_eq jc y hy)
        ((chartSectionsEquiv jc).symm oldRatio),
      Y.presheaf.germ (jc ''ᵁ ⊤) y (chart_mem_of_eq jc y hy)
        ((chartSectionsEquiv jc).symm vEquation)} =
      maximalIdeal (Y.presheaf.stalk y) := by
  subst hy
  exact chart_span_germs jc

end ChartStalk

variable (A : PlaneChartedScheme k)

/-! ## Centres map to centres; isomorphism loci of `between` -/

theorem comap_chartSubstitution_center :
    Ideal.comap (FrobeniusBlowupContact.chartSubstitution (k := k))
      (FrobeniusBlowupContact.centerIdeal (k := k)) = FrobeniusBlowupContact.centerIdeal := by
  symm
  apply (FrobeniusBlowupChartIteration.centerIdeal_isMaximal (k := k)).eq_of_le
    (Ideal.comap_ne_top _ (FrobeniusBlowupChartIteration.centerIdeal_isMaximal (k := k)).ne_top)
  show Ideal.span {FrobeniusBlowupContact.uCoord, FrobeniusBlowupContact.vCoord} ≤ _
  rw [Ideal.span_le]
  rintro y (rfl | rfl)
  · rw [SetLike.mem_coe, Ideal.mem_comap, FrobeniusBlowupContact.chartSubstitution_u]
    exact FrobeniusBlowupContact.centerU.property
  · rw [SetLike.mem_coe, Ideal.mem_comap, FrobeniusBlowupContact.chartSubstitution_v]
    exact Ideal.mul_mem_right _ _ FrobeniusBlowupContact.centerU.property

theorem coordinateBlowdown_origin :
    (coordinateBlowdown (k := k)).base (originPoint (k := k)) = originPoint := by
  rw [coordinateBlowdown_eq]
  apply PrimeSpectrum.ext
  exact comap_chartSubstitution_center

theorem stepProjection_center (n : ℕ) :
    (A.stepProjection n).base ((A.stage (n + 1)).chart.base (originPoint (k := k))) =
      (A.stage n).chart.base (originPoint (k := k)) := by
  have e := congrArg (fun f => f.base (originPoint (k := k))) (A.stage n).nextChart_projection
  change (A.stage n).nextProjection.base ((A.stage n).nextChart.base (originPoint (k := k))) =
    (A.stage n).chart.base (originPoint (k := k))
  rw [show (A.stage n).nextProjection.base ((A.stage n).nextChart.base (originPoint (k := k))) =
    (A.stage n).chart.base ((coordinateBlowdown (k := k)).base (originPoint (k := k))) from e,
    coordinateBlowdown_origin]

theorem between_center (b n : ℕ) (h : b ≤ n) :
    (between A h).base ((A.stage n).chart.base (originPoint (k := k))) =
      (A.stage b).chart.base (originPoint (k := k)) := by
  induction n, h using Nat.le_induction with
  | base =>
    rw [between_refl]
    rfl
  | succ n hbn ih =>
    rw [between_succ A hbn]
    change (between A hbn).base ((A.stepProjection n).base
      ((A.stage (n + 1)).chart.base (originPoint (k := k)))) = _
    rw [stepProjection_center, ih]

/-- The projection `between` is an isomorphism over the complement of the centre of the lower stage. -/
instance between_restrict_isIso (b N : ℕ) (h : b ≤ N) :
    IsIso (between A h ∣_ initialPuncture (A.stage b)) := by
  have e : between A h = (stageFinishIso A b N h).inv ≫ (A.stage b).toInitial (N - b) := by
    rw [Iso.eq_inv_comp, stageFinishIso_hom_between]
  rw [e, morphismRestrict_comp]
  haveI hI := toInitial_restrict_isIso (A.stage b) (N - b)
  infer_instance

/-! ## The lifted chart -/

variable (j : ℕ)

/-- The birth-stage second Rees chart of the pair `C_j, C_{j+1}` (stage `j+2`). -/
abbrev birthChart : Spec (CommRingCat.of (reesVChartRing k)) ⟶ (A.stage (j + 2)).carrier :=
  secondChart (A.stage (j + 1))

theorem birthChart_mem_initialPuncture (p : PrimeSpectrum (reesVChartRing k)) :
    (birthChart A j).base p ∈ initialPuncture (A.stage (j + 2)) :=
  center_not_mem_range_secondChart (A.stage (j + 1)) p

/-- The birth chart, factored through the complement of the centre of stage `j+2`. -/
def birthChartLift : Spec (CommRingCat.of (reesVChartRing k)) ⟶
    (initialPuncture (A.stage (j + 2))).toScheme :=
  IsOpenImmersion.lift (initialPuncture (A.stage (j + 2))).ι (birthChart A j) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    exact birthChart_mem_initialPuncture A j p)

@[reassoc] theorem birthChartLift_ι :
    birthChartLift A j ≫ (initialPuncture (A.stage (j + 2))).ι = birthChart A j :=
  IsOpenImmersion.lift_fac _ _ _

instance birthChartLift_isOpenImmersion : IsOpenImmersion (birthChartLift A j) := by
  haveI hcomp : IsOpenImmersion (birthChartLift A j ≫ (initialPuncture (A.stage (j + 2))).ι) := by
    rw [birthChartLift_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ (initialPuncture (A.stage (j + 2))).ι

/-- The chart of stage `j+3` over the birth chart, through the complement inclusion of the blowup. -/
def stageThreeChart : Spec (CommRingCat.of (reesVChartRing k)) ⟶ (A.stage (j + 3)).carrier :=
  birthChartLift A j ≫ PointBlowupGluing.complementι (A.stage (j + 2)).chart (originPoint (k := k))
    (A.stage (j + 2)).center_closed

instance stageThreeChart_isOpenImmersion : IsOpenImmersion (stageThreeChart A j) := by
  unfold stageThreeChart
  infer_instance

theorem stageThreeChart_step : stageThreeChart A j ≫ A.stepProjection (j + 2) = birthChart A j := by
  rw [stageThreeChart, Category.assoc]
  change birthChartLift A j ≫ (PointBlowupGluing.complementι (A.stage (j + 2)).chart
    (originPoint (k := k)) (A.stage (j + 2)).center_closed ≫
      PointBlowupGluing.projection (A.stage (j + 2)).chart (originPoint (k := k))
        (A.stage (j + 2)).center_closed) = _
  rw [PointBlowupGluing.complementι_projection]
  exact birthChartLift_ι A j

theorem stageThreeChart_mem_initialPuncture (p : PrimeSpectrum (reesVChartRing k)) :
    (stageThreeChart A j).base p ∈ initialPuncture (A.stage (j + 3)) := by
  change (stageThreeChart A j).base p ≠ (A.stage (j + 3)).chart.base (originPoint (k := k))
  intro heq
  have h1 : (A.stepProjection (j + 2)).base ((stageThreeChart A j).base p) = (birthChart A j).base p :=
    congrArg (fun f => f.base p) (stageThreeChart_step A j)
  have h2 : (A.stepProjection (j + 2)).base ((A.stage (j + 3)).chart.base (originPoint (k := k))) =
      (A.stage (j + 2)).chart.base (originPoint (k := k)) := stepProjection_center A (j + 2)
  rw [heq, h2] at h1
  exact center_not_mem_range_secondChart (A.stage (j + 1)) p h1.symm

/-- The stage-`j+3` chart, factored through the complement of the centre of stage `j+3`. -/
def stageThreeChartLift : Spec (CommRingCat.of (reesVChartRing k)) ⟶
    (initialPuncture (A.stage (j + 3))).toScheme :=
  IsOpenImmersion.lift (initialPuncture (A.stage (j + 3))).ι (stageThreeChart A j) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    exact stageThreeChart_mem_initialPuncture A j p)

@[reassoc] theorem stageThreeChartLift_ι :
    stageThreeChartLift A j ≫ (initialPuncture (A.stage (j + 3))).ι = stageThreeChart A j :=
  IsOpenImmersion.lift_fac _ _ _

instance stageThreeChartLift_isOpenImmersion : IsOpenImmersion (stageThreeChartLift A j) := by
  haveI hcomp : IsOpenImmersion (stageThreeChartLift A j ≫ (initialPuncture (A.stage (j + 3))).ι) := by
    rw [stageThreeChartLift_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ (initialPuncture (A.stage (j + 3))).ι

section LiftedChart

variable (N : ℕ) (h : j + 3 ≤ N)

/-- The birth chart lifted to stage `N` through the isomorphism locus of `between`. -/
def liftedChart : Spec (CommRingCat.of (reesVChartRing k)) ⟶ (A.stage N).carrier :=
  stageThreeChartLift A j ≫ inv (between A h ∣_ initialPuncture (A.stage (j + 3))) ≫
    (between A h ⁻¹ᵁ initialPuncture (A.stage (j + 3))).ι

instance liftedChart_isOpenImmersion : IsOpenImmersion (liftedChart A j N h) := by
  unfold liftedChart
  infer_instance

theorem liftedChart_between : liftedChart A j N h ≫ between A h = stageThreeChart A j := by
  rw [liftedChart, Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
    stageThreeChartLift_ι]

theorem between_eq_between_step :
    between A (show j + 2 ≤ N by omega) = between A h ≫ A.stepProjection (j + 2) := by
  rw [← between_step A (j + 2)]
  exact (between_comp A (show j + 2 ≤ j + 3 by omega) h).symm

theorem liftedChart_between' :
    liftedChart A j N h ≫ between A (show j + 2 ≤ N by omega) = birthChart A j := by
  rw [between_eq_between_step A j N h, ← Category.assoc, liftedChart_between, stageThreeChart_step]

/-! ## The crossing point of `C_j` and `C_{j+1}` on stage `N` -/

/-- The common point of `C_j` and `C_{j+1}` on stage `N`: the image of the accepted adjacent point. -/
def crossingPointN : (A.stage N).carrier :=
  (finalOldMap A N j (by omega)).base (adjacentPoint (A.stage j))

theorem crossingPointN_mem_left :
    crossingPointN A j N h ∈ Set.range (finalOldMap A N j (by omega)).base := ⟨_, rfl⟩

theorem crossingPointN_mem_right :
    crossingPointN A j N h ∈ Set.range (finalOldMap A N (j + 1) h).base :=
  finalOld_adjacent A N j h

theorem between_crossingPointN :
    (between A (show j + 2 ≤ N by omega)).base (crossingPointN A j N h) =
      (birthChart A j).base secondOrigin := by
  have e := congrArg (fun f => f.base (adjacentPoint (A.stage j))) (finalOldMap_projection A N j (by omega))
  exact e.trans (adjacentPoint_eq (A.stage j))

theorem between_liftedChart_base (p : PrimeSpectrum (reesVChartRing k)) :
    (between A (show j + 2 ≤ N by omega)).base ((liftedChart A j N h).base p) = (birthChart A j).base p :=
  congrArg (fun f => f.base p) (liftedChart_between' A j N h)

/-- The crossing point is the origin of the lifted chart. -/
theorem crossingPointN_eq : crossingPointN A j N h = (liftedChart A j N h).base secondOrigin := by
  apply eq_of_restrict_isIso (between A (show j + 2 ≤ N by omega)) (initialPuncture (A.stage (j + 2)))
  · rw [between_crossingPointN]
    exact birthChart_mem_initialPuncture A j secondOrigin
  · rw [between_liftedChart_base]
    exact birthChart_mem_initialPuncture A j secondOrigin
  · rw [between_crossingPointN, between_liftedChart_base]

/-! ## The kernel ideals on the lifted chart -/

/-- The lifted chart open. -/
abbrev liftedOpen : (A.stage N).carrier.affineOpens :=
  ⟨liftedChart A j N h ''ᵁ ⊤, chart_image_top_isAffineOpen _⟩

/-- Its section ring, identified with the chart ring. -/
abbrev liftedSections : Γ((A.stage N).carrier, (liftedOpen A j N h).1) ≃+* reesVChartRing k :=
  chartSectionsEquiv (liftedChart A j N h)

/-- **On the lifted chart, `C_j` is the axis `u/v = 0`.** -/
theorem old_ideal_lifted :
    ((finalOldMap A N j (by omega)).ker.ideal (liftedOpen A j N h)).map (liftedSections A j N h) =
      Ideal.span {oldRatio} := by
  rw [ker_ideal_map_eq_of_isPullback (between A (show j + 2 ≤ N by omega)) (previousStrictι (A.stage j))
    (finalOldMap A N j (by omega)) (𝟙 _) (finalOldMap_isPullback A N j (by omega)) (birthChart A j)
    (liftedChart A j N h) (liftedChart_between' A j N h)]
  exact strict_ideal_secondOpen (A.stage j)

/-- The punctured exceptional curve is Noetherian. -/
theorem previousFiber_noetherianSpace (B : PlaneChartedScheme k) : NoetherianSpace (previousFiber B) :=
  haveI hP : NoetherianSpace (projectiveSpace k 1) := projectiveSpace_noetherianSpace k 1
  noetherianSpace_of_isClosedImmersion (previousFiberIso B).hom

theorem previousPuncture_noetherianSpace (B : PlaneChartedScheme k) :
    NoetherianSpace (previousPuncture B).toScheme :=
  haveI hF : NoetherianSpace (previousFiber B) := previousFiber_noetherianSpace B
  (previousPuncture B).ι.isOpenEmbedding.isInducing.noetherianSpace

instance wholePreviousLift_quasiCompact (B : PlaneChartedScheme k) : QuasiCompact (wholePreviousLift B) :=
  haveI hN : NoetherianSpace (previousPuncture B).toScheme := previousPuncture_noetherianSpace B
  quasiCompact_of_noetherianSpace_source _

instance previousFiber_restrict_isClosedImmersion (B : PlaneChartedScheme k) (V : B.next.carrier.Opens) :
    IsClosedImmersion (previousFiberι B ∣_ V) :=
  IsLocalAtTarget.restrict (P := @IsClosedImmersion) inferInstance V

theorem previousStrictι_ker_wholePreviousLift (B : PlaneChartedScheme k) :
    (previousStrictι B).ker = (wholePreviousLift B).ker :=
  Scheme.IdealSheafData.ker_gluedTo _

/-- The lifted exceptional curve is the pullback of the punctured one along the complement inclusion. -/
theorem wholePreviousLift_isPullback (B : PlaneChartedScheme k) :
    IsPullback (previousFiberι B ∣_ PointBlowupGluing.puncture B.next.chart (originPoint (k := k))
        B.next.center_closed) (𝟙 _)
      (PointBlowupGluing.complementι B.next.chart (originPoint (k := k)) B.next.center_closed)
      (wholePreviousLift B) := by
  have hr : Set.range (wholePreviousLift B).base ⊆
      Set.range (PointBlowupGluing.complementι B.next.chart (originPoint (k := k))
        B.next.center_closed).base := by
    rintro _ ⟨t, rfl⟩
    exact ⟨(previousFiberι B ∣_ PointBlowupGluing.puncture B.next.chart (originPoint (k := k))
      B.next.center_closed).base t, rfl⟩
  have hLift : IsOpenImmersion.lift (PointBlowupGluing.complementι B.next.chart (originPoint (k := k))
      B.next.center_closed) (wholePreviousLift B) hr =
      previousFiberι B ∣_ PointBlowupGluing.puncture B.next.chart (originPoint (k := k))
        B.next.center_closed :=
    (IsOpenImmersion.lift_uniq _ _ hr _ rfl).symm
  simpa only [hLift] using IsOpenImmersion.isPullback_lift_id (wholePreviousLift B)
    (PointBlowupGluing.complementι B.next.chart (originPoint (k := k)) B.next.center_closed) hr

/-- **On the lifted chart, `C_{j+1}` is the axis `v = 0`** (three transports: to stage `j+3`, through
the complement inclusion, and the restriction of `P` to the complement of the centre). -/
theorem newer_ideal_lifted :
    ((finalOldMap A N (j + 1) h).ker.ideal (liftedOpen A j N h)).map (liftedSections A j N h) =
      Ideal.span {vEquation} := by
  have h1 := ker_ideal_map_eq_of_isPullback (between A h) (previousStrictι (A.stage (j + 1)))
    (finalOldMap A N (j + 1) h) (𝟙 _) (finalOldMap_isPullback A N (j + 1) h) (stageThreeChart A j)
    (liftedChart A j N h) (liftedChart_between A j N h)
  have h2 := ker_ideal_map_eq_of_isPullback
    (PointBlowupGluing.complementι (A.stage (j + 1)).next.chart (originPoint (k := k))
      (A.stage (j + 1)).next.center_closed)
    (wholePreviousLift (A.stage (j + 1)))
    (previousFiberι (A.stage (j + 1)) ∣_ PointBlowupGluing.puncture (A.stage (j + 1)).next.chart
      (originPoint (k := k)) (A.stage (j + 1)).next.center_closed) (𝟙 _)
    (wholePreviousLift_isPullback (A.stage (j + 1))) (stageThreeChart A j) (birthChartLift A j) rfl
  have h3 := ker_ideal_map_eq_of_isPullback
    (PointBlowupGluing.puncture (A.stage (j + 1)).next.chart (originPoint (k := k))
      (A.stage (j + 1)).next.center_closed).ι
    (previousFiberι (A.stage (j + 1)))
    (previousFiberι (A.stage (j + 1)) ∣_ PointBlowupGluing.puncture (A.stage (j + 1)).next.chart
      (originPoint (k := k)) (A.stage (j + 1)).next.center_closed)
    (previousFiberι (A.stage (j + 1)) ⁻¹ᵁ PointBlowupGluing.puncture (A.stage (j + 1)).next.chart
      (originPoint (k := k)) (A.stage (j + 1)).next.center_closed).ι
    (isPullback_morphismRestrict _ _) (birthChart A j) (birthChartLift A j) (birthChartLift_ι A j)
  rw [h1, previousStrictι_ker_wholePreviousLift, ← h2, h3]
  exact fiber_ideal_secondOpen (A.stage (j + 1))

/-! ## The other components miss the lifted chart -/

theorem liftedOpen_between (y : (A.stage N).carrier) (hy : y ∈ (liftedOpen A j N h).1) :
    ∃ p, (between A (show j + 2 ≤ N by omega)).base y = (birthChart A j).base p := by
  have hy' : y ∈ (liftedChart A j N h).opensRange := by
    rw [← Scheme.Hom.image_top_eq_opensRange]
    exact hy
  obtain ⟨p, rfl⟩ := hy'
  exact ⟨p, between_liftedChart_base A j N h p⟩

/-- The older components `C_i`, `i < j`, miss the lifted chart. -/
theorem old_component_not_mem (i : ℕ) (hi : i + 2 ≤ j + 1) (z : previousStrictTransform (A.stage i)) :
    (finalOldMap A N i (by omega)).base z ∉ (liftedOpen A j N h).1 := by
  intro hz
  obtain ⟨p, hp⟩ := liftedOpen_between A j N h _ hz
  have e : (between A (show j + 2 ≤ N by omega)).base ((finalOldMap A N i (by omega)).base z) =
      (finalOldMap A (j + 2) i (by omega)).base z :=
    congrArg (fun f => f.base z)
      (finalOldMap_between A (show i + 2 ≤ j + 2 by omega) (show j + 2 ≤ N by omega))
  rw [e] at hp
  apply old_not_mem_secondOpen A j i hi z
  rw [hp]
  exact mem_secondOpen (A.stage (j + 1)) p

/-- The later components `C_i`, `i ≥ j + 2`, miss the lifted chart (they project to the centre). -/
theorem later_component_not_mem (i : ℕ) (hi : j + 2 ≤ i) (hiN : i + 2 ≤ N)
    (z : previousStrictTransform (A.stage i)) :
    (finalOldMap A N i hiN).base z ∉ (liftedOpen A j N h).1 := by
  intro hz
  obtain ⟨p, hp⟩ := liftedOpen_between A j N h _ hz
  have h1 := finalOldMap_projection_mem_fiber A N i hiN z
  have h2 : (A.stepProjection i).base ((between A (show i + 1 ≤ N by omega)).base
      ((finalOldMap A N i hiN).base z)) = (A.stage i).chart.base (originPoint (k := k)) :=
    fiber_projection_eq (A.stage i) _ h1
  have ecomp : between A (show j + 2 ≤ N by omega) =
      between A (show i + 1 ≤ N by omega) ≫ A.stepProjection i ≫ between A (show j + 2 ≤ i by omega) := by
    rw [← between_step A i, between_comp, between_comp]
  have e : (between A (show j + 2 ≤ N by omega)).base ((finalOldMap A N i hiN).base z) =
      (between A (show j + 2 ≤ i by omega)).base ((A.stepProjection i).base
        ((between A (show i + 1 ≤ N by omega)).base ((finalOldMap A N i hiN).base z))) := by
    rw [ecomp]
    rfl
  rw [e, h2, between_center] at hp
  exact center_not_mem_range_secondChart (A.stage (j + 1)) p hp.symm

end LiftedChart

/-- The inequality `j + 3 ≤ q + 1` for an older pair `j + 1 < q`. -/
theorem laterLe {q : ℕ} (hj : j + 1 < q) : j + 3 ≤ q + 1 := by omega

/-- The newest component `P` of stage `q+1` (`q ≥ j + 2`) misses the lifted chart. -/
theorem newest_component_not_mem (q : ℕ) (hq : j + 1 < q) (z : previousFiber (A.stage q)) :
    (previousFiberι (A.stage q)).base z ∉ (liftedOpen A j (q + 1) (laterLe j hq)).1 := by
  intro hz
  obtain ⟨p, hp⟩ := liftedOpen_between A j (q + 1) (laterLe j hq) _ hz
  have h2 : (A.stepProjection q).base ((previousFiberι (A.stage q)).base z) =
      (A.stage q).chart.base (originPoint (k := k)) :=
    fiber_projection_eq (A.stage q) _ ⟨z, rfl⟩
  have e : (between A (show j + 2 ≤ q + 1 by omega)).base ((previousFiberι (A.stage q)).base z) =
      (between A (show j + 2 ≤ q by omega)).base
        ((A.stepProjection q).base ((previousFiberι (A.stage q)).base z)) := by
    rw [between_succ A (show j + 2 ≤ q by omega)]
    rfl
  rw [e, h2, between_center] at hp
  exact center_not_mem_range_secondChart (A.stage (j + 1)) p hp.symm

/-! ## The vanishing ideal of the locus on the lifted chart -/

theorem chainIdeal_liftedOpen (q : ℕ) (hj : j + 1 < q) :
    (chainIdeal q A).ideal (liftedOpen A j (q + 1) (laterLe j hj)) =
      Ideal.span {(liftedSections A j (q + 1) (laterLe j hj)).symm oldRatio *
        (liftedSections A j (q + 1) (laterLe j hj)).symm vEquation} := by
  rw [chainIdeal_ideal_eq,
    iInf_eq_inf_of_top _ (Sum.inl ⟨j, by omega⟩ : FinalIndex.{u} q) (Sum.inl ⟨j + 1, hj⟩)]
  · have hC : (finalComponentι A q (Sum.inl ⟨j, by omega⟩)).ker.ideal (liftedOpen A j (q + 1) (laterLe j hj)) =
        Ideal.span {(liftedSections A j (q + 1) (laterLe j hj)).symm oldRatio} :=
      eq_span_symm_of_map_eq _ (old_ideal_lifted A j (q + 1) (laterLe j hj))
    have hD : (finalComponentι A q (Sum.inl ⟨j + 1, hj⟩)).ker.ideal (liftedOpen A j (q + 1) (laterLe j hj)) =
        Ideal.span {(liftedSections A j (q + 1) (laterLe j hj)).symm vEquation} :=
      eq_span_symm_of_map_eq _ (newer_ideal_lifted A j (q + 1) (laterLe j hj))
    rw [hC, hD, (span_symm_oldRatio_isPrime' _).radical, (span_symm_vEquation_isPrime' _).radical,
      span_symm_inf', map_mul (liftedSections A j (q + 1) (laterLe j hj)).symm (oldRatio (k := k))
        (vEquation (k := k))]
  · rintro (⟨i, hi⟩ | ⟨⟩) hne hne'
    · have hij : i ≠ j := fun e => hne (by congr 1; exact Fin.ext e)
      have hij' : i ≠ j + 1 := fun e => hne' (by congr 1; exact Fin.ext e)
      rcases Nat.lt_or_ge i j with hlt | hge
      · have hi' : (finalComponentι A q (Sum.inl ⟨i, hi⟩)).ker.ideal
            (liftedOpen A j (q + 1) (laterLe j hj)) = ⊤ :=
          ker_ideal_eq_top_of_disjoint (finalOldMap A (q + 1) i (by omega)) _
            (old_component_not_mem A j (q + 1) (laterLe j hj) i (by omega))
        rw [hi', Ideal.radical_top]
      · have hi' : (finalComponentι A q (Sum.inl ⟨i, hi⟩)).ker.ideal
            (liftedOpen A j (q + 1) (laterLe j hj)) = ⊤ :=
          ker_ideal_eq_top_of_disjoint (finalOldMap A (q + 1) i (by omega)) _
            (later_component_not_mem A j (q + 1) (laterLe j hj) i (by omega) (by omega))
        rw [hi', Ideal.radical_top]
    · have hi' : (finalComponentι A q (Sum.inr PUnit.unit)).ker.ideal
          (liftedOpen A j (q + 1) (laterLe j hj)) = ⊤ :=
        ker_ideal_eq_top_of_disjoint (previousFiberι (A.stage q)) _
          (newest_component_not_mem A j q hj)
      rw [hi', Ideal.radical_top]

/-! ## The transversal crossing of an older pair -/

section Later

variable (q : ℕ) [NoetherianSpace (chainStage q A)] [IsLocallyNoetherian (chainStage q A)]

omit [IsLocallyNoetherian (chainStage q A)] in
/-- **An older pair `C_{j+1}, C_{j+2}` (`j + 1 < q`) of the chain of stage `q+1` crosses transversally at
its common point** (lane A1's `TransversalCrossing`). -/
theorem transversalCrossing_later (hyp : ChainSinglePoints q A) (j : Fin q) (hj : j.val + 1 < q)
    (x : chainScheme q A) (hC : x ∈ (chainComponentEquiv q A hyp j.castSucc).1)
    (hD : x ∈ (chainComponentEquiv q A hyp j.succ).1) :
    TransversalCrossing (chainInclusion q A) (chainComponentEquiv q A hyp j.castSucc)
      (chainComponentEquiv q A hyp j.succ) x := by
  have hmemC : chainMember.{u} q j.castSucc = Sum.inl ⟨j.val, by omega⟩ :=
    chainMember_of_lt q j.castSucc (by rw [Fin.coe_castSucc]; omega)
  have hmemD : chainMember.{u} q j.succ = Sum.inl ⟨j.val + 1, hj⟩ :=
    chainMember_of_lt q j.succ (by rw [Fin.val_succ]; exact hj)
  have hC' : (chainInclusion q A).base x ∈ finalSupport A q (chainMember.{u} q j.castSucc) := by
    have h := hC
    rw [chainComponentEquiv_val, range_chainCurve_eq] at h
    exact h
  have hD' : (chainInclusion q A).base x ∈ finalSupport A q (chainMember.{u} q j.succ) := by
    have h := hD
    rw [chainComponentEquiv_val, range_chainCurve_eq] at h
    exact h
  rw [hmemC] at hC'
  rw [hmemD] at hD'
  have hyC : (chainInclusion q A).base x ∈ Set.range (finalOldMap A (q + 1) j.val (by omega)).base := hC'
  have hyD : (chainInclusion q A).base x ∈
      Set.range (finalOldMap A (q + 1) (j.val + 1) (by omega)).base := hD'
  have hy : (chainInclusion q A).base x = crossingPointN A j.val (q + 1) (laterLe j.val hj) :=
    old_pair_subsingleton A (q + 1) j.val (laterLe j.val hj) ⟨hyC, hyD⟩
      ⟨crossingPointN_mem_left A j.val (q + 1) (laterLe j.val hj),
        crossingPointN_mem_right A j.val (q + 1) (laterLe j.val hj)⟩
  rw [crossingPointN_eq] at hy
  refine transversalCrossing_of_chart A q hyp j.castSucc j.succ x (liftedOpen A j.val (q + 1) (laterLe j.val hj))
    (chart_mem_of_eq _ _ hy) (chart_regularLocal_of_eq _ _ hy) (chart_ringKrullDim_of_eq _ _ hy) _ _
    (chart_span_germs_of_eq _ _ hy) (chainIdeal_liftedOpen A j.val q hj) ?_ ?_
  · rw [hmemC]
    have e : (finalComponentι A q (Sum.inl ⟨j.val, by omega⟩)).ker.ideal
        (liftedOpen A j.val (q + 1) (laterLe j.val hj)) =
        Ideal.span {(liftedSections A j.val (q + 1) (laterLe j.val hj)).symm oldRatio} :=
      eq_span_symm_of_map_eq _ (old_ideal_lifted A j.val (q + 1) (laterLe j.val hj))
    exact (congrArg (fun I : Ideal Γ((A.stage (q + 1)).carrier,
      (liftedOpen A j.val (q + 1) (laterLe j.val hj)).1) =>
        (liftedSections A j.val (q + 1) (laterLe j.val hj)).symm oldRatio ∈ I) e).mpr
      (Ideal.mem_span_singleton_self _)
  · rw [hmemD]
    have e : (finalComponentι A q (Sum.inl ⟨j.val + 1, hj⟩)).ker.ideal
        (liftedOpen A j.val (q + 1) (laterLe j.val hj)) =
        Ideal.span {(liftedSections A j.val (q + 1) (laterLe j.val hj)).symm vEquation} :=
      eq_span_symm_of_map_eq _ (newer_ideal_lifted A j.val (q + 1) (laterLe j.val hj))
    exact (congrArg (fun I : Ideal Γ((A.stage (q + 1)).carrier,
      (liftedOpen A j.val (q + 1) (laterLe j.val hj)).1) =>
        (liftedSections A j.val (q + 1) (laterLe j.val hj)).symm vEquation ∈ I) e).mpr
      (Ideal.mem_span_singleton_self _)

/-- **Lane A1's hypothesis `ChainTransversal`, for every charted plane and every `q`.** -/
theorem chainTransversal : ChainTransversal q A (chainSinglePoints A q) := by
  intro j x hC hD
  by_cases hj : j.val + 1 < q
  · exact transversalCrossing_later A q (chainSinglePoints A q) j hj x hC hD
  · obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨j.val, by have := j.isLt; omega⟩
    exact transversalCrossing_last A m (chainSinglePoints A (m + 1)) j (by have := j.isLt; omega) x hC hD

end Later

/-- **`Pic(C_1 ∪ ⋯ ∪ C_q ∪ P) ≃* ℤ^{q+1}`, unconditionally** (lane A1's `chainPicardEquivFin` with both
hypotheses discharged). -/
def chainPicardEquivFin_unconditional (q : ℕ) [IsAlgClosed k] [NoetherianSpace (chainStage q A)]
    [IsLocallyNoetherian (chainStage q A)] [LocallyOfFiniteType (A.stage (q + 1)).structureMap] :
    (chainScheme q A).Pic ≃* (Fin (q + 1) → Multiplicative ℤ) :=
  chainPicardEquivFin q A (chainSinglePoints A q) (chainTransversal A q)

/-- Universe check at universe `0`. -/
example (k₀ : Type) [Field k₀] (A₀ : PlaneChartedScheme k₀) (q₀ : ℕ)
    [NoetherianSpace (chainStage q₀ A₀)] [IsLocallyNoetherian (chainStage q₀ A₀)] :
    ChainTransversal q₀ A₀ (chainSinglePoints A₀ q₀) :=
  chainTransversal A₀ q₀

end KltDP.Examples.FrobeniusExceptionalChainTransversalLater

import KltDP.Examples.ProjectiveProductTranslation
import KltDP.Examples.FrobeniusGlobalExceptionalSuccessor
import KltDP.Examples.FrobeniusContactTowerSelectedPoint
import KltDP.Examples.FrobeniusExceptionalFinalConfiguration

/-!
# Transport of the contact towers along an isomorphism of charted planes

An isomorphism of charted planes `e : ChartedIso A B` is an isomorphism `A.carrier ≅ B.carrier`
over `k` carrying the chart of `A` to the chart of `B`. The accepted one-step blowup
`A.nextScheme` is the two-open gluing of the affine Rees blowup of the chart (the same scheme for
`A` and `B`) with the complement of the centre; the isomorphism maps the complement of the centre
of `A` onto that of `B` (`punctureMap`), compatibly with the overlap, and the two pieces glue to an
isomorphism `nextIso e : A.nextScheme ≅ B.nextScheme` which is the identity on the affine blowup
(`affineBlowupι_nextHom`), restricts to `e` on the complements (`complementι_nextHom`), carries the
chart of the next stage to the chart of the next stage (`nextChart_comm`) and commutes with the
blowdowns (`nextHom_nextProjection`). Iterating gives an isomorphism of charted planes of every
stage (`stage e n`) commuting with the step projections and the composite projections.

Applied to the translation `τ_a × τ_{a^p}` (`ProjectiveProductTranslation`), this gives the
isomorphism `translationChartedIso p a : ChartedIso projectiveProductInitial (translatedInitial p a)`
and hence `stageTranslationIso p a n : projectiveContactStage n ≅ selectedStage p a n`, the
origin contact tower and the translated tower at `(a, a^p)` being isomorphic stage by stage,
compatibly with the blowdowns, the selected charts and the projections to `P¹ × P¹`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusTowerTransport

open KltDP.Geometry KltDP.Geometry.PointBlowupGluing KltDP.SchemeTwoOpenGluing
  FrobeniusGlobalBlowupStages FrobeniusBlowupChartIteration FrobeniusBlowupContact
  FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint ProjectiveProductTranslation
  FrobeniusExceptionalFinalConfiguration

variable {k : Type u} [Field k]

/-- The centre of a chart is a maximal ideal (the accepted witness, as in the accepted gluing
modules). -/
local instance towerTransportOriginMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- An isomorphism of charted planes: an isomorphism of the carriers over `k` carrying the chart of
`A` to the chart of `B`. -/
structure ChartedIso (A B : PlaneChartedScheme k) where
  /-- The isomorphism of the underlying schemes. -/
  iso : A.carrier ≅ B.carrier
  chart_comm : A.chart ≫ iso.hom = B.chart
  structure_comm : iso.hom ≫ B.structureMap = A.structureMap

namespace ChartedIso

variable {A B : PlaneChartedScheme k} (e : ChartedIso A B)

/-- The inverse isomorphism of charted planes. -/
def symm : ChartedIso B A where
  iso := e.iso.symm
  chart_comm := by
    rw [Iso.symm_hom, ← e.chart_comm, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  structure_comm := by
    rw [Iso.symm_hom, ← e.structure_comm, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

theorem symm_iso_hom : e.symm.iso.hom = e.iso.inv := rfl

theorem chart_comm_inv : B.chart ≫ e.iso.inv = A.chart := e.symm.chart_comm

/-- The centres correspond. -/
theorem center_comm :
    e.iso.hom.base (A.chart.base (originPoint (k := k))) = B.chart.base originPoint :=
  congrArg (fun f => f.base (originPoint (k := k))) e.chart_comm

/-! ## The complements of the centres -/

theorem range_puncture_le :
    Set.range ((puncture A.chart (originPoint (k := k)) A.center_closed).ι ≫ e.iso.hom).base ⊆
      Set.range (puncture B.chart (originPoint (k := k)) B.center_closed).ι.base := by
  rintro _ ⟨x, rfl⟩
  refine ⟨⟨e.iso.hom.base x.1, ?_⟩, rfl⟩
  change e.iso.hom.base x.1 ∉ ({B.chart.base (originPoint (k := k))} : Set B.carrier)
  intro h
  have hx : x.1 ∉ ({A.chart.base (originPoint (k := k))} : Set A.carrier) := x.2
  apply hx
  rw [Set.mem_singleton_iff] at h ⊢
  rw [← e.center_comm] at h
  exact e.iso.hom.isOpenEmbedding.injective h

/-- The isomorphism restricted to the complements of the centres. -/
def punctureMap :
    (puncture A.chart (originPoint (k := k)) A.center_closed).toScheme ⟶
      (puncture B.chart (originPoint (k := k)) B.center_closed).toScheme :=
  IsOpenImmersion.lift (puncture B.chart (originPoint (k := k)) B.center_closed).ι
    ((puncture A.chart (originPoint (k := k)) A.center_closed).ι ≫ e.iso.hom) e.range_puncture_le

@[reassoc] theorem punctureMap_ι :
    e.punctureMap ≫ (puncture B.chart (originPoint (k := k)) B.center_closed).ι =
      (puncture A.chart (originPoint (k := k)) A.center_closed).ι ≫ e.iso.hom :=
  IsOpenImmersion.lift_fac _ _ _

theorem punctureMap_symm : e.punctureMap ≫ e.symm.punctureMap = 𝟙 _ := by
  apply (cancel_mono (puncture A.chart (originPoint (k := k)) A.center_closed).ι).mp
  rw [Category.assoc, punctureMap_ι, ← Category.assoc, punctureMap_ι, Category.assoc,
    Category.id_comp, symm_iso_hom, Iso.hom_inv_id, Category.comp_id]

theorem symm_punctureMap : e.symm.punctureMap ≫ e.punctureMap = 𝟙 _ := by
  apply (cancel_mono (puncture B.chart (originPoint (k := k)) B.center_closed).ι).mp
  rw [Category.assoc, punctureMap_ι, ← Category.assoc, punctureMap_ι, Category.assoc,
    Category.id_comp, symm_iso_hom, Iso.inv_hom_id, Category.comp_id]

/-- The overlap maps of the two gluings correspond. -/
theorem overlapToPuncture_punctureMap :
    overlapToPuncture A.chart (originPoint (k := k)) A.center_closed ≫ e.punctureMap =
      overlapToPuncture B.chart (originPoint (k := k)) B.center_closed := by
  apply (cancel_mono (puncture B.chart (originPoint (k := k)) B.center_closed).ι).mp
  rw [Category.assoc, punctureMap_ι, ← Category.assoc, ← overlap_base_compatibility,
    ← overlap_base_compatibility, Category.assoc, Category.assoc, e.chart_comm]

/-! ## The isomorphism of the next stages -/

/-- The morphism of the one-step blowups: the identity on the affine Rees blowup, `e` on the
complement of the centre. -/
def nextHom : A.nextScheme ⟶ B.nextScheme :=
  toTarget (overlapOpen (originPoint (k := k))).ι
    (overlapToPuncture A.chart (originPoint (k := k)) A.center_closed)
    (affineBlowupι B.chart (originPoint (k := k)) B.center_closed)
    (e.punctureMap ≫ complementι B.chart (originPoint (k := k)) B.center_closed)
    (by
      rw [← Category.assoc, overlapToPuncture_punctureMap]
      exact overlap_condition _ _)

@[reassoc] theorem affineBlowupι_nextHom :
    affineBlowupι A.chart (originPoint (k := k)) A.center_closed ≫ e.nextHom =
      affineBlowupι B.chart (originPoint (k := k)) B.center_closed :=
  leftι_toTarget _ _ _ _ _

@[reassoc] theorem complementι_nextHom :
    complementι A.chart (originPoint (k := k)) A.center_closed ≫ e.nextHom =
      e.punctureMap ≫ complementι B.chart (originPoint (k := k)) B.center_closed :=
  rightι_toTarget _ _ _ _ _

theorem nextHom_symm : e.nextHom ≫ e.symm.nextHom = 𝟙 _ := by
  apply PointBlowupGluing.hom_ext
  · rw [← Category.assoc, affineBlowupι_nextHom, affineBlowupι_nextHom, Category.comp_id]
  · rw [← Category.assoc, complementι_nextHom, Category.assoc, complementι_nextHom,
      ← Category.assoc, punctureMap_symm, Category.id_comp, Category.comp_id]

theorem symm_nextHom : e.symm.nextHom ≫ e.nextHom = 𝟙 _ := by
  apply PointBlowupGluing.hom_ext
  · rw [← Category.assoc, affineBlowupι_nextHom, affineBlowupι_nextHom, Category.comp_id]
  · rw [← Category.assoc, complementι_nextHom, Category.assoc, complementι_nextHom,
      ← Category.assoc, symm_punctureMap, Category.id_comp, Category.comp_id]

/-- **The isomorphism of the one-step blowups.** -/
def nextIso : A.nextScheme ≅ B.nextScheme where
  hom := e.nextHom
  inv := e.symm.nextHom
  hom_inv_id := e.nextHom_symm
  inv_hom_id := e.symm_nextHom

instance nextHom_isIso : IsIso e.nextHom := ⟨e.symm.nextHom, e.nextHom_symm, e.symm_nextHom⟩

/-- The selected charts of the next stages correspond. -/
theorem nextChart_comm : A.nextChart ≫ e.nextHom = B.nextChart := by
  rw [PlaneChartedScheme.nextChart, PlaneChartedScheme.nextChart, Category.assoc]
  change coordinateChart ≫ (affineBlowupι A.chart (originPoint (k := k)) A.center_closed ≫
    e.nextHom) = coordinateChart ≫ affineBlowupι B.chart (originPoint (k := k)) B.center_closed
  rw [affineBlowupι_nextHom]

/-- The isomorphism commutes with the blowdowns. -/
theorem nextHom_nextProjection : e.nextHom ≫ B.nextProjection = A.nextProjection ≫ e.iso.hom := by
  apply PointBlowupGluing.hom_ext
  · rw [← Category.assoc, affineBlowupι_nextHom]
    change affineBlowupι B.chart (originPoint (k := k)) B.center_closed ≫
        projection B.chart (originPoint (k := k)) B.center_closed =
      (affineBlowupι A.chart (originPoint (k := k)) A.center_closed ≫
        projection A.chart (originPoint (k := k)) A.center_closed) ≫ e.iso.hom
    rw [affineBlowupι_projection, affineBlowupι_projection, Category.assoc, e.chart_comm]
  · rw [← Category.assoc, complementι_nextHom, Category.assoc]
    change e.punctureMap ≫ (complementι B.chart (originPoint (k := k)) B.center_closed ≫
        projection B.chart (originPoint (k := k)) B.center_closed) =
      (complementι A.chart (originPoint (k := k)) A.center_closed ≫
        projection A.chart (originPoint (k := k)) A.center_closed) ≫ e.iso.hom
    rw [complementι_projection, complementι_projection, punctureMap_ι]

/-- The isomorphism is over `k`. -/
theorem nextHom_nextStructure : e.nextHom ≫ B.nextStructure = A.nextStructure := by
  rw [PlaneChartedScheme.nextStructure, PlaneChartedScheme.nextStructure, ← Category.assoc,
    nextHom_nextProjection, Category.assoc, e.structure_comm]

/-- **The isomorphism of charted planes of the next stages.** -/
def next : ChartedIso A.next B.next where
  iso := e.nextIso
  chart_comm := e.nextChart_comm
  structure_comm := e.nextHom_nextStructure

theorem next_iso_hom : e.next.iso.hom = e.nextHom := rfl

/-! ## All stages -/

/-- **The isomorphism of charted planes of every stage.** -/
def stage : ∀ n : ℕ, ChartedIso (A.stage n) (B.stage n)
  | 0 => e
  | n + 1 => (stage n).next

theorem stage_zero : e.stage 0 = e := rfl

theorem stage_succ (n : ℕ) : e.stage (n + 1) = (e.stage n).next := rfl

/-- The stage isomorphisms carry the selected charts to the selected charts. -/
theorem stage_chart_comm (n : ℕ) :
    (A.stage n).chart ≫ (e.stage n).iso.hom = (B.stage n).chart :=
  (e.stage n).chart_comm

/-- The stage isomorphisms are over `k`. -/
theorem stage_structure_comm (n : ℕ) :
    (e.stage n).iso.hom ≫ (B.stage n).structureMap = (A.stage n).structureMap :=
  (e.stage n).structure_comm

/-- The stage isomorphisms commute with the step blowdowns. -/
theorem stage_hom_stepProjection (n : ℕ) :
    (e.stage (n + 1)).iso.hom ≫ B.stepProjection n = A.stepProjection n ≫ (e.stage n).iso.hom :=
  (e.stage n).nextHom_nextProjection

/-- The stage isomorphisms commute with the composite projections to the initial planes. -/
theorem stage_hom_toInitial : ∀ n : ℕ,
    (e.stage n).iso.hom ≫ B.toInitial n = A.toInitial n ≫ e.iso.hom
  | 0 => by
    change e.iso.hom ≫ 𝟙 B.carrier = 𝟙 A.carrier ≫ e.iso.hom
    rw [Category.comp_id, Category.id_comp]
  | n + 1 => by
    rw [PlaneChartedScheme.toInitial_succ, PlaneChartedScheme.toInitial_succ, ← Category.assoc,
      stage_hom_stepProjection, Category.assoc, stage_hom_toInitial n, Category.assoc]

/-- The stage isomorphisms commute with the composite blowdowns `between A h` between any two
stages. -/
theorem stage_hom_between {i j : ℕ} (h : i ≤ j) :
    (e.stage j).iso.hom ≫ between B h = between A h ≫ (e.stage i).iso.hom := by
  induction j, h using Nat.le_induction with
  | base => rw [between_refl, between_refl, Category.comp_id, Category.id_comp]
  | succ j hij ih =>
    rw [between_succ B hij, between_succ A hij, ← Category.assoc, stage_hom_stepProjection,
      Category.assoc, ih, Category.assoc]

end ChartedIso

/-! ## The translation of the origin tower to the tower at `(a, a^p)` -/

/-- **The translation `τ_a × τ_{a^p}` as an isomorphism of charted planes** from the origin datum
`projectiveProductInitial` to the translated datum `translatedInitial p a`. -/
def translationChartedIso (p : ℕ) (a : k) :
    ChartedIso (projectiveProductInitial (k := k)) (translatedInitial p a) where
  iso := productTranslationIso a (a ^ p)
  chart_comm := (translatedPlaneChart_eq p a).symm
  structure_comm := productTranslation_over_base a (a ^ p)

/-- **The origin contact tower and the translated tower are isomorphic stage by stage.** -/
def stageTranslationIso (p : ℕ) (a : k) (n : ℕ) :
    projectiveContactStage (k := k) n ≅ selectedStage p a n :=
  ((translationChartedIso p a).stage n).iso

theorem stageTranslationIso_zero_hom (p : ℕ) (a : k) :
    (stageTranslationIso p a 0).hom = productTranslation a (a ^ p) := rfl

/-- The stage isomorphisms commute with the step blowdowns. -/
theorem stageTranslationIso_hom_stepProjection (p : ℕ) (a : k) (n : ℕ) :
    (stageTranslationIso p a (n + 1)).hom ≫ (translatedInitial p a).stepProjection n =
      (projectiveProductInitial (k := k)).stepProjection n ≫ (stageTranslationIso p a n).hom :=
  (translationChartedIso p a).stage_hom_stepProjection n

/-- The stage isomorphisms carry the selected chart of the origin tower to the selected chart of
the translated tower. -/
theorem stageTranslationIso_chart (p : ℕ) (a : k) (n : ℕ) :
    ((projectiveProductInitial (k := k)).stage n).chart ≫ (stageTranslationIso p a n).hom =
      ((translatedInitial p a).stage n).chart :=
  (translationChartedIso p a).stage_chart_comm n

/-- The stage isomorphisms commute with the projections to `P¹ × P¹`: on the base they are the
translation `τ_a × τ_{a^p}`. -/
theorem stageTranslationIso_hom_projection (p : ℕ) (a : k) (n : ℕ) :
    (stageTranslationIso p a n).hom ≫ selectedProjection p a n =
      projectiveContactProjection n ≫ productTranslation a (a ^ p) :=
  (translationChartedIso p a).stage_hom_toInitial n

/-- The stage isomorphisms commute with the composite blowdowns between any two stages. -/
theorem stageTranslationIso_hom_between (p : ℕ) (a : k) {i j : ℕ} (h : i ≤ j) :
    (stageTranslationIso p a j).hom ≫ between (translatedInitial p a) h =
      between (projectiveProductInitial (k := k)) h ≫ (stageTranslationIso p a i).hom :=
  (translationChartedIso p a).stage_hom_between h

/-- The stage isomorphisms are over `k`. -/
theorem stageTranslationIso_hom_structure (p : ℕ) (a : k) (n : ℕ) :
    (stageTranslationIso p a n).hom ≫ ((translatedInitial p a).stage n).structureMap =
      ((projectiveProductInitial (k := k)).stage n).structureMap :=
  (translationChartedIso p a).stage_structure_comm n

/-! ## The newest exceptional curves correspond -/

namespace ChartedIso

variable {A B : PlaneChartedScheme k} (e : ChartedIso A B)

/-- The closed centres correspond. -/
theorem closedCenterInclusion_comm :
    closedCenterInclusion A.chart (originPoint (k := k)) ≫ e.iso.hom =
      closedCenterInclusion B.chart (originPoint (k := k)) := by
  rw [closedCenterInclusion, closedCenterInclusion, Category.assoc, e.chart_comm]

/-- The induced morphism of the newest exceptional curves (the literal centre fibres of the
blowdowns). -/
def previousFiberMap :
    FrobeniusGlobalExceptionalSuccessor.previousFiber A ⟶
      FrobeniusGlobalExceptionalSuccessor.previousFiber B :=
  pullback.map (projection A.chart (originPoint (k := k)) A.center_closed)
    (closedCenterInclusion A.chart (originPoint (k := k)))
    (projection B.chart (originPoint (k := k)) B.center_closed)
    (closedCenterInclusion B.chart (originPoint (k := k)))
    e.nextHom (𝟙 _) e.iso.hom e.nextHom_nextProjection.symm
    (by rw [Category.id_comp, closedCenterInclusion_comm])

@[reassoc] theorem previousFiberMap_fst :
    e.previousFiberMap ≫ pullback.fst (projection B.chart (originPoint (k := k)) B.center_closed)
        (closedCenterInclusion B.chart (originPoint (k := k))) =
      pullback.fst (projection A.chart (originPoint (k := k)) A.center_closed)
        (closedCenterInclusion A.chart (originPoint (k := k))) ≫ e.nextHom :=
  pullback.lift_fst _ _ _

@[reassoc] theorem previousFiberMap_snd :
    e.previousFiberMap ≫ pullback.snd (projection B.chart (originPoint (k := k)) B.center_closed)
        (closedCenterInclusion B.chart (originPoint (k := k))) =
      pullback.snd (projection A.chart (originPoint (k := k)) A.center_closed)
        (closedCenterInclusion A.chart (originPoint (k := k))) :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- **The newest exceptional curve of `A.next` is carried onto that of `B.next`.** -/
theorem previousFiberMap_ι :
    e.previousFiberMap ≫ FrobeniusGlobalExceptionalSuccessor.previousFiberι B =
      FrobeniusGlobalExceptionalSuccessor.previousFiberι A ≫ e.nextHom :=
  e.previousFiberMap_fst

theorem previousFiberMap_symm : e.previousFiberMap ≫ e.symm.previousFiberMap = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.id_comp, previousFiberMap_fst, ← Category.assoc,
      previousFiberMap_fst, Category.assoc, nextHom_symm, Category.comp_id]
  · rw [Category.assoc, Category.id_comp, previousFiberMap_snd, previousFiberMap_snd]

theorem symm_previousFiberMap : e.symm.previousFiberMap ≫ e.previousFiberMap = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.id_comp, previousFiberMap_fst, ← Category.assoc,
      previousFiberMap_fst, Category.assoc, symm_nextHom, Category.comp_id]
  · rw [Category.assoc, Category.id_comp, previousFiberMap_snd, previousFiberMap_snd]

/-- **The isomorphism of the newest exceptional curves.** -/
def previousFiberIso :
    FrobeniusGlobalExceptionalSuccessor.previousFiber A ≅
      FrobeniusGlobalExceptionalSuccessor.previousFiber B where
  hom := e.previousFiberMap
  inv := e.symm.previousFiberMap
  hom_inv_id := e.previousFiberMap_symm
  inv_hom_id := e.symm_previousFiberMap

end ChartedIso

/-- The newest exceptional curves `P` of the origin tower and of the translated tower correspond
under the stage isomorphism. -/
theorem stageTranslationIso_previousFiber (p : ℕ) (a : k) (n : ℕ) :
    ((translationChartedIso p a).stage n).previousFiberMap ≫
        FrobeniusGlobalExceptionalSuccessor.previousFiberι ((translatedInitial p a).stage n) =
      FrobeniusGlobalExceptionalSuccessor.previousFiberι
          ((projectiveProductInitial (k := k)).stage n) ≫ (stageTranslationIso p a (n + 1)).hom :=
  ((translationChartedIso p a).stage n).previousFiberMap_ι

end KltDP.Examples.FrobeniusTowerTransport

import KltDP.Examples.FrobeniusGlobalExceptionalSuccessor
import KltDP.Examples.FrobeniusStageComplement

/-!
# The original previous exceptional curve through all later stages

After its adjacent exceptional pair is formed, the whole original previous
strict transform avoids the selected chart. The existing finite-stage
complement isomorphism therefore lifts this same curve through every later
whole blowup. These maps are actual closed immersions and actual pullbacks
of the original inclusion. They commute with all one-step projections,
avoid all later selected charts and centers, and are disjoint from every
newly created later center fiber.

Reuse: the original finite-stage complement isomorphism and its projection
equation, and pinned restriction-pullback uniqueness. The short uniqueness
proof is reproduced from the existing private whole-graph helper; that
private declaration is not imported as a public API. No curve or incidence
property is supplied as an additional geometric premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusExceptionalLaterStages

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupChartIteration
open FrobeniusGlobalBlowupStages FrobeniusGlobalExceptionalSuccessor
open FrobeniusStageComplement.PlaneChartedScheme

/-- The actual restriction pullback determines a lift over an isomorphism open. -/
private theorem eq_lift_over_restrict_iso {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) [IsIso (f ∣_ U)] (h : Z ⟶ X) (q : Z ⟶ U.toScheme)
    (w : q ≫ U.ι = h ≫ f) : h = q ≫ inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι := by
  let H := isPullback_morphismRestrict f U
  let l := H.lift q h w
  have hl : l = q ≫ inv (f ∣_ U) := by
    apply (cancel_mono (f ∣_ U)).mp
    change H.lift q h w ≫ (f ∣_ U) = (q ≫ inv (f ∣_ U)) ≫ (f ∣_ U)
    rw [H.lift_fst, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  calc
    h = l ≫ (f ⁻¹ᵁ U).ι := (H.lift_snd q h w).symm
    _ = q ≫ inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι := by rw [hl, Category.assoc]

variable {k : Type u} [Field k] (A : PlaneChartedScheme k)

local instance originPoint_asIdeal_isMaximal :
    (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- The whole old curve lies in the original complement of the following center. -/
theorem previousCurve_range_puncture :
    Set.range (previousStrictι A).base ⊆
      Set.range (initialPuncture A.next.next).ι.base := by
  rintro _ ⟨z, rfl⟩
  refine ⟨⟨(previousStrictι A).base z, ?_⟩, rfl⟩
  change (previousStrictι A).base z ≠ A.next.next.chart.base (originPoint (k := k))
  intro hz
  exact nextCenter_not_on_previousStrict A ⟨z, hz⟩

/-- The same original closed curve, factored through the actual center complement. -/
def previousCurveToComplement : previousStrictTransform A ⟶
    (initialPuncture A.next.next).toScheme :=
  IsOpenImmersion.lift (initialPuncture A.next.next).ι
    (previousStrictι A) (previousCurve_range_puncture A)

@[reassoc] theorem previousCurveToComplement_ι :
    previousCurveToComplement A ≫ (initialPuncture A.next.next).ι = previousStrictι A :=
  IsOpenImmersion.lift_fac _ _ _

/-- The original whole previous curve in the actual scheme after `n` further blowups. -/
def laterCurveMap (n : ℕ) : previousStrictTransform A ⟶
    (A.next.next.stage n).carrier :=
  previousCurveToComplement A ≫ (stageComplementIso A.next.next n).inv ≫
    (stagePuncture A.next.next n).ι

/-- Its actual finite projection is exactly the original closed inclusion. -/
@[reassoc] theorem laterCurveMap_projection (n : ℕ) :
    laterCurveMap A n ≫ A.next.next.toInitial n = previousStrictι A := by
  rw [laterCurveMap, Category.assoc, Category.assoc,
    ← stageComplementIso_hom_ι A.next.next n,
    Iso.inv_hom_id_assoc, previousCurveToComplement_ι]

/-- Original maps over the old closed curve have a unique lift at every later stage. -/
theorem laterCurveMap_eq_of_projection (n : ℕ) {Z : Scheme.{u}}
    (h : Z ⟶ (A.next.next.stage n).carrier) (q : Z ⟶ previousStrictTransform A)
    (w : h ≫ A.next.next.toInitial n = q ≫ previousStrictι A) :
    h = q ≫ laterCurveMap A n := by
  letI := toInitial_restrict_isIso A.next.next n
  have hw : (q ≫ previousCurveToComplement A) ≫
      (initialPuncture A.next.next).ι = h ≫ A.next.next.toInitial n := by
    rw [Category.assoc, previousCurveToComplement_ι]
    exact w.symm
  have he := eq_lift_over_restrict_iso (A.next.next.toInitial n)
    (initialPuncture A.next.next) h (q ≫ previousCurveToComplement A) hw
  change h = q ≫ previousCurveToComplement A ≫
    inv (A.next.next.toInitial n ∣_ initialPuncture A.next.next) ≫
      (A.next.next.toInitial n ⁻¹ᵁ initialPuncture A.next.next).ι
  simpa only [Category.assoc] using he

/-- The same original curve is the actual scheme-theoretic inverse image,
not merely a map with the same pointwise projection. -/
theorem laterCurveMap_isPullback (n : ℕ) :
    IsPullback (laterCurveMap A n) (𝟙 (previousStrictTransform A))
      (A.next.next.toInitial n) (previousStrictι A) := by
  have w : laterCurveMap A n ≫ A.next.next.toInitial n =
      (𝟙 (previousStrictTransform A)) ≫ previousStrictι A := by
    rw [laterCurveMap_projection, Category.id_comp]
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk w (fun s => s.snd)
    (fun s => (laterCurveMap_eq_of_projection A n s.fst s.snd s.condition).symm)
    (fun s => Category.comp_id s.snd)
    (fun s m _ hm => by simpa only [Category.comp_id] using hm))

/-- In particular each later map is an actual closed immersion. -/
instance laterCurveMap_isClosedImmersion (n : ℕ) : IsClosedImmersion (laterCurveMap A n) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (laterCurveMap_isPullback A n).flip inferInstance

/-- The literal pullback scheme is canonically the unchanged original curve. -/
def laterCurveIsoPullback (n : ℕ) : previousStrictTransform A ≅
    pullback (A.next.next.toInitial n) (previousStrictι A) :=
  (laterCurveMap_isPullback A n).isoPullback

@[reassoc] theorem laterCurveIsoPullback_hom_fst (n : ℕ) :
    (laterCurveIsoPullback A n).hom ≫ pullback.fst _ _ = laterCurveMap A n :=
  (laterCurveMap_isPullback A n).isoPullback_hom_fst

@[reassoc] theorem laterCurveIsoPullback_hom_snd (n : ℕ) :
    (laterCurveIsoPullback A n).hom ≫ pullback.snd _ _ = 𝟙 (previousStrictTransform A) :=
  (laterCurveMap_isPullback A n).isoPullback_hom_snd

@[simp] theorem laterCurveMap_zero : laterCurveMap A 0 = previousStrictι A := by
  have h := laterCurveMap_projection A 0
  simpa only [PlaneChartedScheme.toInitial_zero, Category.comp_id] using h

/-- Every one-step projection preserves the original whole curve map. -/
@[reassoc] theorem laterCurveMap_step (n : ℕ) :
    laterCurveMap A (n + 1) ≫ A.next.next.stepProjection n = laterCurveMap A n := by
  have h := laterCurveMap_eq_of_projection A n
    (laterCurveMap A (n + 1) ≫ A.next.next.stepProjection n)
    (𝟙 (previousStrictTransform A)) (by
      rw [Category.assoc, ← PlaneChartedScheme.toInitial_succ,
        laterCurveMap_projection, Category.id_comp])
  simpa only [Category.id_comp] using h

/-- The whole curve avoids the actual selected chart at every later stage. -/
theorem laterCurveMap_avoids_chart (n : ℕ) (z : previousStrictTransform A) :
    (laterCurveMap A n).base z ∉ Set.range (A.next.next.stage n).chart.base := by
  rintro ⟨p, hp⟩
  apply previousStrict_avoids_nextChart A z
  refine ⟨(stageProjection (k := k) n).base p, ?_⟩
  have h : ((A.next.next.stage n).chart ≫ A.next.next.toInitial n).base p =
      (laterCurveMap A n ≫ A.next.next.toInitial n).base z :=
    congrArg (A.next.next.toInitial n).base hp
  rw [PlaneChartedScheme.stage_chart_toInitial, laterCurveMap_projection] at h
  exact h

/-- None of the actual later selected rational centers is on the whole curve. -/
theorem laterCenter_not_on_curve (n : ℕ) :
    (A.next.next.stage n).chart.base (originPoint (k := k)) ∉
      Set.range (laterCurveMap A n).base := by
  rintro ⟨z, hz⟩
  exact laterCurveMap_avoids_chart A n z ⟨originPoint, hz.symm⟩

/-- The old whole curve avoids each newly created subsequent exceptional fiber. -/
theorem laterCurveMap_avoids_newFiber (n : ℕ) (z : previousStrictTransform A) :
    (laterCurveMap A (n + 1)).base z ∉
      Set.range (PointBlowupGluing.globalCenterFiberι (A.next.next.stage n).chart
        (originPoint (k := k)) (A.next.next.stage n).center_closed).base := by
  rw [PointBlowupGluing.range_globalCenterFiberι]
  intro h
  have he : (laterCurveMap A (n + 1) ≫ A.next.next.stepProjection n).base z =
      (A.next.next.stage n).chart.base (originPoint (k := k)) := h
  rw [laterCurveMap_step] at he
  exact laterCenter_not_on_curve A n ⟨z, he⟩

/-- This is disjointness of the actual closed images in the actual whole stage. -/
theorem laterCurve_disjoint_newFiber (n : ℕ) :
    Disjoint (Set.range (laterCurveMap A (n + 1)).base)
      (Set.range (PointBlowupGluing.globalCenterFiberι (A.next.next.stage n).chart
        (originPoint (k := k)) (A.next.next.stage n).center_closed).base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨z, rfl⟩ hz
  exact laterCurveMap_avoids_newFiber A n z hz

/-- The actual adjacent point on the old curve has a specified image in every later scheme. -/
def laterAdjacentPoint (n : ℕ) : (A.next.next.stage n).carrier :=
  (laterCurveMap A n).base (adjacentPoint A)

theorem laterAdjacentPoint_projection (n : ℕ) :
    (A.next.next.toInitial n).base (laterAdjacentPoint A n) =
      (previousStrictι A).base (adjacentPoint A) :=
  congrArg (fun f => f.base (adjacentPoint A)) (laterCurveMap_projection A n)

theorem laterAdjacentPoint_step (n : ℕ) :
    (A.next.next.stepProjection n).base (laterAdjacentPoint A (n + 1)) =
      laterAdjacentPoint A n :=
  congrArg (fun f => f.base (adjacentPoint A)) (laterCurveMap_step A n)

/-- Its original adjacent-fiber incidence is retained after every finite lift.
The target is explicitly the total inverse image of that original fiber. -/
theorem laterAdjacentPoint_mem_originalFiber_preimage (n : ℕ) :
    laterAdjacentPoint A n ∈ (A.next.next.toInitial n).base ⁻¹'
      Set.range (PointBlowupGluing.globalCenterFiberι A.next.chart
        (originPoint (k := k)) A.next.center_closed).base := by
  rw [Set.mem_preimage, laterAdjacentPoint_projection]
  exact adjacentPoint_mem_newFiber A

end KltDP.Examples.FrobeniusExceptionalLaterStages

import KltDP.Examples.FrobeniusContactTowerSelectedPoint
import KltDP.Examples.FrobeniusGraphPicardClassZeroFiber

/-!
# Fibres over non-selected points are unaffected by the contact blowups

The accepted finite-stage complement isomorphism (`FrobeniusStageComplement`) says that the
composite projection of the whole contact tower is an isomorphism over the complement of the
selected centre. This module draws the consequence for curves avoiding the centre.

Generic part (any `PlaneChartedScheme`): a morphism `f : Z ⟶ A.carrier` whose points avoid the
centre lifts to every stage; the lift is an actual categorical pullback of `f` along the stage
projection with identity second leg (so the scheme-theoretic preimage of `f` is `f` itself), it is
a closed immersion whenever `f` is, and its image lies in the stage puncture, hence away from all
exceptional curves.

Frobenius part (tower at the rational graph point `(a, a^p)`, `k` algebraically closed): the
horizontal fibre `y = c` for `c ≠ a^p` and the vertical fibre `x = c` for `c ≠ a` avoid the centre,
because the accepted product projections separate rational points (`point_injective`). Both are
closed immersions (sections of the proper projections) and are unaffected by every stage of the
tower in the above sense.

No fibre model, avoidance, lift, pullback or closedness statement is assumed. The private
restriction-lift helper of the accepted later-stage module is reproduced here verbatim because
private declarations are not importable.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusUnaffectedFibers

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusBlowupChartIteration
  FrobeniusGlobalBlowupStages FrobeniusGraphClosed FrobeniusGraphPicardClassZeroFiber
  FrobeniusTranslatedCharts FrobeniusStageComplement.PlaneChartedScheme
  FrobeniusContactTowerSelectedPoint

variable {k : Type u} [Field k]

/-- The actual restriction pullback determines a lift over an isomorphism open. -/
theorem eq_lift_over_restrict_iso {X Y Z : Scheme.{u}} (f : X ⟶ Y)
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

section Generic

variable (A : PlaneChartedScheme k) {Z : Scheme.{u}} (f : Z ⟶ A.carrier)
  (hf : ∀ z : Z, f.base z ≠ A.chart.base (originPoint (k := k)))

include hf

/-- A morphism avoiding the centre lands in the accepted centre complement. -/
theorem range_subset_initialPuncture :
    Set.range f.base ⊆ Set.range (initialPuncture A).ι.base := by
  rintro _ ⟨z, rfl⟩
  refine ⟨⟨f.base z, ?_⟩, rfl⟩
  change f.base z ≠ A.chart.base (originPoint (k := k))
  exact hf z

/-- The same morphism, factored through the centre complement. -/
def liftToPuncture : Z ⟶ (initialPuncture A).toScheme :=
  IsOpenImmersion.lift (initialPuncture A).ι f (range_subset_initialPuncture A f hf)

@[reassoc] theorem liftToPuncture_ι :
    liftToPuncture A f hf ≫ (initialPuncture A).ι = f :=
  IsOpenImmersion.lift_fac _ _ _

/-- The lift of `f` to the whole scheme after `n` blowups. -/
def stageLift (n : ℕ) : Z ⟶ (A.stage n).carrier :=
  liftToPuncture A f hf ≫ (stageComplementIso A n).inv ≫ (stagePuncture A n).ι

/-- Its projection is the original morphism. -/
@[reassoc] theorem stageLift_toInitial (n : ℕ) :
    stageLift A f hf n ≫ A.toInitial n = f := by
  rw [stageLift, Category.assoc, Category.assoc, ← stageComplementIso_hom_ι A n,
    Iso.inv_hom_id_assoc, liftToPuncture_ι]

/-- Morphisms over `f` lift uniquely. -/
theorem stageLift_eq_of_projection (n : ℕ) {W : Scheme.{u}}
    (h : W ⟶ (A.stage n).carrier) (q : W ⟶ Z) (w : h ≫ A.toInitial n = q ≫ f) :
    h = q ≫ stageLift A f hf n := by
  letI := toInitial_restrict_isIso A n
  have hw : (q ≫ liftToPuncture A f hf) ≫ (initialPuncture A).ι = h ≫ A.toInitial n := by
    rw [Category.assoc, liftToPuncture_ι]
    exact w.symm
  have he := eq_lift_over_restrict_iso (A.toInitial n) (initialPuncture A) h
    (q ≫ liftToPuncture A f hf) hw
  change h = q ≫ liftToPuncture A f hf ≫
    inv (A.toInitial n ∣_ initialPuncture A) ≫ (A.toInitial n ⁻¹ᵁ initialPuncture A).ι
  simpa only [Category.assoc] using he

/-- The lift is the literal scheme-theoretic inverse image of `f`: the fibre is unaffected. -/
theorem stageLift_isPullback (n : ℕ) :
    IsPullback (stageLift A f hf n) (𝟙 Z) (A.toInitial n) f := by
  have w : stageLift A f hf n ≫ A.toInitial n = (𝟙 Z) ≫ f := by
    rw [stageLift_toInitial, Category.id_comp]
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk w (fun s => s.snd)
    (fun s => (stageLift_eq_of_projection A f hf n s.fst s.snd s.condition).symm)
    (fun s => Category.comp_id s.snd)
    (fun s m _ hm => by simpa only [Category.comp_id] using hm))

/-- A closed curve avoiding the centre remains a closed curve at every stage. -/
theorem stageLift_isClosedImmersion (n : ℕ) [IsClosedImmersion f] :
    IsClosedImmersion (stageLift A f hf n) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (stageLift_isPullback A f hf n).flip inferInstance

/-- The lift lies in the stage puncture, hence away from every exceptional curve. -/
theorem stageLift_mem_stagePuncture (n : ℕ) (z : Z) :
    (stageLift A f hf n).base z ∈ stagePuncture A n := by
  change (A.toInitial n).base ((stageLift A f hf n).base z) ≠
    A.chart.base (originPoint (k := k))
  have h : (A.toInitial n).base ((stageLift A f hf n).base z) = f.base z := by
    change (stageLift A f hf n ≫ A.toInitial n).base z = f.base z
    rw [stageLift_toInitial]
  rw [h]
  exact hf z

end Generic

section Fibers

/-- The vertical fibre `x = c` of the product, with first coordinate the rational point `[1:c]`. -/
def verticalFiberMorphismAt (c : k) : projectiveSpace k 1 ⟶ projectiveProduct k :=
  pullback.lift (projectiveSpaceToSpec k 1 ≫ pointMorphism c) (𝟙 (projectiveSpace k 1))
    (by rw [Category.assoc, pointMorphism_over_base, Category.comp_id, Category.id_comp])

@[reassoc] theorem verticalFiberMorphismAt_fst (c : k) :
    verticalFiberMorphismAt c ≫ firstProjection =
      projectiveSpaceToSpec k 1 ≫ pointMorphism c :=
  pullback.lift_fst _ _ _

@[reassoc] theorem verticalFiberMorphismAt_snd (c : k) :
    verticalFiberMorphismAt c ≫ secondProjection = 𝟙 (projectiveSpace k 1) :=
  pullback.lift_snd _ _ _

instance firstProjection_isProper : IsProper (firstProjection (k := k)) :=
  MorphismProperty.pullback_fst (P := @IsProper)
    (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) inferInstance

instance secondProjection_isProper : IsProper (secondProjection (k := k)) :=
  MorphismProperty.pullback_snd (P := @IsProper)
    (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) inferInstance

/-- The horizontal fibre is a section of the separated first projection, hence closed. -/
instance horizontalFiberMorphism_isClosedImmersion (c : k) :
    IsClosedImmersion (horizontalFiberMorphism c) := by
  haveI : IsClosedImmersion (horizontalFiberMorphism c ≫ firstProjection) := by
    rw [horizontalFiberMorphism_fst]
    infer_instance
  exact IsClosedImmersion.of_comp (horizontalFiberMorphism c) firstProjection

instance verticalFiberMorphismAt_isClosedImmersion (c : k) :
    IsClosedImmersion (verticalFiberMorphismAt c) := by
  haveI : IsClosedImmersion (verticalFiberMorphismAt c ≫ secondProjection) := by
    rw [verticalFiberMorphismAt_snd]
    infer_instance
  exact IsClosedImmersion.of_comp (verticalFiberMorphismAt c) secondProjection

variable [IsAlgClosed k]

/-- The fibre `y = c` avoids the selected centre `(a, a^p)` when `c ≠ a^p`. -/
theorem horizontalFiber_avoids_center (p : ℕ) (a c : k) (hc : c ≠ a ^ p)
    (y : projectiveSpace k 1) :
    (horizontalFiberMorphism c).base y ≠
      (translatedInitial p a).chart.base (originPoint (k := k)) := by
  rw [selected_center]
  intro h
  apply hc
  apply point_injective
  have h2 := congrArg
    (pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base h
  rw [graphPoint_snd] at h2
  have h1 : (pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base
      ((horizontalFiberMorphism c).base y) = point c := by
    change (horizontalFiberMorphism c ≫ secondProjection).base y = point c
    rw [horizontalFiberMorphism_snd]
    change (pointMorphism c).base ((projectiveSpaceToSpec k 1).base y) = point c
    rw [Subsingleton.elim ((projectiveSpaceToSpec k 1).base y) (IsLocalRing.closedPoint k)]
    rfl
  exact h1.symm.trans h2

/-- The fibre `x = c` avoids the selected centre `(a, a^p)` when `c ≠ a`. -/
theorem verticalFiber_avoids_center (p : ℕ) (a c : k) (hc : c ≠ a)
    (y : projectiveSpace k 1) :
    (verticalFiberMorphismAt c).base y ≠
      (translatedInitial p a).chart.base (originPoint (k := k)) := by
  rw [selected_center]
  intro h
  apply hc
  apply point_injective
  have h2 := congrArg
    (pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base h
  rw [graphPoint_fst] at h2
  have h1 : (pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base
      ((verticalFiberMorphismAt c).base y) = point c := by
    change (verticalFiberMorphismAt c ≫ firstProjection).base y = point c
    rw [verticalFiberMorphismAt_fst]
    change (pointMorphism c).base ((projectiveSpaceToSpec k 1).base y) = point c
    rw [Subsingleton.elim ((projectiveSpaceToSpec k 1).base y) (IsLocalRing.closedPoint k)]
    rfl
  exact h1.symm.trans h2

/-- The unaffected horizontal fibre `y = c` in every stage of the tower at `(a, a^p)`. -/
def horizontalFiberLift (p : ℕ) (a c : k) (hc : c ≠ a ^ p) (n : ℕ) :
    projectiveSpace k 1 ⟶ selectedStage p a n :=
  stageLift (translatedInitial p a) (horizontalFiberMorphism c)
    (horizontalFiber_avoids_center p a c hc) n

@[reassoc] theorem horizontalFiberLift_projection (p : ℕ) (a c : k) (hc : c ≠ a ^ p) (n : ℕ) :
    horizontalFiberLift p a c hc n ≫ selectedProjection p a n = horizontalFiberMorphism c :=
  stageLift_toInitial _ _ _ n

theorem horizontalFiberLift_isPullback (p : ℕ) (a c : k) (hc : c ≠ a ^ p) (n : ℕ) :
    IsPullback (horizontalFiberLift p a c hc n) (𝟙 (projectiveSpace k 1))
      (selectedProjection p a n) (horizontalFiberMorphism c) :=
  stageLift_isPullback _ _ _ n

instance horizontalFiberLift_isClosedImmersion (p : ℕ) (a c : k) (hc : c ≠ a ^ p) (n : ℕ) :
    IsClosedImmersion (horizontalFiberLift p a c hc n) :=
  stageLift_isClosedImmersion _ _ _ n

theorem horizontalFiberLift_mem_puncture (p : ℕ) (a c : k) (hc : c ≠ a ^ p) (n : ℕ)
    (y : projectiveSpace k 1) :
    (horizontalFiberLift p a c hc n).base y ∈ stagePuncture (translatedInitial p a) n :=
  stageLift_mem_stagePuncture _ _ _ n y

/-- The unaffected vertical fibre `x = c` in every stage of the tower at `(a, a^p)`. -/
def verticalFiberLift (p : ℕ) (a c : k) (hc : c ≠ a) (n : ℕ) :
    projectiveSpace k 1 ⟶ selectedStage p a n :=
  stageLift (translatedInitial p a) (verticalFiberMorphismAt c)
    (verticalFiber_avoids_center p a c hc) n

@[reassoc] theorem verticalFiberLift_projection (p : ℕ) (a c : k) (hc : c ≠ a) (n : ℕ) :
    verticalFiberLift p a c hc n ≫ selectedProjection p a n = verticalFiberMorphismAt c :=
  stageLift_toInitial _ _ _ n

theorem verticalFiberLift_isPullback (p : ℕ) (a c : k) (hc : c ≠ a) (n : ℕ) :
    IsPullback (verticalFiberLift p a c hc n) (𝟙 (projectiveSpace k 1))
      (selectedProjection p a n) (verticalFiberMorphismAt c) :=
  stageLift_isPullback _ _ _ n

instance verticalFiberLift_isClosedImmersion (p : ℕ) (a c : k) (hc : c ≠ a) (n : ℕ) :
    IsClosedImmersion (verticalFiberLift p a c hc n) :=
  stageLift_isClosedImmersion _ _ _ n

theorem verticalFiberLift_mem_puncture (p : ℕ) (a c : k) (hc : c ≠ a) (n : ℕ)
    (y : projectiveSpace k 1) :
    (verticalFiberLift p a c hc n).base y ∈ stagePuncture (translatedInitial p a) n :=
  stageLift_mem_stagePuncture _ _ _ n y

end Fibers

end KltDP.Examples.FrobeniusUnaffectedFibers

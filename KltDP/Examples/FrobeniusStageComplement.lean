import KltDP.Examples.FrobeniusGlobalBlowupStages

/-!
# The finite global projection is an isomorphism off the original center

The coordinate substitution fixes the actual rational origin, so every
successive blowup center maps to the original center. Each one-step
projection is already proved to be an isomorphism off its actual center.
Restriction and composition of these actual isomorphisms give the result
for every finite global stage.

Reuse: the pinned `morphismRestrictRestrict`, `morphismRestrictEq` and
`morphismRestrict_comp` transport the existing one-step puncture isomorphism.
No target-complement isomorphism or center-image equality is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusStageComplement

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages

/-- An isomorphism over an actual open remains one over any smaller open. -/
theorem restrict_isIso_of_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U V : Y.Opens} (hUV : U ≤ V) [IsIso (f ∣_ V)] : IsIso (f ∣_ U) := by
  have hImage : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inter, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hUV]
  let e := morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U) ≪≫ morphismRestrictEq f hImage
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff e).mp
    (inferInstance : IsIso (f ∣_ V ∣_ V.ι ⁻¹ᵁ U))

variable {k : Type u} [Field k]

/-- The actual point-blowup chart substitution fixes the origin evaluation. -/
theorem originEvaluation_chartSubstitution :
    (originEvaluation (k := k)).comp chartSubstitution = originEvaluation := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [originEvaluation]
  · change originEvaluation (chartSubstitution (vCoord (k := k))) =
      originEvaluation vCoord
    rw [chartSubstitution_v, map_mul]
    simp [originEvaluation, uCoord, vCoord]

/-- The actual origin morphism maps to the origin under the chart projection. -/
@[reassoc] theorem originMorphism_coordinateBlowdown :
    originMorphism (k := k) ≫ coordinateBlowdown = originMorphism := by
  rw [coordinateBlowdown_eq, originMorphism, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, originEvaluation_chartSubstitution]

/-- The same statement holds for every actual finite chart composite. -/
@[reassoc] theorem originMorphism_stageProjection (n : ℕ) :
    originMorphism (k := k) ≫ stageProjection n = originMorphism := by
  induction n with
  | zero => exact Category.comp_id _
  | succ n ih =>
      rw [stageProjection_succ, ← Category.assoc, originMorphism_coordinateBlowdown, ih]

namespace PlaneChartedScheme

variable (A : PlaneChartedScheme k)

/-- Every actual center morphism projects to the original center morphism. -/
@[reassoc] theorem centerMorphism_toInitial (n : ℕ) :
    (A.stage n).centerMorphism ≫ A.toInitial n = A.centerMorphism := by
  rw [FrobeniusGlobalBlowupStages.PlaneChartedScheme.centerMorphism,
    Category.assoc, A.stage_chart_toInitial, ← Category.assoc,
    originMorphism_stageProjection]
  rfl

/-- In particular, this is equality of the actual underlying closed points. -/
theorem centerPoint_toInitial (n : ℕ) :
    (A.toInitial n).base ((A.stage n).chart.base (originPoint (k := k))) =
      A.chart.base (originPoint (k := k)) := by
  rw [← (A.stage n).centerMorphism_point, ← A.centerMorphism_point]
  exact congrArg fieldMorphismPoint (centerMorphism_toInitial A n)

/-- The complement of the actual original closed center. -/
def initialPuncture : A.carrier.Opens :=
  PointBlowupGluing.puncture A.chart originPoint A.center_closed

/-- Its actual inverse image in the entire `n`-th scheme. -/
def stagePuncture (n : ℕ) : (A.stage n).carrier.Opens :=
  A.toInitial n ⁻¹ᵁ (initialPuncture A)

/-- This inverse image avoids the actual next center, by the proved point image. -/
theorem stagePuncture_le_currentPuncture (n : ℕ) :
    (stagePuncture A n) ≤ (initialPuncture (A.stage n)) := by
  intro x hx
  change x ≠ (A.stage n).chart.base (originPoint (k := k))
  change (A.toInitial n).base x ≠ A.chart.base (originPoint (k := k)) at hx
  intro heq
  apply hx
  rw [heq]
  exact centerPoint_toInitial A n

/-- The previously constructed one-step puncture isomorphism has exactly
this restricted actual projection as its forward map. -/
theorem nextProjection_restrict_isIso :
    IsIso (A.nextProjection ∣_ (initialPuncture A)) := by
  letI : (originPoint (k := k)).asIdeal.IsMaximal :=
    FrobeniusBlowupChartIteration.centerIdeal_isMaximal
  change IsIso (PointBlowupGluing.projection A.chart originPoint A.center_closed ∣_
    PointBlowupGluing.puncture A.chart originPoint A.center_closed)
  rw [← PointBlowupGluing.punctureIso_hom]
  infer_instance

/-- Every finite global projection is an actual isomorphism over the
original center complement, including the complementary projective chart. -/
theorem toInitial_restrict_isIso (n : ℕ) :
    IsIso (A.toInitial n ∣_ (initialPuncture A)) := by
  induction n with
  | zero =>
      change IsIso ((𝟙 A.carrier) ∣_ (initialPuncture A))
      exact (morphismRestrict_id (initialPuncture A)).symm ▸
        (inferInstance : IsIso (𝟙 (initialPuncture A).toScheme))
  | succ n ih =>
      letI : IsIso (A.toInitial n ∣_ (initialPuncture A)) := ih
      letI : IsIso (A.stepProjection n ∣_ (initialPuncture (A.stage n))) := by
        change IsIso ((A.stage n).nextProjection ∣_ (initialPuncture (A.stage n)))
        exact nextProjection_restrict_isIso (A.stage n)
      have hStep : IsIso (A.stepProjection n ∣_ (stagePuncture A n)) :=
        restrict_isIso_of_le (A.stepProjection n) (stagePuncture_le_currentPuncture A n)
      letI : IsIso (A.stepProjection n ∣_ A.toInitial n ⁻¹ᵁ (initialPuncture A)) := hStep
      rw [A.toInitial_succ, morphismRestrict_comp]
      infer_instance

/-- The actual complement isomorphism for the entire finite-stage projection. -/
def stageComplementIso (n : ℕ) :
    (stagePuncture A n).toScheme ≅ (initialPuncture A).toScheme := by
  letI := toInitial_restrict_isIso A n
  exact asIso (A.toInitial n ∣_ (initialPuncture A))

theorem stageComplementIso_hom (n : ℕ) :
    (stageComplementIso A n).hom = A.toInitial n ∣_ (initialPuncture A) := rfl

/-- The displayed isomorphism retains the actual morphism to the original scheme. -/
@[reassoc] theorem stageComplementIso_hom_ι (n : ℕ) :
    (stageComplementIso A n).hom ≫ (initialPuncture A).ι =
      (stagePuncture A n).ι ≫ A.toInitial n :=
  morphismRestrict_ι _ _

end PlaneChartedScheme

end KltDP.Examples.FrobeniusStageComplement

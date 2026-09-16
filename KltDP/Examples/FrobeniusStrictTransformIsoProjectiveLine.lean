import KltDP.Geometry.IsoOfPunctureAndChart
import KltDP.Examples.FrobeniusStrictTransformStepProjection
import KltDP.Examples.FrobeniusStrictTransformStepPuncture
import KltDP.Examples.FrobeniusStrictTransformStageCover
import KltDP.Examples.FrobeniusStrictTransformContact
import KltDP.Geometry.PrimeCurveOfClosedImmersion
import KltDP.Examples.FrobeniusFiberPuncture
import KltDP.Examples.FrobeniusFiberPicard

/-!
# `B ≅ P¹` and `F̃ ≅ P¹` (BRIEF15, item 1)

The accepted step projections `strictStepProjection n m : B_{n+1} ⟶ B_n` and
`fiberStepProjection n : F̃_{n+1} ⟶ F̃_n` (the blowdown restricted to the strict transforms) are
isomorphisms (`strictStepProjection_isIso`, `fiberStepProjection_isIso`): by the generic
`isIso_of_pieces`, since over the centre complement they are the accepted isomorphisms
`strictStepOnPuncture` / `fiberStepOnPuncture`, over the chart they carry the accepted chart
parametrisation `residualChart (n+1) m` / `fiberResidualToClosure (n+1)` to the one of the next
stage (`residualChart_step`, `fiberResidualToClosure_step`), chart and puncture cover both curves
(accepted `strictTransform_chart_or_puncture`, `fiberClosure_chart_or_puncture`, with relative
closedness of the residual curve in the chart), and they are surjective (accepted).

At stage `0` the strict transforms are the graph (`strictTransformIdeal_zero`) and the horizontal
fibre (accepted `fiberStrictIdeal_zero`), both `≅ P¹`. Hence
`graphStrictIsoProjectiveLine n m : strictTransform n (m + n) ≅ P¹` and
`fiberStrictIsoProjectiveLine n : liftedFiberClosure n ≅ P¹`, compatible with the blowdown to
stage `0`: `iso.hom ≫ projectiveGraphMorphism (m + n) = strictTransformι ≫ projectiveContactProjection n`
and `iso.hom ≫ horizontalFiberMorphism 0 = fiberClosureInclusion ≫ projectiveContactProjection n`.
Bundle: `f29_strict_transforms_iso_projectiveLine`, with a universe check.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusStrictTransformIsoProjectiveLine

open KltDP.Geometry KltDP.Geometry.IsoOfPunctureAndChart KltDP.Geometry.SchematicImageToImageIso
open KltDP.Geometry.PrimeCurveOfClosedImmersion
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
open FrobeniusStrictTransformClosure FrobeniusGlobalStrictTransform
open FrobeniusStrictTransformStepProjection FrobeniusStrictTransformStepPuncture
open FrobeniusStrictTransformStageCover FrobeniusStrictTransformContact
open FrobeniusGraphClosed FrobeniusProjectiveMorphism FrobeniusProjectivePoints
open FrobeniusFiberPuncture FrobeniusFiberClosure FrobeniusFiberPicard
open FrobeniusGraphPicardClassZeroFiber
open FrobeniusStageComplement.PlaneChartedScheme

variable {k : Type u} [Field k]

/-- The `eqToHom` of equal ideal sheaves is compatible with the glued inclusions. -/
theorem gluedTo_eqToHom' {X : Scheme.{u}} (I J : X.IdealSheafData) (h : I = J) :
    eqToHom (congrArg (fun K : X.IdealSheafData => K.glueData.glued) h) ≫ J.gluedTo =
      I.gluedTo := by
  subst J
  exact Category.id_comp _

/-- A point of stage `n+1` in the stage puncture blows down into the centre complement of stage
`n`. -/
theorem mem_currentPuncture_of_mem_stagePuncture_succ (A : PlaneChartedScheme k) (n : ℕ)
    (x : (A.stage (n + 1)).carrier) (h : x ∈ stagePuncture A (n + 1)) :
    (A.stepProjection n).base x ∈ initialPuncture (A.stage n) := by
  have hx : (A.stepProjection n).base x ∈ stagePuncture A n := by
    change (A.toInitial n).base ((A.stepProjection n).base x) ∈ initialPuncture A
    rw [← Scheme.comp_base_apply]
    exact h
  exact stagePuncture_le_currentPuncture A n hx

/-! ## The strict transform of the graph -/

section Graph

/-- The strict transform is the closure of the residual curve. -/
theorem range_strictTransformι_eq_closure_residual (n m : ℕ) :
    Set.range (strictTransformι (k := k) n (m + n)).base =
      closure (Set.range ((projectiveProductInitial (k := k)).residualCurve n m).base) := by
  rw [← strictTransformIsoLocal_hom_ι n m, range_comp_base_of_isIso,
    range_closureInclusion_eq_residual]

/-- The chart parametrisations of consecutive strict transforms are compatible with the step. -/
theorem residualChart_step (n m : ℕ) :
    residualChart (k := k) (n + 1) m ≫ strictStepProjection n m = residualChart n (m + 1) := by
  apply (cancel_mono (strictTransformι (k := k) n ((m + 1) + n))).mp
  rw [Category.assoc, strictStepProjection_inclusion, ← Category.assoc, residualChart_ι,
    residualCurve_stepProjection, residualChart_ι]

/-- A point of the strict transform over the chart is on the residual chart. -/
theorem mem_range_residualChart_of_mem_chart (n m : ℕ) (x : strictTransform (k := k) n (m + n))
    (h : (strictTransformι (k := k) n (m + n)).base x ∈
      ((projectiveProductInitial (k := k)).stage n).chart.opensRange) :
    x ∈ Set.range (residualChart (k := k) n m).base := by
  have hcl : (strictTransformι (k := k) n (m + n)).base x ∈
      closure (Set.range ((projectiveProductInitial (k := k)).residualCurve n m).base) := by
    rw [← range_strictTransformι_eq_closure_residual]
    exact ⟨x, rfl⟩
  obtain ⟨t, ht⟩ := mem_range_comp_of_mem_closure (curveInPlane m)
    ((projectiveProductInitial (k := k)).stage n).chart _ hcl h
  refine ⟨t, (strictTransformι (k := k) n (m + n)).isClosedEmbedding.injective ?_⟩
  rw [← Scheme.comp_base_apply, residualChart_ι]
  exact ht

/-- The strict transform is covered by the residual chart and the centre complement. -/
theorem strictTransform_cover (n m : ℕ) (x : strictTransform (k := k) n (m + n)) :
    x ∈ Set.range (residualChart (k := k) n m).base ∨
      x ∈ strictTransformι (k := k) n (m + n) ⁻¹ᵁ currentPuncture n := by
  rcases strictTransform_chart_or_puncture n m ((strictTransformι n (m + n)).base x) ⟨x, rfl⟩
    with h | h
  · exact Or.inl (mem_range_residualChart_of_mem_chart n m x h)
  · exact Or.inr (stagePuncture_le_currentPuncture (projectiveProductInitial (k := k)) n h)

/-- The successor strict transform is covered by its residual chart and the inverse image of the
centre complement. -/
theorem strictTransform_cover_succ (n m : ℕ) (x : strictTransform (k := k) (n + 1) (m + (n + 1))) :
    x ∈ Set.range (residualChart (k := k) (n + 1) m).base ∨
      x ∈ strictTransformι (k := k) (n + 1) (m + (n + 1)) ⁻¹ᵁ
        ((projectiveProductInitial (k := k)).stepProjection n ⁻¹ᵁ currentPuncture n) := by
  rcases strictTransform_chart_or_puncture (n + 1) m
    ((strictTransformι (n + 1) (m + (n + 1))).base x) ⟨x, rfl⟩ with h | h
  · exact Or.inl (mem_range_residualChart_of_mem_chart (n + 1) m x h)
  · exact Or.inr (mem_currentPuncture_of_mem_stagePuncture_succ (projectiveProductInitial (k := k))
      n _ h)

/-- **The step projection of the strict transform of the graph is an isomorphism.** -/
instance strictStepProjection_isIso (n m : ℕ) : IsIso (strictStepProjection (k := k) n m) :=
  isIso_of_pieces (strictStepProjection n m) (strictTransformι (n + 1) (m + (n + 1)))
    (strictTransformι n ((m + 1) + n)) ((projectiveProductInitial (k := k)).stepProjection n)
    (strictStepProjection_inclusion n m) (currentPuncture n) (strictStepOnPuncture n m)
    (strictStepOnPuncture_ι n m) (residualChart (n + 1) m) (residualChart n (m + 1))
    (residualChart_step n m) (strictTransform_cover_succ n m) (strictTransform_cover n (m + 1))
    (strictStepProjection_surjective n m).surj

/-- At stage `0` the strict transform ideal is the kernel of the graph inclusion. -/
theorem strictTransformIdeal_zero (p : ℕ) :
    strictTransformIdeal (k := k) 0 p = (graphι (k := k) p).ker := by
  letI : IsIntegral (graph (k := k) p) := isIntegral_of_iso_projectiveLine (graphIsoProjectiveLine p)
  have h : wholeGraphLift (k := k) 0 p = (graphPuncture p).ι ≫ graphι p := by
    have h0 := wholeGraphLift_projection (k := k) 0 p
    rwa [show projectiveContactProjection (k := k) 0 = 𝟙 _ from rfl, Category.comp_id] at h0
  rw [strictTransformIdeal, h]
  exact SchematicImageDenseOpen.ker_precompose_open (graphPuncture p) (graphι p)

/-- **The stage-`0` strict transform is the graph.** -/
def strictTransformZeroIsoGraph (p : ℕ) : strictTransform (k := k) 0 p ≅ graph (k := k) p :=
  letI : IsIntegral (graph (k := k) p) := isIntegral_of_iso_projectiveLine (graphIsoProjectiveLine p)
  eqToIso (congrArg (fun I : (projectiveContactStage (k := k) 0).IdealSheafData =>
    I.glueData.glued) (strictTransformIdeal_zero p)) ≪≫ (toImageIso (graphι p)).symm

theorem strictTransformZeroIsoGraph_hom_ι (p : ℕ) :
    (strictTransformZeroIsoGraph p).hom ≫ graphι (k := k) p = strictTransformι 0 p := by
  letI : IsIntegral (graph (k := k) p) := isIntegral_of_iso_projectiveLine (graphIsoProjectiveLine p)
  rw [strictTransformZeroIsoGraph, Iso.trans_hom, eqToIso.hom, Iso.symm_hom, Category.assoc,
    toImageIso_inv_comp]
  exact gluedTo_eqToHom' _ _ (strictTransformIdeal_zero p)

/-- The graph inclusion through the projective line. -/
theorem graphι_eq_hom_comp (p : ℕ) :
    graphι (k := k) p = (graphIsoProjectiveLine p).hom ≫ projectiveGraphMorphism p := by
  rw [← graphIso_inv_ι, Iso.hom_inv_id_assoc]

/-- **`B_n ≅ P¹`**: the strict transform of the graph at stage `n` (residual exponent `m`,
Frobenius exponent `m + n`) is isomorphic to the projective line. -/
def graphStrictIsoProjectiveLine : (n m : ℕ) → strictTransform (k := k) n (m + n) ≅ projectiveSpace k 1
  | 0, m => strictTransformZeroIsoGraph (m + 0) ≪≫ graphIsoProjectiveLine (m + 0)
  | n + 1, m => asIso (strictStepProjection n m) ≪≫ graphStrictIsoProjectiveLine n (m + 1)

/-- The isomorphism is the blowdown to the graph of stage `0`. -/
theorem graphStrictIsoProjectiveLine_hom_comp : ∀ (n m : ℕ),
    (graphStrictIsoProjectiveLine (k := k) n m).hom ≫ projectiveGraphMorphism (m + n) =
      strictTransformι n (m + n) ≫ projectiveContactProjection n
  | 0, m => by
    rw [graphStrictIsoProjectiveLine, Iso.trans_hom, Category.assoc, ← graphι_eq_hom_comp,
      strictTransformZeroIsoGraph_hom_ι,
      show projectiveContactProjection (k := k) 0 = 𝟙 _ from rfl, Category.comp_id]
  | n + 1, m => by
    rw [graphStrictIsoProjectiveLine, Iso.trans_hom, asIso_hom, Category.assoc,
      show projectiveGraphMorphism (k := k) (m + (n + 1)) = projectiveGraphMorphism ((m + 1) + n)
        from congrArg _ (by omega),
      graphStrictIsoProjectiveLine_hom_comp n (m + 1), ← Category.assoc,
      strictStepProjection_inclusion, Category.assoc]
    rfl

end Graph

/-! ## The strict transform of the fibre -/

section Fiber

/-- The chart parametrisations of consecutive strict fibres are compatible with the step. -/
theorem fiberResidualToClosure_step (n : ℕ) :
    fiberResidualToClosure (projectiveProductInitial (k := k)) (n + 1) ≫ fiberStepProjection n =
      fiberResidualToClosure (projectiveProductInitial (k := k)) n := by
  apply (cancel_mono (fiberClosureInclusion (projectiveProductInitial (k := k)) n)).mp
  rw [Category.assoc, fiberStepProjection_inclusion, ← Category.assoc,
    fiberResidualToClosure_inclusion, fiberResidual_stepProjection, fiberResidualToClosure_inclusion]

/-- A point of the strict fibre over the chart is on the chart parametrisation. -/
theorem mem_range_fiberResidualToClosure_of_mem_chart (n : ℕ)
    (x : liftedFiberClosure (projectiveProductInitial (k := k)) n)
    (h : (fiberClosureInclusion (projectiveProductInitial (k := k)) n).base x ∈
      ((projectiveProductInitial (k := k)).stage n).chart.opensRange) :
    x ∈ Set.range (fiberResidualToClosure (projectiveProductInitial (k := k)) n).base := by
  have hcl : (fiberClosureInclusion (projectiveProductInitial (k := k)) n).base x ∈
      closure (Set.range (fiberResidual (projectiveProductInitial (k := k)) n).base) := by
    rw [← range_fiberClosureInclusion_eq_residual]
    exact ⟨x, rfl⟩
  obtain ⟨t, ht⟩ := mem_range_comp_of_mem_closure fiberCurve
    ((projectiveProductInitial (k := k)).stage n).chart _ hcl h
  refine ⟨t, (fiberClosureInclusion (projectiveProductInitial (k := k)) n).isClosedEmbedding.injective ?_⟩
  rw [← Scheme.comp_base_apply, fiberResidualToClosure_inclusion]
  exact ht

theorem liftedFiberClosure_cover (n : ℕ) (x : liftedFiberClosure (projectiveProductInitial (k := k)) n) :
    x ∈ Set.range (fiberResidualToClosure (projectiveProductInitial (k := k)) n).base ∨
      x ∈ fiberClosureInclusion (projectiveProductInitial (k := k)) n ⁻¹ᵁ currentPuncture n := by
  rcases fiberClosure_chart_or_puncture (projectiveProductInitial (k := k)) n
    ((fiberClosureInclusion (projectiveProductInitial (k := k)) n).base x) ⟨x, rfl⟩ with h | h
  · exact Or.inl (mem_range_fiberResidualToClosure_of_mem_chart n x h)
  · exact Or.inr (stagePuncture_le_currentPuncture (projectiveProductInitial (k := k)) n h)

theorem liftedFiberClosure_cover_succ (n : ℕ)
    (x : liftedFiberClosure (projectiveProductInitial (k := k)) (n + 1)) :
    x ∈ Set.range (fiberResidualToClosure (projectiveProductInitial (k := k)) (n + 1)).base ∨
      x ∈ fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1) ⁻¹ᵁ
        ((projectiveProductInitial (k := k)).stepProjection n ⁻¹ᵁ currentPuncture n) := by
  rcases fiberClosure_chart_or_puncture (projectiveProductInitial (k := k)) (n + 1)
    ((fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)).base x) ⟨x, rfl⟩
    with h | h
  · exact Or.inl (mem_range_fiberResidualToClosure_of_mem_chart (n + 1) x h)
  · exact Or.inr (mem_currentPuncture_of_mem_stagePuncture_succ (projectiveProductInitial (k := k))
      n _ h)

/-- **The step projection of the strict fibre is an isomorphism.** -/
instance fiberStepProjection_isIso (n : ℕ) : IsIso (fiberStepProjection (k := k) n) :=
  isIso_of_pieces (fiberStepProjection n)
    (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))
    (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
    ((projectiveProductInitial (k := k)).stepProjection n) (fiberStepProjection_inclusion n)
    (currentPuncture n) (fiberStepOnPuncture n) (fiberStepOnPuncture_ι n)
    (fiberResidualToClosure (projectiveProductInitial (k := k)) (n + 1))
    (fiberResidualToClosure (projectiveProductInitial (k := k)) n) (fiberResidualToClosure_step n)
    (liftedFiberClosure_cover_succ n) (liftedFiberClosure_cover n)
    (fiberStepProjection_surjective n).surj

/-- **The stage-`0` strict fibre is the horizontal fibre `≅ P¹`.** -/
def liftedFiberClosureZeroIso :
    liftedFiberClosure (projectiveProductInitial (k := k)) 0 ≅ projectiveSpace k 1 :=
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  eqToIso (congrArg (fun I : (projectiveContactStage (k := k) 0).IdealSheafData =>
    I.glueData.glued) fiberStrictIdeal_zero) ≪≫ (toImageIso (horizontalFiberMorphism (0 : k))).symm

theorem liftedFiberClosureZeroIso_hom :
    (liftedFiberClosureZeroIso (k := k)).hom ≫ horizontalFiberMorphism (0 : k) =
      fiberClosureInclusion (projectiveProductInitial (k := k)) 0 := by
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  rw [liftedFiberClosureZeroIso, Iso.trans_hom, eqToIso.hom, Iso.symm_hom, Category.assoc,
    toImageIso_inv_comp]
  exact gluedTo_eqToHom' _ _ fiberStrictIdeal_zero

/-- **`F̃_n ≅ P¹`**: the strict fibre at stage `n` is isomorphic to the projective line. -/
def fiberStrictIsoProjectiveLine :
    (n : ℕ) → liftedFiberClosure (projectiveProductInitial (k := k)) n ≅ projectiveSpace k 1
  | 0 => liftedFiberClosureZeroIso
  | n + 1 => asIso (fiberStepProjection n) ≪≫ fiberStrictIsoProjectiveLine n

/-- The isomorphism is the blowdown to the horizontal fibre of stage `0`. -/
theorem fiberStrictIsoProjectiveLine_hom_comp : ∀ n : ℕ,
    (fiberStrictIsoProjectiveLine (k := k) n).hom ≫ horizontalFiberMorphism (0 : k) =
      fiberClosureInclusion (projectiveProductInitial (k := k)) n ≫ projectiveContactProjection n
  | 0 => by
    rw [fiberStrictIsoProjectiveLine, liftedFiberClosureZeroIso_hom,
      show projectiveContactProjection (k := k) 0 = 𝟙 _ from rfl, Category.comp_id]
  | n + 1 => by
    rw [fiberStrictIsoProjectiveLine, Iso.trans_hom, asIso_hom, Category.assoc,
      fiberStrictIsoProjectiveLine_hom_comp n, ← Category.assoc, fiberStepProjection_inclusion,
      Category.assoc]
    rfl

end Fiber

end KltDP.Examples.FrobeniusStrictTransformIsoProjectiveLine

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform FrobeniusFiberClosure
  FrobeniusStrictTransformIsoProjectiveLine

/-- **The strict transforms of the graph and of the fibre are projective lines** at every stage
of the origin tower (`B_n` with Frobenius exponent `m + n`). -/
theorem f29_strict_transforms_iso_projectiveLine (k : Type u) [Field k] (n m : ℕ) :
    Nonempty (strictTransform (k := k) n (m + n) ≅ projectiveSpace k 1) ∧
    Nonempty (liftedFiberClosure (projectiveProductInitial (k := k)) n ≅ projectiveSpace k 1) :=
  ⟨⟨graphStrictIsoProjectiveLine n m⟩, ⟨fiberStrictIsoProjectiveLine n⟩⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_strict_transforms_iso_projectiveLine_universe_check (k : Type u) [Field k] (n m : ℕ) :
    True := by
  have _ := f29_strict_transforms_iso_projectiveLine.{u} k n m
  trivial

end KltDP.Examples

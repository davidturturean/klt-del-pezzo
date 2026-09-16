import KltDP.Examples.FrobeniusMultiCentreGraphFiber
import KltDP.Examples.FrobeniusTranslatedGraphCartierIdentity
import KltDP.Examples.FrobeniusStrictTransformIsoProjectiveLine
import KltDP.Examples.FrobeniusStrictTransformSmoothCurves
import KltDP.Geometry.SchematicImageToImageIso

/-!
# The original global strict graph is a projective line over its original field

The accepted strict-graph isomorphism in each origin tower and the original
translation square give compatible parametrizations in every selected tower.
They join through the actual defining fibre products of the multi-centre
surface. The resulting parametrization is a closed immersion because its
composite to the first ruling is identity. On the original isomorphism locus
it agrees with the original punctured-graph lift by uniqueness. Removing that
nonempty open does not alter its kernel, so its image is the independently
defined global strict graph.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusMultiCentreGraphProjectiveLine

open KltDP.Geometry KltDP.Geometry.ProjectiveLineTranslation KltDP.Geometry.SchematicImageToImageIso
  KltDP.Geometry.SchematicImageOpenBaseChange
open FrobeniusProjectiveMorphism FrobeniusProjectivePoints FrobeniusGraphClosed
  FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform FrobeniusTranslatedCharts
  FrobeniusContactTowerSelectedPoint FrobeniusTowerTransport
  FrobeniusTranslatedGraphCartierIdentity FrobeniusStrictTransformIsoProjectiveLine
  FrobeniusMultiCentreSurface FrobeniusMultiCentreGraphFiber
  FrobeniusStrictTransformSmoothCurves

variable {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The original selected-tower strict graph, parametrized by its original global first coordinate. -/
def selectedGraphParametrization (c : k) : projectiveSpace k 1 ⟶ selectedStage p c p :=
  (projectiveTranslationIso c).inv ≫ (graphStrictIsoProjectiveLine p 0).inv ≫
    strictTransformι p (0 + p) ≫ (stageTranslationIso p c p).hom

theorem selectedGraphParametrization_projection (c : k) :
    selectedGraphParametrization p c ≫ selectedProjection p c p = projectiveGraphMorphism p := by
  have ho : (graphStrictIsoProjectiveLine (k := k) p 0).inv ≫
      (strictTransformι p (0 + p) ≫ projectiveContactProjection p) =
      projectiveGraphMorphism p := by
    rw [← graphStrictIsoProjectiveLine_hom_comp, Iso.inv_hom_id_assoc, zero_add]
  simp only [selectedGraphParametrization, Category.assoc]
  rw [stageTranslationIso_hom_projection]
  rw [← Category.assoc (strictTransformι p (0 + p)),
    ← Category.assoc (graphStrictIsoProjectiveLine p 0).inv, ho,
    projectiveGraph_translation]
  change (projectiveTranslationIso c).inv ≫
    (projectiveTranslationIso c).hom ≫ projectiveGraphMorphism p = _
  rw [Iso.inv_hom_id_assoc]

private def graphParametrizationCone (p : ℕ) [Fact p.Prime] [CharP k p] :
    (n : ℕ) → (a : Fin n → k) →
    {f : projectiveSpace k 1 ⟶ multiSurface p n a // f ≫ multiProjection p n a =
      projectiveGraphMorphism p}
  | 0, a => ⟨projectiveGraphMorphism p, by exact Category.comp_id (projectiveGraphMorphism p)⟩
  | n + 1, a => by
    let c := graphParametrizationCone p n (fun i => a i.castSucc)
    have hc : c.val ≫ multiProjection p n (fun i => a i.castSucc) =
        selectedGraphParametrization p (a (Fin.last n)) ≫
          selectedProjection p (a (Fin.last n)) p :=
      c.property.trans (selectedGraphParametrization_projection p (a (Fin.last n))).symm
    refine ⟨pullback.lift c.val (selectedGraphParametrization p (a (Fin.last n))) hc, ?_⟩
    rw [multiProjection_succ]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ multiProjection p n (fun i => a i.castSucc))
        (pullback.lift_fst c.val (selectedGraphParametrization p (a (Fin.last n))) hc)).trans
          c.property)

/-- The compatible original tower parametrizations join in the original iterated fibre product. -/
def globalGraphParametrization (n : ℕ) (a : Fin n → k) :
    projectiveSpace k 1 ⟶ multiSurface p n a :=
  (graphParametrizationCone p n a).val

theorem globalGraphParametrization_projection (n : ℕ) (a : Fin n → k) :
    globalGraphParametrization p n a ≫ multiProjection p n a = projectiveGraphMorphism p :=
  (graphParametrizationCone p n a).property

instance globalGraphParametrization_isClosedImmersion (n : ℕ) (a : Fin n → k) :
    IsClosedImmersion (globalGraphParametrization p n a) := by
  haveI : IsClosedImmersion (globalGraphParametrization p n a ≫
      (multiProjection p n a ≫ firstProjection)) := by
    rw [← Category.assoc, globalGraphParametrization_projection, projectiveGraphMorphism_fst]
    infer_instance
  exact IsClosedImmersion.of_comp (globalGraphParametrization p n a)
    (multiProjection p n a ≫ firstProjection)

theorem globalGraphParametrization_structure (n : ℕ) (a : Fin n → k) :
    globalGraphParametrization p n a ≫ multiStructure p n a = projectiveSpaceToSpec k 1 := by
  change globalGraphParametrization p n a ≫
    (multiProjection p n a ≫ (firstProjection ≫ projectiveSpaceToSpec k 1)) = _
  rw [← Category.assoc, globalGraphParametrization_projection, ← Category.assoc,
    projectiveGraphMorphism_fst, Category.id_comp]

/-- The same actual map with the independently defined original graph as its source. -/
def wholeGraphLift (n : ℕ) (a : Fin n → k) : graph (k := k) p ⟶ multiSurface p n a :=
  (graphIsoProjectiveLine p).hom ≫ globalGraphParametrization p n a

instance wholeGraphLift_isClosedImmersion (n : ℕ) (a : Fin n → k) :
    IsClosedImmersion (wholeGraphLift p n a) := by
  unfold wholeGraphLift
  infer_instance

/-- On the original isomorphism locus the whole parametrization is the original punctured lift. -/
theorem wholeGraphLift_on_puncture (n : ℕ) (a : Fin n → k) :
    (FrobeniusMultiCentreGraphFiber.graphPuncture p n a).ι ≫ wholeGraphLift p n a =
      FrobeniusMultiCentreGraphFiber.graphLift p n a := by
  letI := multiProjection_restrict_centersComplement_isIso p n a
  have h := liftOverIso_eq_of_projection (multiProjection p n a)
    (centersComplement p n a) (puncturedGraph p n a) (puncturedGraph_range p n a)
    ((FrobeniusMultiCentreGraphFiber.graphPuncture p n a).ι ≫ wholeGraphLift p n a) (𝟙 _) (by
      rw [wholeGraphLift, Category.assoc, Category.assoc,
        globalGraphParametrization_projection, ← graphι_eq_hom_comp, Category.id_comp]
      rfl)
  simpa only [Category.id_comp] using h

variable [IsAlgClosed k]

/-- The whole original parametrization and the punctured lift have the same actual kernel. -/
theorem wholeGraphLift_ker (n : ℕ) (a : Fin n → k) :
    (wholeGraphLift p n a).ker = (FrobeniusMultiCentreGraphFiber.graphLift p n a).ker := by
  letI : IsIntegral (graph (k := k) p) :=
    PrimeCurveOfClosedImmersion.isIntegral_of_iso_projectiveLine (graphIsoProjectiveLine p)
  letI := graphPuncture_nonempty p n a
  rw [← wholeGraphLift_on_puncture]
  exact (SchematicImageDenseOpen.ker_precompose_open
    (FrobeniusMultiCentreGraphFiber.graphPuncture p n a) (wholeGraphLift p n a)).symm

/-- The original global strict graph is the original projective line. -/
def globalGraphIsoProjectiveLine (n : ℕ) (a : Fin n → k) :
    graphStrict p n a ≅ projectiveSpace k 1 := by
  letI : IsIntegral (graph (k := k) p) :=
    PrimeCurveOfClosedImmersion.isIntegral_of_iso_projectiveLine (graphIsoProjectiveLine p)
  exact imageIsoOfKerEq (FrobeniusMultiCentreGraphFiber.graphLift p n a) (wholeGraphLift p n a)
      (wholeGraphLift_ker p n a).symm ≪≫
    (toImageIso (wholeGraphLift p n a)).symm ≪≫ graphIsoProjectiveLine p

/-- Its inverse parametrizes the independently constructed original graph inclusion. -/
theorem globalGraphIsoProjectiveLine_hom_inclusion (n : ℕ) (a : Fin n → k) :
    (globalGraphIsoProjectiveLine p n a).hom ≫ globalGraphParametrization p n a =
      graphStrictι p n a := by
  letI : IsIntegral (graph (k := k) p) :=
    PrimeCurveOfClosedImmersion.isIntegral_of_iso_projectiveLine (graphIsoProjectiveLine p)
  simp only [globalGraphIsoProjectiveLine, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  change (imageIsoOfKerEq (FrobeniusMultiCentreGraphFiber.graphLift p n a) (wholeGraphLift p n a)
      (wholeGraphLift_ker p n a).symm).hom ≫
    (toImageIso (wholeGraphLift p n a)).inv ≫ wholeGraphLift p n a = _
  rw [toImageIso_inv_comp, imageIsoOfKerEq_hom_inclusion]

/-- The global graph isomorphism respects its original field structure. -/
theorem globalGraphIsoProjectiveLine_hom_structure (n : ℕ) (a : Fin n → k) :
    (globalGraphIsoProjectiveLine p n a).hom ≫ projectiveSpaceToSpec k 1 =
      graphStrictι p n a ≫ multiStructure p n a := by
  rw [← globalGraphParametrization_structure p n a, ← Category.assoc,
    globalGraphIsoProjectiveLine_hom_inclusion]

theorem globalGraph_isSmooth (n : ℕ) (a : Fin n → k) :
    IsSmooth (graphStrictι p n a ≫ multiStructure p n a) := by
  rw [← globalGraphIsoProjectiveLine_hom_structure p n a]
  letI : IsSmooth (projectiveSpaceToSpec k 1) := projectiveLine_isSmooth
  infer_instance

end KltDP.Examples.FrobeniusMultiCentreGraphProjectiveLine

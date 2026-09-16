import KltDP.Examples.FrobeniusGlobalStrictTransform
import KltDP.Examples.FrobeniusGraphPicardClassFrames
import KltDP.Geometry.ReducedClosedImageChart
import KltDP.Compatibility.SchemeTwoOpenCoverIso
import KltDP.Geometry.SchemeConormalSourceIso
import KltDP.Geometry.SchemeConormalOpenImmersion
import KltDP.Geometry.SchemeKernelOpenPullback
import KltDP.Geometry.SchemeInvertibleSheafPullback

/-!
# The original strict-transform kernel away from the original center

The whole punctured projective graph is the actual pullback of the
original strict-transform inclusion to the stage puncture. Its source
isomorphism with the literal open restriction gives a comparison of the
original categorical kernels, preserving their structure-module inclusions.

The original projective graph kernel is transported through its proved
source isomorphism, the original open restriction, and the actual stage
complement isomorphism. Both kernel comparisons retain the canonical unit
maps. Thus the original strict kernel is invertible on the stage puncture
for every field and every pair of natural stage/residual exponents.

No whole-stage invertibility, exceptional multiplicity, tensor
factorization, or strict-transform class formula is asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusStrictTransformPunctureKernel

open KltDP.Geometry
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusGraphClosed FrobeniusProjectiveMorphism FrobeniusGraphPicardClassFrames
open FrobeniusStageComplement.PlaneChartedScheme

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

/-- The original whole-graph factorization retains both actual ambient maps. -/
@[reassoc] theorem wholeGraphToStrictTransform_puncture_ι (n m : ℕ) :
    wholeGraphToStrictTransform (k := k) n (m + n) ≫ strictTransformι n (m + n) =
      wholeGraphIntoStagePuncture n (m + n) ≫
        (stagePuncture (projectiveProductInitial (k := k)) n).ι := by
  simpa only [wholeGraphIntoStagePuncture, wholeGraphLift, Category.assoc] using
    wholeGraphToStrictTransform_ι (k := k) n (m + n)

/-- This is an actual open chart of the original reduced closed strict transform. -/
instance wholeGraphToStrictTransform_isOpenImmersion (n m : ℕ) :
    IsOpenImmersion (wholeGraphToStrictTransform (k := k) n (m + n)) := by
  letI : IsIntegral (strictTransform (k := k) n (m + n)) :=
    strictTransform_isIntegral n m
  apply ReducedClosedImageChart.isOpenImmersion_of_reduced_closed_image
    (wholeGraphIntoStagePuncture n (m + n))
    (stagePuncture (projectiveProductInitial (k := k)) n).ι
    (strictTransformι n (m + n)) (wholeGraphToStrictTransform n (m + n))
  · exact wholeGraphToStrictTransform_puncture_ι n m
  · simpa only [wholeGraphIntoStagePuncture, wholeGraphLift, Category.assoc] using
      range_strictTransformι (k := k) n (m + n)

/-- Its range is precisely the inverse image of the actual stage puncture. -/
theorem range_wholeGraphToStrictTransform (n m : ℕ) :
    Set.range (wholeGraphToStrictTransform (k := k) n (m + n)).base =
      (strictTransformι n (m + n)).base ⁻¹'
        Set.range (stagePuncture (projectiveProductInitial (k := k)) n).ι.base := by
  let c := wholeGraphIntoStagePuncture (k := k) n (m + n)
  let j := (stagePuncture (projectiveProductInitial (k := k)) n).ι
  let f := wholeGraphToStrictTransform (k := k) n (m + n)
  let i := strictTransformι (k := k) n (m + n)
  have hw : f ≫ i = c ≫ j := wholeGraphToStrictTransform_puncture_ι n m
  have hr : Set.range i.base = closure (Set.range (c ≫ j).base) := by
    simpa only [c, j, i, wholeGraphIntoStagePuncture, wholeGraphLift,
      Category.assoc] using range_strictTransformι (k := k) n (m + n)
  change Set.range f.base = i.base ⁻¹' Set.range j.base
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨c.base t, congrArg (fun h => h.base t) hw.symm⟩
  · rintro ⟨a, ha⟩
    have hmem : a ∈ j.base ⁻¹' closure (Set.range (c ≫ j).base) := by
      change j.base a ∈ closure (Set.range (c ≫ j).base)
      rw [ha, ← hr]
      exact ⟨z, rfl⟩
    rw [ReducedClosedImageChart.preimage_closure_range c j] at hmem
    obtain ⟨t, ht⟩ := hmem
    refine ⟨t, i.isClosedEmbedding.injective ?_⟩
    change (f ≫ i).base t = i.base z
    rw [hw]
    exact (congrArg j.base ht).trans ha

/-- The punctured graph is the actual scheme pullback of the original inclusion. -/
theorem strictTransform_puncture_isPullback (n m : ℕ) :
    IsPullback (wholeGraphIntoStagePuncture (k := k) n (m + n))
      (wholeGraphToStrictTransform n (m + n))
      (stagePuncture (projectiveProductInitial (k := k)) n).ι
      (strictTransformι n (m + n)) :=
  (KltDP.SchemeTwoOpenGluing.isPullback_of_range
    (wholeGraphToStrictTransform (k := k) n (m + n))
    (wholeGraphIntoStagePuncture n (m + n)) (strictTransformι n (m + n))
    (stagePuncture (projectiveProductInitial (k := k)) n).ι
    (wholeGraphToStrictTransform_puncture_ι n m)
    (range_wholeGraphToStrictTransform n m)).flip

/-- Pullback uniqueness identifies the source with the literal open restriction. -/
def graphPunctureStrictOpenIso (n m : ℕ) :
    (graphPuncture (k := k) (m + n)).toScheme ≅
      (strictTransformι n (m + n) ⁻¹ᵁ
        stagePuncture (projectiveProductInitial (k := k)) n).toScheme :=
  (strictTransform_puncture_isPullback n m).isoIsPullback _ _
    (isPullback_morphismRestrict (strictTransformι n (m + n))
      (stagePuncture (projectiveProductInitial (k := k)) n))

@[reassoc] theorem graphPunctureStrictOpenIso_hom_restrict (n m : ℕ) :
    (graphPunctureStrictOpenIso (k := k) n m).hom ≫
        (strictTransformι n (m + n) ∣_
          stagePuncture (projectiveProductInitial (k := k)) n) =
      wholeGraphIntoStagePuncture n (m + n) := by
  simp only [graphPunctureStrictOpenIso, IsPullback.isoIsPullback_hom_fst]

@[reassoc] theorem graphPunctureStrictOpenIso_hom_ι (n m : ℕ) :
    (graphPunctureStrictOpenIso (k := k) n m).hom ≫
        (strictTransformι n (m + n) ⁻¹ᵁ
          stagePuncture (projectiveProductInitial (k := k)) n).ι =
      wholeGraphToStrictTransform n (m + n) := by
  simp only [graphPunctureStrictOpenIso, IsPullback.isoIsPullback_hom_snd]

/-- Transport of a kernel through an equality of source morphisms preserves the inclusion. -/
private theorem kernel_eqToIso_hom_ι {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (eqToIso (congrArg schemeKernelIdeal h)).hom ≫ schemeKernelIdealι g =
      schemeKernelIdealι f := by
  subst g
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]

/-- Generic form of the puncture kernel comparison: an open-restriction source isomorphism
together with the local-to-global kernel comparison, for abstract `f`, `U`, `e`, `w`. -/
private def kernelPunctureIsoOf {X Y W : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (e : W ≅ (f ⁻¹ᵁ U).toScheme) (w : W ⟶ U.toScheme) (h : e.hom ≫ (f ∣_ U) = w) :
    schemeKernelIdeal w ≅ (schemeModulePullback U.ι).obj (schemeKernelIdeal f) :=
  eqToIso (congrArg schemeKernelIdeal h.symm) ≪≫ schemeKernelPrecompIso e (f ∣_ U) ≪≫
    localKernelToGlobalPullbackIso f U

private theorem kernelPunctureIsoOf_inclusion {X Y W : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (e : W ≅ (f ⁻¹ᵁ U).toScheme) (w : W ⟶ U.toScheme) (h : e.hom ≫ (f ∣_ U) = w) :
    (kernelPunctureIsoOf f U e w h).hom ≫ pulledKernelInclusion f U.ι =
      schemeKernelIdealι w := by
  subst h
  simp only [kernelPunctureIsoOf, Iso.trans_hom, Category.assoc,
    localKernelToGlobalPullbackIso_inclusion, schemeKernelPrecompIso_hom_ι, eqToIso_refl,
    Iso.refl_hom, Category.id_comp]

/-- The actual punctured-graph kernel identifies the original global strict kernel. Its type
is `schemeKernelIdeal (wholeGraphIntoStagePuncture n (m + n)) ≅
(schemeModulePullback (stagePuncture projectiveProductInitial n).ι).obj
(schemeKernelIdeal (strictTransformι n (m + n)))`, stated through the generic construction so
that the ambient stage is written uniformly. -/
def strictKernelPunctureIso (n m : ℕ) :=
  kernelPunctureIsoOf (strictTransformι (k := k) n (m + n))
    (stagePuncture (projectiveProductInitial (k := k)) n) (graphPunctureStrictOpenIso n m)
    (wholeGraphIntoStagePuncture n (m + n)) (graphPunctureStrictOpenIso_hom_restrict n m)

/-- The comparison preserves the original strict-kernel inclusion and canonical unit. -/
theorem strictKernelPunctureIso_inclusion (n m : ℕ) :
    (strictKernelPunctureIso (k := k) n m).hom ≫
        pulledKernelInclusion (strictTransformι n (m + n))
          (stagePuncture (projectiveProductInitial (k := k)) n).ι =
      schemeKernelIdealι (wholeGraphIntoStagePuncture n (m + n)) :=
  kernelPunctureIsoOf_inclusion _ _ _ _ _

private def closedGraphKernelIso (p : ℕ) :
    schemeKernelIdeal (projectiveGraphMorphism (k := k) p) ≅ schemeKernelIdeal (graphι p) :=
  eqToIso (congrArg schemeKernelIdeal (graphIso_inv_ι p).symm) ≪≫
    schemeKernelPrecompIso (graphIsoProjectiveLine p).symm (graphι p)

private theorem closedGraphKernelIso_inclusion (p : ℕ) :
    (closedGraphKernelIso (k := k) p).hom ≫ schemeKernelIdealι (graphι p) =
      schemeKernelIdealι (projectiveGraphMorphism p) := by
  simp only [closedGraphKernelIso, Iso.trans_hom, Category.assoc,
    schemeKernelPrecompIso_hom_ι]
  exact kernel_eqToIso_hom_ι (graphIso_inv_ι p).symm

private def originalGraphOpenKernelIso (p : ℕ) :
    (schemeModulePullback (initialPuncture (projectiveProductInitial (k := k))).ι).obj
        (schemeKernelIdeal (projectiveGraphMorphism p)) ≅
      schemeKernelIdeal (graphι p ∣_ initialPuncture (projectiveProductInitial (k := k))) :=
  (schemeModulePullback (initialPuncture (projectiveProductInitial (k := k))).ι).mapIso
      (closedGraphKernelIso p) ≪≫
    (localKernelToGlobalPullbackIso (graphι p)
      (initialPuncture (projectiveProductInitial (k := k)))).symm

private theorem originalGraphOpenKernelIso_inclusion (p : ℕ) :
    (originalGraphOpenKernelIso (k := k) p).hom ≫
        schemeKernelIdealι
          (graphι p ∣_ initialPuncture (projectiveProductInitial (k := k))) =
      pulledKernelInclusion (projectiveGraphMorphism p)
        (initialPuncture (projectiveProductInitial (k := k))).ι := by
  rw [originalGraphOpenKernelIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, ← localKernelToGlobalPullbackIso_inclusion (graphι p)
      (initialPuncture (projectiveProductInitial (k := k))), Iso.inv_hom_id_assoc]
  rw [pulledKernelInclusion, pulledKernelInclusion, ← Category.assoc, ← Functor.map_comp,
    closedGraphKernelIso_inclusion]

private theorem puncturedGraph_complementIso (n p : ℕ) :
    wholeGraphIntoStagePuncture (k := k) n p ≫
        (stageComplementIso (projectiveProductInitial (k := k)) n).hom =
      graphι p ∣_ initialPuncture (projectiveProductInitial (k := k)) := by
  simp only [wholeGraphIntoStagePuncture, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- Generic transport of a kernel comparison through an open immersion of the ambient scheme,
for abstract `a`, `f`, `g`, `O`, `u`. -/
private def transportedKernelIsoOf {Y Z W : Scheme.{u}} (a : Y ⟶ Z) [IsOpenImmersion a]
    (f : W ⟶ Y) {g : W ⟶ Z} (hg : g = f ≫ a) {M : Z.Modules} (O : M ≅ schemeKernelIdeal g) :
    (schemeModulePullback a).obj M ≅ schemeKernelIdeal f :=
  (schemeModulePullback a).mapIso (O ≪≫ eqToIso (congrArg schemeKernelIdeal hg)) ≪≫
    schemeKernelPostcompOpenIso f a

private theorem transportedKernelIsoOf_inclusion {Y Z W : Scheme.{u}} (a : Y ⟶ Z)
    [IsOpenImmersion a] (f : W ⟶ Y) {g : W ⟶ Z} (hg : g = f ≫ a) {M : Z.Modules}
    (O : M ≅ schemeKernelIdeal g) (u : M ⟶ _root_.SheafOfModules.unit Z.ringCatSheaf)
    (hO : O.hom ≫ schemeKernelIdealι g = u) :
    (transportedKernelIsoOf a f hg O).hom ≫ schemeKernelIdealι f =
      (schemeModulePullback a).map u ≫ (schemeModulePullbackUnitIso a).hom := by
  subst hO
  subst hg
  simp only [transportedKernelIsoOf, Iso.trans_hom, Functor.mapIso_hom, eqToIso_refl,
    Iso.refl_hom, Category.comp_id, Category.assoc, schemeKernelPostcompOpenIso_hom_ι,
    Functor.map_comp]

/-- Transport the original graph kernel through the original complement isomorphism. -/
def originalGraphKernelPunctureIso (n p : ℕ) :
    (schemeModulePullback (stageComplementIso (projectiveProductInitial (k := k)) n).hom).obj
        ((schemeModulePullback (initialPuncture (projectiveProductInitial (k := k))).ι).obj
          (schemeKernelIdeal (projectiveGraphMorphism p))) ≅
      schemeKernelIdeal (wholeGraphIntoStagePuncture n p) :=
  transportedKernelIsoOf (stageComplementIso (projectiveProductInitial (k := k)) n).hom
    (wholeGraphIntoStagePuncture n p) (puncturedGraph_complementIso n p).symm
    (originalGraphOpenKernelIso p)

/-- Both original unit comparisons are retained under transport of the graph ideal. -/
theorem originalGraphKernelPunctureIso_inclusion (n p : ℕ) :
    (originalGraphKernelPunctureIso (k := k) n p).hom ≫
        schemeKernelIdealι (wholeGraphIntoStagePuncture n p) =
      (schemeModulePullback (stageComplementIso (projectiveProductInitial (k := k)) n).hom).map
          (pulledKernelInclusion (projectiveGraphMorphism p)
            (initialPuncture (projectiveProductInitial (k := k))).ι) ≫
        (schemeModulePullbackUnitIso
          (stageComplementIso (projectiveProductInitial (k := k)) n).hom).hom :=
  transportedKernelIsoOf_inclusion _ _ _ _ _ (originalGraphOpenKernelIso_inclusion p)

/-- The original strict kernel is invertible on the whole original-center complement. -/
theorem strictKernel_stagePuncture_isInvertible (n m : ℕ) :
    KltDP.SheafOfModules.IsInvertible
      (R := (stagePuncture (projectiveProductInitial (k := k)) n).toScheme.ringCatSheaf)
      ((schemeModulePullback (stagePuncture (projectiveProductInitial (k := k)) n).ι).obj
        (schemeKernelIdeal (strictTransformι n (m + n)))) := by
  have h := schemeModulePullback_isInvertible
    (stageComplementIso (projectiveProductInitial (k := k)) n).hom _
    (schemeModulePullback_isInvertible
      (initialPuncture (projectiveProductInitial (k := k))).ι _
      (graphKernel_isInvertible (k := k) (m + n)))
  exact (KltDP.SheafOfModules.isInvertible_iff_of_iso
    (R := (stagePuncture (projectiveProductInitial (k := k)) n).toScheme.ringCatSheaf)
    (originalGraphKernelPunctureIso n (m + n) ≪≫ strictKernelPunctureIso n m)).mp h

end KltDP.Examples.FrobeniusStrictTransformPunctureKernel

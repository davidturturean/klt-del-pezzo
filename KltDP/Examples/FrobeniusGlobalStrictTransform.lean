import KltDP.Examples.FrobeniusStrictTransformClosure
import KltDP.Examples.FrobeniusStageComplement
import KltDP.Geometry.SchematicImageOpenImmersion
import KltDP.Geometry.ProjectiveSpaceIntegral

/-!
# The strict transform of the whole original projective graph

Remove the original center from the actual closed projective graph, lift
this entire open subscheme through the proved finite-stage complement
isomorphism, and take its actual kernel subscheme in the entire stage.
The punctured affine graph is proved to be a nonempty open immersion into
that source. Its lift is the previously constructed punctured residual
curve, by the actual pullback square for the restricted projection.
Consequently the two kernel ideal sheaves are equal.

This identifies the previously computed local closure with the schematic
strict transform defined from the whole original graph off the center.
It does not assert divisor classes, intersection numbers or contractions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusGlobalStrictTransform

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
open FrobeniusGlobalGraphCompatibility FrobeniusGraphClosed FrobeniusProjectiveMorphism
open FrobeniusStrictTransformClosure FrobeniusStageComplement
open FrobeniusStageComplement.PlaneChartedScheme

variable {k : Type u} [Field k]

/-- The actual open of the whole closed graph lying outside the original center. -/
def graphPuncture (p : ℕ) : (graph (k := k) p).Opens :=
  graphι p ⁻¹ᵁ (initialPuncture (projectiveProductInitial (k := k)))

/-- The actual punctured polynomial chart inside the whole closed graph. -/
def puncturedGraphChart (p : ℕ) :
    (parameterPuncture (k := k)).toScheme ⟶ graph (k := k) p :=
  parameterPuncture.ι ≫ ProjectiveLineComparison.polynomialChartMap k 0 ≫ lineToGraph p

private theorem lineToGraph_isIso (p : ℕ) : IsIso (lineToGraph (k := k) p) := by
  change IsIso (graphIsoProjectiveLine p).inv
  infer_instance

instance puncturedGraphChart_isOpenImmersion (p : ℕ) :
    IsOpenImmersion (puncturedGraphChart (k := k) p) := by
  letI := lineToGraph_isIso (k := k) p
  unfold puncturedGraphChart
  infer_instance

/-- The actual chart map followed by the closed graph inclusion is the
punctured monomial curve in the original product-plane chart. -/
@[reassoc] theorem puncturedGraphChart_graphι (p : ℕ) :
    puncturedGraphChart (k := k) p ≫ graphι p =
      parameterPuncture.ι ≫ (curveInPlane p ≫ (projectiveProductInitial (k := k)).chart) := by
  rw [puncturedGraphChart, Category.assoc, Category.assoc, lineToGraph_ι,
    ← curveInPlane_productChart]
  rfl

/-- The punctured affine graph lies in the actual complement of the original center. -/
theorem puncturedGraphChart_range (p : ℕ) :
    Set.range (puncturedGraphChart (k := k) p).base ⊆ Set.range (graphPuncture p).ι.base := by
  rintro _ ⟨q, rfl⟩
  refine ⟨⟨(puncturedGraphChart p).base q, ?_⟩, rfl⟩
  change (puncturedGraphChart p ≫ graphι p).base q ≠
    (projectiveProductInitial (k := k)).chart.base (originPoint (k := k))
  rw [puncturedGraphChart_graphι]
  exact puncturedResidualCurve_ne_center projectiveProductInitial 0 p q

/-- The actual open-immersion factorization through the whole punctured graph. -/
def parameterToGraphPuncture (p : ℕ) :
    (parameterPuncture (k := k)).toScheme ⟶ (graphPuncture (k := k) p).toScheme :=
  IsOpenImmersion.lift (graphPuncture p).ι (puncturedGraphChart p)
    (puncturedGraphChart_range p)

@[reassoc] theorem parameterToGraphPuncture_ι (p : ℕ) :
    parameterToGraphPuncture (k := k) p ≫ (graphPuncture p).ι = puncturedGraphChart p :=
  IsOpenImmersion.lift_fac _ _ _

instance parameterToGraphPuncture_isOpenImmersion (p : ℕ) :
    IsOpenImmersion (parameterToGraphPuncture (k := k) p) := by
  letI : IsOpenImmersion (parameterToGraphPuncture (k := k) p ≫ (graphPuncture p).ι) := by
    rw [parameterToGraphPuncture_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ (graphPuncture p).ι

instance graphPuncture_nonempty (p : ℕ) : Nonempty (graphPuncture (k := k) p) :=
  ⟨(parameterToGraphPuncture p).base (Classical.choice inferInstance)⟩

/-- Integrality of the whole source comes from the proved projective-line
isomorphism and the actual nonempty open, not from its local equations alone. -/
instance graphPuncture_isIntegral (p : ℕ) : IsIntegral (graphPuncture (k := k) p).toScheme := by
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  letI : Nonempty (graph (k := k) p) :=
    ⟨(graphIsoProjectiveLine (k := k) p).inv.base (Classical.choice inferInstance)⟩
  letI : IsIntegral (graph (k := k) p) :=
    isIntegral_of_isOpenImmersion (graphIsoProjectiveLine (k := k) p).hom
  exact isIntegral_of_isOpenImmersion (graphPuncture p).ι

/-- The actual whole punctured graph is Noetherian: it is an open
subscheme of the proved projective-line model. -/
instance graphPuncture_noetherianSpace (p : ℕ) :
    TopologicalSpace.NoetherianSpace (graphPuncture (k := k) p).toScheme := by
  letI := projectiveSpace_noetherianSpace k 1
  exact ((graphPuncture (k := k) p).ι ≫
    (graphIsoProjectiveLine (k := k) p).hom).isOpenEmbedding.isInducing.noetherianSpace

/-- The inverse image of the whole punctured graph inside the actual
stage complement, obtained by transporting its closed inclusion through
the proved complement isomorphism. -/
def wholeGraphIntoStagePuncture (n p : ℕ) :
    (graphPuncture (k := k) p).toScheme ⟶
      (stagePuncture (projectiveProductInitial (k := k)) n).toScheme :=
  (graphι p ∣_ (initialPuncture (projectiveProductInitial (k := k)))) ≫
    (stageComplementIso (projectiveProductInitial (k := k)) n).inv

instance wholeGraphIntoStagePuncture_isClosedImmersion (n p : ℕ) :
    IsClosedImmersion (wholeGraphIntoStagePuncture (k := k) n p) := by
  letI : IsClosedImmersion (graphι p ∣_ (initialPuncture (projectiveProductInitial (k := k)))) :=
    IsLocalAtTarget.restrict (graphι_isClosedImmersion p) _
  unfold wholeGraphIntoStagePuncture
  infer_instance

/-- The transported subscheme is the actual pullback of the original
closed graph on the center complement, by an actual categorical square. -/
theorem wholeGraphIntoStagePuncture_isPullback (n p : ℕ) :
    IsPullback (wholeGraphIntoStagePuncture (k := k) n p)
      (𝟙 (graphPuncture p).toScheme)
      (stageComplementIso (projectiveProductInitial (k := k)) n).hom
      (graphι p ∣_ (initialPuncture (projectiveProductInitial (k := k)))) := by
  apply IsPullback.of_vert_isIso
  constructor
  simp only [wholeGraphIntoStagePuncture, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, Category.id_comp]

/-- The whole original graph off the center lifts through the actual
finite-stage complement isomorphism into the entire current scheme. -/
def wholeGraphLift (n p : ℕ) :
    (graphPuncture (k := k) p).toScheme ⟶ projectiveContactStage (k := k) n :=
  (graphι p ∣_ (initialPuncture (projectiveProductInitial (k := k)))) ≫
    (stageComplementIso (projectiveProductInitial (k := k)) n).inv ≫
      (stagePuncture (projectiveProductInitial (k := k)) n).ι

/-- This is a lift of the original actual graph inclusion on its entire punctured open. -/
@[reassoc] theorem wholeGraphLift_projection (n p : ℕ) :
    wholeGraphLift (k := k) n p ≫ projectiveContactProjection n =
      (graphPuncture p).ι ≫ graphι p := by
  rw [wholeGraphLift, Category.assoc, Category.assoc]
  change (graphι p ∣_ (initialPuncture (projectiveProductInitial (k := k)))) ≫
    (stageComplementIso (projectiveProductInitial (k := k)) n).inv ≫
      ((stagePuncture (projectiveProductInitial (k := k)) n).ι ≫
        (projectiveProductInitial (k := k)).toInitial n) = _
  rw [← FrobeniusStageComplement.PlaneChartedScheme.stageComplementIso_hom_ι,
    Iso.inv_hom_id_assoc, morphismRestrict_ι]
  rfl

/-- Pullback uniqueness determines every lift over an open where the actual
projection is an isomorphism. This uses the actual restriction square. -/
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

/-- On the punctured affine chart, the whole-graph lift is exactly the
actual residual-curve lift already constructed through the Rees charts. -/
theorem parameterToGraphPuncture_wholeGraphLift (n m : ℕ) :
    parameterToGraphPuncture (k := k) (m + n) ≫ wholeGraphLift n (m + n) =
      puncturedResidualCurve projectiveProductInitial n m := by
  let A := projectiveProductInitial (k := k)
  letI := toInitial_restrict_isIso A n
  let q := parameterToGraphPuncture (k := k) (m + n) ≫
    (graphι (m + n) ∣_ (initialPuncture A))
  have w : q ≫ (initialPuncture A).ι =
      puncturedResidualCurve A n m ≫ A.toInitial n := by
    dsimp only [q]
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc]
    change (parameterToGraphPuncture (k := k) (m + n) ≫
        (graphPuncture (k := k) (m + n)).ι) ≫ graphι (m + n) =
      puncturedResidualCurve A n m ≫ A.toInitial n
    rw [parameterToGraphPuncture_ι, puncturedGraphChart_graphι,
      puncturedResidualCurve, Category.assoc, A.residualCurve_toInitial]
  have h := eq_lift_over_restrict_iso (A.toInitial n) (initialPuncture A)
    (puncturedResidualCurve A n m) q w
  simpa only [wholeGraphLift, q, A,
    FrobeniusStageComplement.PlaneChartedScheme.stageComplementIso,
    asIso_inv, Category.assoc] using h.symm

/-- The actual schematic strict-transform ideal of the whole projective graph. -/
def strictTransformIdeal (n p : ℕ) : (projectiveContactStage (k := k) n).IdealSheafData :=
  (wholeGraphLift n p).ker

/-- The whole original graph and the punctured local graph define the same
actual closed subscheme at every stage with the specified residual exponent. -/
theorem strictTransformIdeal_eq_local (n m : ℕ) :
    strictTransformIdeal (k := k) n (m + n) =
      liftedGraphClosureIdeal projectiveProductInitial n m := by
  rw [strictTransformIdeal, liftedGraphClosureIdeal,
    ← parameterToGraphPuncture_wholeGraphLift]
  exact (SchematicImageOpenImmersion.ker_precompose_openImmersion
    (parameterToGraphPuncture (m + n)) (wholeGraphLift n (m + n))).symm

/-- The actual global strict-transform scheme, formed from the entire
original graph minus the original center. -/
abbrev strictTransform (n p : ℕ) : Scheme.{u} :=
  (strictTransformIdeal (k := k) n p).glueData.glued

abbrev strictTransformι (n p : ℕ) :
    strictTransform (k := k) n p ⟶ projectiveContactStage (k := k) n :=
  (strictTransformIdeal n p).gluedTo

instance strictTransformι_isClosedImmersion (n p : ℕ) :
    IsClosedImmersion (strictTransformι (k := k) n p) :=
  (strictTransformIdeal n p).gluedTo_isClosedImmersion

/-- The actual strict-transform inclusion has range equal to the closure
of the lift of the entire original graph off the center. -/
theorem range_strictTransformι (n p : ℕ) :
    Set.range (strictTransformι (k := k) n p).base =
      closure (Set.range (wholeGraphLift n p).base) := by
  rw [Scheme.IdealSheafData.range_gluedTo]
  exact Scheme.Hom.support_ker (wholeGraphLift n p)

/-- The whole punctured graph factors through the actual strict transform. -/
def wholeGraphToStrictTransform (n p : ℕ) :
    (graphPuncture (k := k) p).toScheme ⟶ strictTransform (k := k) n p :=
  SchematicImageGlued.toImage (wholeGraphLift n p)

@[reassoc] theorem wholeGraphToStrictTransform_ι (n p : ℕ) :
    wholeGraphToStrictTransform (k := k) n p ≫ strictTransformι n p = wholeGraphLift n p :=
  SchematicImageGlued.toImage_inclusion _

/-- In the actual contact range, the whole strict transform is integral
by its proved equality with the computed integral local closure. -/
instance strictTransform_isIntegral (n m : ℕ) :
    IsIntegral (strictTransform (k := k) n (m + n)) := by
  change IsIntegral (strictTransformIdeal (k := k) n (m + n)).glueData.glued
  rw [strictTransformIdeal_eq_local]
  exact liftedGraphClosure_isIntegral projectiveProductInitial n m

/-- The actual global strict transform equals the previously computed
local graph closure as a scheme, by the proved ideal-sheaf equality. -/
def strictTransformIsoLocal (n m : ℕ) :
    strictTransform (k := k) n (m + n) ≅
      liftedGraphClosure (projectiveProductInitial (k := k)) n m :=
  eqToIso (congrArg (fun I : (projectiveContactStage (k := k) n).IdealSheafData =>
    I.glueData.glued) (strictTransformIdeal_eq_local n m))

private theorem gluedTo_eqToHom {X : Scheme.{u}} (I J : X.IdealSheafData) (h : I = J) :
    eqToHom (congrArg (fun K : X.IdealSheafData => K.glueData.glued) h) ≫ J.gluedTo =
      I.gluedTo := by
  subst J
  exact Category.id_comp _

/-- The scheme isomorphism preserves the actual closed inclusions in the stage. -/
@[reassoc] theorem strictTransformIsoLocal_hom_ι (n m : ℕ) :
    (strictTransformIsoLocal (k := k) n m).hom ≫
      closureInclusion projectiveProductInitial n m = strictTransformι n (m + n) :=
  gluedTo_eqToHom _ _ (strictTransformIdeal_eq_local n m)

end KltDP.Examples.FrobeniusGlobalStrictTransform

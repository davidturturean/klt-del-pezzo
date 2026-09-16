import KltDP.Examples.FrobeniusTranslatedCharts
import KltDP.Examples.FrobeniusGlobalBlowupSmooth
import KltDP.Examples.FrobeniusStageComplement
import KltDP.Examples.FrobeniusGraphRationalPoints

/-!
# The whole contact-blowup tower at a selected rational graph point

The accepted `FrobeniusTranslatedCharts.translatedInitial p a` equips the actual projective
product with the translated polynomial-plane chart centred at the rational graph point
`(a, a^p)`. The accepted generic recursion `PlaneChartedScheme.stage` then produces the entire
scheme after `n` successive point blowups along the contact chain at that point. This module
names the resulting tower and derives, for every selected parameter `a`:

* the composite projection `selectedProjection p a n` to the product and its properness;
* properness and smoothness of relative dimension two of every stage over `k`, from the
  accepted product instances and the accepted stage-preservation theorems;
* the centre of the tower is the accepted point `graphPoint p a`, it is closed, every stage
  centre projects to it, and distinct `a` give distinct centres (algebraically closed `k`);
* in characteristic `p` the residual curve of every stage with accumulated exponent `p`
  projects onto the whole closed Frobenius graph (accepted `translatedResidualCurve_toGraph`);
* the finite projection is an isomorphism away from the centre (accepted complement isomorphism).

Nothing here is assumed: every statement specialises an accepted theorem about an arbitrary
`PlaneChartedScheme` to the accepted translated initial data. No class, intersection number or
multi-centre surface is asserted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusContactTowerSelectedPoint

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusBlowupChartIteration
  FrobeniusGlobalBlowupStages FrobeniusGlobalBlowupSmooth FrobeniusTranslatedCharts
  FrobeniusStageComplement.PlaneChartedScheme

variable {k : Type u} [Field k]

/-- The whole scheme after `n` contact blowups at the selected graph point `(a, a^p)`. -/
abbrev selectedStage (p : ℕ) (a : k) (n : ℕ) : Scheme.{u} :=
  ((translatedInitial p a).stage n).carrier

/-- Its composite projection to the actual projective product. -/
def selectedProjection (p : ℕ) (a : k) (n : ℕ) :
    selectedStage p a n ⟶ projectiveProduct k :=
  (translatedInitial p a).toInitial n

instance selectedProjection_isProper (p : ℕ) (a : k) (n : ℕ) :
    IsProper (selectedProjection p a n) :=
  (translatedInitial p a).toInitial_isProper n

/-- The translated initial data has the accepted proper product structure morphism. -/
instance translatedInitial_structure_isProper (p : ℕ) (a : k) :
    IsProper (translatedInitial (k := k) p a).structureMap :=
  projectiveProductInitial_structure_isProper

instance selectedStage_structure_isProper (p : ℕ) (a : k) (n : ℕ) :
    IsProper ((translatedInitial (k := k) p a).stage n).structureMap :=
  (translatedInitial p a).stageStructure_isProper n

/-- The translated initial data has the accepted smooth product structure morphism. -/
instance translatedInitial_structure_smoothTwo (p : ℕ) (a : k) :
    IsSmoothOfRelativeDimension 2 (translatedInitial (k := k) p a).structureMap :=
  projectiveProduct_structure_smoothTwo

/-- Every stage of the tower at `(a, a^p)` is smooth of relative dimension two over `k`. -/
instance selectedStage_structure_smoothTwo (p : ℕ) (a : k) (n : ℕ) :
    IsSmoothOfRelativeDimension 2 ((translatedInitial (k := k) p a).stage n).structureMap :=
  ExplicitStages.stageStructure_smoothTwo (translatedInitial p a) n

instance selectedStage_structure_smooth (p : ℕ) (a : k) (n : ℕ) :
    IsSmooth ((translatedInitial (k := k) p a).stage n).structureMap :=
  IsSmoothOfRelativeDimension.isSmooth 2 _

/-- The projection is compatible with the structure morphisms over `k`. -/
theorem selectedProjection_structure (p : ℕ) (a : k) (n : ℕ) :
    selectedProjection p a n ≫ projectiveProductToSpec =
      ((translatedInitial (k := k) p a).stage n).structureMap :=
  (translatedInitial p a).toInitial_structure n

/-- The centre of the tower is the accepted rational graph point `(a, a^p)`. -/
theorem selected_center (p : ℕ) (a : k) :
    (translatedInitial p a).chart.base (originPoint (k := k)) = graphPoint p a :=
  translatedInitial_centerPoint p a

theorem selected_center_isClosed (p : ℕ) (a : k) :
    IsClosed ({graphPoint p a} : Set (projectiveProduct k)) :=
  graphPoint_isClosed p a

/-- Every stage centre projects to the selected graph point. -/
theorem selectedStage_center_projection (p : ℕ) (a : k) (n : ℕ) :
    (selectedProjection p a n).base
        (((translatedInitial p a).stage n).chart.base (originPoint (k := k))) =
      graphPoint p a :=
  (centerPoint_toInitial (translatedInitial p a) n).trans (selected_center p a)

/-- The finite projection is an isomorphism over the complement of the selected point. -/
def selectedComplementIso (p : ℕ) (a : k) (n : ℕ) :
    (stagePuncture (translatedInitial p a) n).toScheme ≅
      (initialPuncture (translatedInitial p a)).toScheme :=
  stageComplementIso (translatedInitial p a) n

theorem selectedComplementIso_hom (p : ℕ) (a : k) (n : ℕ) :
    (selectedComplementIso p a n).hom =
      selectedProjection p a n ∣_ initialPuncture (translatedInitial p a) :=
  rfl

/-- The residual curve of the stage with accumulated exponent `p` projects onto the whole
closed Frobenius graph, with translated parameter. -/
theorem selectedResidualCurve_toGraph (p : ℕ) [Fact p.Prime] [CharP k p] (a : k)
    (n m : ℕ) (hm : m + n = p) :
    (translatedInitial p a).residualCurve n m ≫ selectedProjection p a n =
      (parameterTranslationIso a).hom ≫
        ProjectiveLineComparison.polynomialChartMap k 0 ≫
          FrobeniusProjectiveMorphism.projectiveGraphMorphism p :=
  translatedResidualCurve_toGraph p a n m hm

/-- Before the contact is exhausted, the next centre lies on the residual curve. -/
theorem selected_center_on_residualCurve (p : ℕ) (a : k) (n m : ℕ) (hm : 0 < m) :
    parameterOriginMorphism (k := k) ≫ (translatedInitial p a).residualCurve n m =
      ((translatedInitial p a).stage n).centerMorphism :=
  (translatedInitial p a).parameterOrigin_residualCurve n m hm

/-- Distinct selected parameters give distinct centres. -/
theorem selected_centers_injective [IsAlgClosed k] (p : ℕ) :
    Function.Injective (β := projectiveProduct k) (fun a : k =>
      (translatedInitial p a).chart.base (originPoint (k := k))) :=
  translatedInitial_centers_injective p

end KltDP.Examples.FrobeniusContactTowerSelectedPoint

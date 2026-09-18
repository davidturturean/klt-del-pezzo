import KltDP.Geometry.LinearSystemMatrixDomainCover
import KltDP.Geometry.PullbackSectionCoherence

/-!
# The original matrix square identifies the actual pulled section tuples

The original commuting-square pullback isomorphism followed by the pullback
of the specific degree-one comparison carries every actual matrix section
to the pullback of its original section combination.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemMatrixMorphism

open InvertibleSectionNonvanishingOpen ProjectiveSpaceDegreeOneSheaf

variable {k : Type u} [Field k] {X : Scheme.{u}} (L : InvertibleSheaf X)
  {n : ℕ} (s : Fin (n + 1) → L.obj.sections) (f : X ⟶ Spec (CommRingCat.of k))
  (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤)
  {m : ℕ} (a : Fin (m + 1) → Fin (n + 1) → k)
  {T : Scheme.{u}} (v : T ⟶ X) (w : T ⟶ (ProjectiveLinearForms.domain k n a).toScheme)
  (hsq : v ≫ LinearSystemMorphism.morphism L s f hcover =
    w ≫ (ProjectiveLinearForms.domain k n a).ι)

/-- The actual pullback comparison induced by the original matrix square. -/
def pulledCombinationIso :
    (pullbackInvertibleSheaf w
      (pullbackInvertibleSheaf (ProjectiveLinearForms.domain k n a).ι (degreeOne k n))).obj ≅
        (pullbackInvertibleSheaf v L).obj :=
  PullbackSectionCoherence.commutingSquareIso w (ProjectiveLinearForms.domain k n a).ι
    v (LinearSystemMorphism.morphism L s f hcover) hsq.symm (degreeOne k n).obj ≪≫
      (schemeModulePullback v).mapIso (LinearSystemPullback.pullbackDegreeOneIso L s f hcover)

/-- This specific comparison preserves the original matrix combination sections. -/
theorem pulledCombinationIso_sectionsMap (j : Fin (m + 1)) :
    _root_.SheafOfModules.sectionsMap (pulledCombinationIso L s f hcover a v w hsq).hom
      (InvertibleSheafSectionPowersPullback.pullbackSection w
        (pullbackInvertibleSheaf (ProjectiveLinearForms.domain k n a).ι (degreeOne k n)).obj
        (InvertibleSheafSectionPowersPullback.pullbackSection
          (ProjectiveLinearForms.domain k n a).ι (degreeOne k n).obj
          (ProjectiveLinearForms.formSection k n (a j)))) =
      InvertibleSheafSectionPowersPullback.pullbackSection v L.obj
        (combinationSections L s f a j) := by
  change _root_.SheafOfModules.sectionsMap
    ((PullbackSectionCoherence.commutingSquareIso w (ProjectiveLinearForms.domain k n a).ι
      v (LinearSystemMorphism.morphism L s f hcover) hsq.symm (degreeOne k n).obj).hom ≫
        (schemeModulePullback v).map (LinearSystemPullback.pullbackDegreeOneIso L s f hcover).hom)
      _ = _
  refine (_root_.SheafOfModules.sectionsMap_comp _ _ _).trans ?_
  refine (congrArg (_root_.SheafOfModules.sectionsMap ((schemeModulePullback v).map
      (LinearSystemPullback.pullbackDegreeOneIso L s f hcover).hom))
    (PullbackSectionCoherence.commutingSquareIso_sectionsMap w
      (ProjectiveLinearForms.domain k n a).ι v (LinearSystemMorphism.morphism L s f hcover)
      hsq.symm (degreeOne k n).obj (ProjectiveLinearForms.formSection k n (a j)))).trans ?_
  refine (pullbackSection_sectionsMap v (LinearSystemPullback.pullbackDegreeOneIso L s f hcover).hom
    (InvertibleSheafSectionPowersPullback.pullbackSection (LinearSystemMorphism.morphism L s f hcover)
      (degreeOne k n).obj (ProjectiveLinearForms.formSection k n (a j)))).trans ?_
  exact congrArg (InvertibleSheafSectionPowersPullback.pullbackSection v L.obj)
    (LinearSystemMatrixSections.pullbackDegreeOneIso_formSection L s f hcover (a j))

end KltDP.Geometry.LinearSystemMatrixMorphism

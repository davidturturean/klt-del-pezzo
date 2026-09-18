import KltDP.Geometry.LinearSystemDegreeOnePullbackSections
import KltDP.Geometry.SectionLinearCombinationsPullback
import KltDP.Geometry.ProjectiveLinearForms
import KltDP.Geometry.LinearSystemIsoCoordinates
import KltDP.Geometry.InvertibleSectionNonvanishingPullback

/-!
# Original projective linear forms recover the original section combinations

The specific degree-one pullback isomorphism sends each pulled homogeneous
section to the original supplied section. The proved pullback and morphism
compatibility of finite combinations then identifies every original linear
form. Its nonvanishing open gives the exact inverse image of the original
matrix domain, with no scalar or section-compatibility premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemMatrixSections

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSectionNonvanishingOpen SectionLinearCombinations
  ProjectiveSpaceDegreeOneSheaf LinearSystemMorphism LinearSystemPullback

variable {k : Type u} [Field k] {X : Scheme.{u}} (L : InvertibleSheaf X)
  {n : ℕ} (s : Fin (n + 1) → L.obj.sections) (f : X ⟶ Spec (CommRingCat.of k))
  (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤)

/-- The specific original degree-one comparison carries a pulled linear form
to the corresponding combination of the original compatible sections. -/
theorem pullbackDegreeOneIso_formSection (a : Fin (n + 1) → k) :
    _root_.SheafOfModules.sectionsMap (pullbackDegreeOneIso L s f hcover).hom
      (InvertibleSheafSectionPowersPullback.pullbackSection (morphism L s f hcover)
        (degreeOne k n).obj (ProjectiveLinearForms.formSection k n a)) =
      combination f L.obj s a := by
  let g := morphism L s f hcover
  let P := (degreeOne k n).obj
  let N := (schemeModulePullback g).obj P
  let e := pullbackDegreeOneIso L s f hcover
  let t := fun j => InvertibleSheafSectionPowersPullback.pullbackSection
    g P (homogeneousSection k n j)
  have ht : (fun j => _root_.SheafOfModules.sectionsMap e.hom (t j)) = s :=
    funext (fun j => pullbackDegreeOneIso_homogeneousSection L s f hcover j)
  calc
    _ = _root_.SheafOfModules.sectionsMap e.hom
        (combination (g ≫ projectiveSpaceToSpec k n) N t a) :=
      congrArg (_root_.SheafOfModules.sectionsMap e.hom)
        (pullbackSection_combination (projectiveSpaceToSpec k n) g P
          (homogeneousSection k n) a)
    _ = _root_.SheafOfModules.sectionsMap e.hom (combination f N t a) :=
      congrArg (fun q : X ⟶ Spec (CommRingCat.of k) =>
        _root_.SheafOfModules.sectionsMap e.hom (combination q N t a))
          (morphism_structure L s f hcover)
    _ = combination f L.obj (fun j => _root_.SheafOfModules.sectionsMap e.hom (t j)) a :=
      sectionsMap_combination f e.hom t a
    _ = _ := congrArg (fun v : Fin (n + 1) → L.obj.sections => combination f L.obj v a) ht

/-- The original form's nonvanishing open pulls back to the original combination's open. -/
theorem preimage_formSection_nonvanishingOpen (a : Fin (n + 1) → k) :
    morphism L s f hcover ⁻¹ᵁ
      nonvanishingOpen (projectiveSpace k n) (degreeOne k n)
        (ProjectiveLinearForms.formSection k n a) =
      nonvanishingOpen X L (combination f L.obj s a) := by
  let g := morphism L s f hcover
  let b := InvertibleSheafSectionPowersPullback.pullbackSection
    g (degreeOne k n).obj (ProjectiveLinearForms.formSection k n a)
  calc
    _ = nonvanishingOpen X (pullbackInvertibleSheaf g (degreeOne k n)) b :=
      (InvertibleSectionNonvanishingPullback.nonvanishingOpen_pullback
        g (degreeOne k n) (ProjectiveLinearForms.formSection k n a)).symm
    _ = nonvanishingOpen X L
        (_root_.SheafOfModules.sectionsMap (pullbackDegreeOneIso L s f hcover).hom b) :=
      (LinearSystemNaturality.nonvanishingOpen_sectionsMap_iso
        (pullbackInvertibleSheaf g (degreeOne k n)) L
        (pullbackDegreeOneIso L s f hcover) b).symm
    _ = _ := congrArg (nonvanishingOpen X L) (pullbackDegreeOneIso_formSection L s f hcover a)

/-- The original matrix domain has exactly the non-base open of the actual section combinations
as its inverse image under the original linear-system map. -/
theorem preimage_matrixDomain {m : ℕ} (a : Fin (m + 1) → Fin (n + 1) → k) :
    morphism L s f hcover ⁻¹ᵁ ProjectiveLinearForms.domain k n a =
      LinearSystemRationalMap.nonBaseOpen L (fun j => combination f L.obj s (a j)) :=
  ((morphism L s f hcover).preimage_iSup (fun j =>
    nonvanishingOpen (projectiveSpace k n) (degreeOne k n)
      (ProjectiveLinearForms.formSection k n (a j)))).trans
        (iSup_congr (fun j => preimage_formSection_nonvanishingOpen L s f hcover (a j)))

end KltDP.Geometry.LinearSystemMatrixSections

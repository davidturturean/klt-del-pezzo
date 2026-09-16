import KltDP.Examples.FrobeniusMultiCentreFiberIdealIso
import KltDP.Examples.FrobeniusMultiCentreExceptionalDegreeTransport
import KltDP.Examples.FrobeniusTowerTransportCurves
import KltDP.Examples.FrobeniusFiberFirstFiberDegree
import KltDP.Examples.FrobeniusStrictTransformSmoothCurves

/-!
# The original global strict fibres are projective lines over the original field

The actual strict fibre is the previously proved base change of its original
translated-tower fibre. That entire fibre lies in the tower projection's
isomorphism open, so the actual pullback projection is an isomorphism.
The accepted translation isomorphism and origin-tower fibre isomorphism then
give the global result, including its original field structure.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusMultiCentreFiberProjectiveLine

open KltDP.Geometry
open FrobeniusProjectiveMorphism FrobeniusProjectivePoints FrobeniusGraphClosed
  FrobeniusGlobalBlowupStages FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint
  FrobeniusFiberClosure FrobeniusTowerTransport FrobeniusTowerTransportCurves
  FrobeniusMultiCentreSurface FrobeniusMultiCentreGraphFiber
  FrobeniusMultiCentreFiberIdeal FrobeniusMultiCentreFiberIdealIso
  FrobeniusMultiCentreExceptionalDegreeTransport FrobeniusStrictTransformIsoProjectiveLine
  FrobeniusStrictTransformFiberRows FrobeniusStrictTransformSmoothCurves
  FrobeniusFiberFirstFiberDegree FrobeniusGraphPicardClassZeroFiber

variable {k : Type u} [Field k]

/-- The accepted origin strict-fibre isomorphism commutes with the original field maps. -/
theorem originFiberIso_hom_structure (m : ℕ) :
    (fiberStrictIsoProjectiveLine (k := k) m).hom ≫ projectiveSpaceToSpec k 1 =
      fiberClosureInclusion (projectiveProductInitial (k := k)) m ≫
        ((projectiveProductInitial (k := k)).stage m).structureMap := by
  have hbase : horizontalFiberMorphism (0 : k) ≫ projectiveProductToSpec =
      projectiveSpaceToSpec k 1 := by
    change horizontalFiberMorphism (0 : k) ≫ (firstProjection ≫ projectiveSpaceToSpec k 1) = _
    rw [← Category.assoc, horizontalFiberMorphism_fst, Category.id_comp]
  rw [← hbase, ← Category.assoc,
    fiberStrictIsoProjectiveLine_hom_comp, Category.assoc]
  congr 1
  exact projectiveContactProjection_structureMap m

/-- The original translated strict fibre, via the proved translation of the origin fibre. -/
def translatedFiberIsoProjectiveLine (p : ℕ) (c : k) (m : ℕ) :
    liftedFiberClosure (translatedInitial p c) m ≅ projectiveSpace k 1 :=
  (fiberClosureTranslationIso p c m).symm ≪≫ fiberStrictIsoProjectiveLine m

theorem translatedFiberIso_hom_structure (p : ℕ) (c : k) (m : ℕ) :
    (translatedFiberIsoProjectiveLine p c m).hom ≫ projectiveSpaceToSpec k 1 =
      fiberClosureInclusion (translatedInitial p c) m ≫
        ((translatedInitial p c).stage m).structureMap := by
  have ht : (fiberClosureTranslationIso p c m).hom ≫
      (fiberClosureInclusion (translatedInitial p c) m ≫
        ((translatedInitial p c).stage m).structureMap) =
      fiberClosureInclusion (projectiveProductInitial (k := k)) m ≫
        ((projectiveProductInitial (k := k)).stage m).structureMap := by
    rw [← Category.assoc, fiberClosureTranslationIso_hom, Category.assoc,
      stageTranslationIso_hom_structure]
  simp only [translatedFiberIsoProjectiveLine, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [originFiberIso_hom_structure, ← ht, Iso.inv_hom_id_assoc]

variable [IsAlgClosed k] (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
  [Fact (q + 1).Prime] [CharP k (q + 1)] (i : Fin n)

/-- The original global strict fibre is isomorphic to its entire original tower strict fibre. -/
def fiberStrictIsoTower :
    fiberStrict (q + 1) n a i ≅ liftedFiberClosure (translatedInitial (q + 1) (a i)) (q + 1) := by
  letI := isIso_baseChange_snd q n a ha i
  exact fiberStrictIsoBaseChange q n a ha i ≪≫
    asIso (pullback.snd (towerProjection (q + 1) n a i)
      (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1)))

theorem fiberStrictIsoTower_hom_inclusion :
    (fiberStrictIsoTower q n a ha i).hom ≫
        fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1) =
      fiberStrictι (q + 1) n a i ≫ towerProjection (q + 1) n a i := by
  letI := isIso_baseChange_snd q n a ha i
  simp only [fiberStrictIsoTower, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← pullback.condition, ← Category.assoc, fiberStrictIsoBaseChange_hom]

theorem fiberStrictIsoTower_hom_structure :
    (fiberStrictIsoTower q n a ha i).hom ≫
        (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1) ≫
          ((translatedInitial (q + 1) (a i)).stage (q + 1)).structureMap) =
      fiberStrictι (q + 1) n a i ≫ multiStructure (q + 1) n a := by
  rw [← Category.assoc, fiberStrictIsoTower_hom_inclusion, Category.assoc,
    towerProjection_structure]

/-- Every independently constructed global strict fibre is an actual projective line. -/
def globalFiberIsoProjectiveLine : fiberStrict (q + 1) n a i ≅ projectiveSpace k 1 :=
  fiberStrictIsoTower q n a ha i ≪≫ translatedFiberIsoProjectiveLine (q + 1) (a i) (q + 1)

/-- The original global fibre isomorphism is over the original field. -/
theorem globalFiberIsoProjectiveLine_hom_structure :
    (globalFiberIsoProjectiveLine q n a ha i).hom ≫ projectiveSpaceToSpec k 1 =
      fiberStrictι (q + 1) n a i ≫ multiStructure (q + 1) n a := by
  simp only [globalFiberIsoProjectiveLine, Iso.trans_hom, Category.assoc]
  rw [translatedFiberIso_hom_structure, fiberStrictIsoTower_hom_structure]

include ha in
/-- Each original global strict fibre is smooth over the original field. -/
theorem globalFiber_isSmooth : IsSmooth (fiberStrictι (q + 1) n a i ≫ multiStructure (q + 1) n a) := by
  rw [← globalFiberIsoProjectiveLine_hom_structure q n a ha i]
  letI : IsSmooth (projectiveSpaceToSpec k 1) := projectiveLine_isSmooth
  infer_instance

end KltDP.Examples.FrobeniusMultiCentreFiberProjectiveLine

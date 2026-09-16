import KltDP.Geometry.AffineBlowupConormalChartFrames
import KltDP.Examples.FrobeniusExceptionalLine

/-!
# Original equation frames of the exceptional conormal on P1

The two frames below belong to the actual transported global conormal.
They come from the original Rees equations and the proved quotient-chart
comparisons. Pulling either frame farther back retains its original
local equation map. On the actual overlap both frames have the same
actual global module as target.

The comparisons to the two different ambient local conormals are still
different comparisons. These results do not identify the ratio of the two
global frames with the previously computed cotangent ratio, or assert a
normal-bundle degree or self-intersection number.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusExceptionalChartFrames

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusExceptionalProjectiveLine FrobeniusExceptionalLine

variable {k : Type u} [Field k]

/-- The original `u` equation gives an actual frame of the transported
conormal on the original first projective chart. -/
def leftFrameIso :
    _root_.SheafOfModules.unit (exceptionalChart centerIdeal (centerU (k := k))).ringCatSheaf ≅
      (schemeModulePullback leftToProjectiveLine).obj (conormalLine (k := k)).obj :=
  originalExceptionalChartFrameIso centerIdeal centerU ≪≫ leftConormalPullbackIso.symm

/-- The original `v` equation gives the corresponding actual second frame. -/
def rightFrameIso :
    _root_.SheafOfModules.unit (exceptionalChart centerIdeal (centerV (k := k))).ringCatSheaf ≅
      (schemeModulePullback rightToProjectiveLine).obj (conormalLine (k := k)).obj :=
  originalExceptionalChartFrameIso centerIdeal centerV ≪≫ rightConormalPullbackIso.symm

/-- The first frame comparison uses the original ambient affine chart. -/
def leftComparisonIso :
    (schemeModulePullback leftToProjectiveLine).obj (conormalLine (k := k)).obj ≅
      (schemeModulePullback (originalExceptionalChartLocalMap centerIdeal centerU)).obj
        (schemeConormalSheaf
          ((exceptionalIdeal centerIdeal).gluedTo ∣_ (chartAffineOpen centerIdeal centerU).1)) :=
  leftConormalPullbackIso ≪≫ originalExceptionalChartConormalComparisonIso centerIdeal centerU

/-- The second frame comparison uses the original second ambient chart. -/
def rightComparisonIso :
    (schemeModulePullback rightToProjectiveLine).obj (conormalLine (k := k)).obj ≅
      (schemeModulePullback (originalExceptionalChartLocalMap centerIdeal centerV)).obj
        (schemeConormalSheaf
          ((exceptionalIdeal centerIdeal).gluedTo ∣_ (chartAffineOpen centerIdeal centerV).1)) :=
  rightConormalPullbackIso ≪≫ originalExceptionalChartConormalComparisonIso centerIdeal centerV

/-- The first global-line frame retains precisely the original `u` equation. -/
theorem leftFrameIso_comparison :
    (leftFrameIso (k := k)).hom ≫ leftComparisonIso.hom =
      pulledConormalGenerator
        ((exceptionalIdeal centerIdeal).gluedTo ∣_ (chartAffineOpen centerIdeal centerU).1)
        (originalExceptionalChartLocalMap centerIdeal centerU)
        (gluedAffineEquation (chartAffineOpen centerIdeal centerU)
          (chartEquationSection centerIdeal centerU))
        (gluedAffineEquation_eq_zero (exceptionalIdeal centerIdeal)
          (chartAffineOpen centerIdeal centerU) (chartEquationSection centerIdeal centerU)
          (exceptionalIdeal_chartEquationSection centerIdeal centerU)) := by
  simp only [leftFrameIso, leftComparisonIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  exact originalExceptionalChartFrameIso_comparison centerIdeal centerU

/-- The second global-line frame retains precisely the original `v` equation. -/
theorem rightFrameIso_comparison :
    (rightFrameIso (k := k)).hom ≫ rightComparisonIso.hom =
      pulledConormalGenerator
        ((exceptionalIdeal centerIdeal).gluedTo ∣_ (chartAffineOpen centerIdeal centerV).1)
        (originalExceptionalChartLocalMap centerIdeal centerV)
        (gluedAffineEquation (chartAffineOpen centerIdeal centerV)
          (chartEquationSection centerIdeal centerV))
        (gluedAffineEquation_eq_zero (exceptionalIdeal centerIdeal)
          (chartAffineOpen centerIdeal centerV) (chartEquationSection centerIdeal centerV)
          (exceptionalIdeal_chartEquationSection centerIdeal centerV)) := by
  simp only [rightFrameIso, rightComparisonIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  exact originalExceptionalChartFrameIso_comparison centerIdeal centerV

/-- Further actual pullback of the first frame preserves its original equation. -/
theorem leftFrameIso_refinement {T : Scheme.{u}}
    (h : T ⟶ exceptionalChart centerIdeal (centerU (k := k))) :
    schemeModulePullbackFrame h leftFrameIso.hom ≫
      (schemeModulePullback h).map leftComparisonIso.hom ≫
        (schemeModulePullbackCompIso h
          (originalExceptionalChartLocalMap centerIdeal centerU)).hom.app _ =
      pulledConormalGenerator
        ((exceptionalIdeal centerIdeal).gluedTo ∣_ (chartAffineOpen centerIdeal centerU).1)
        (h ≫ originalExceptionalChartLocalMap centerIdeal centerU)
        (gluedAffineEquation (chartAffineOpen centerIdeal centerU)
          (chartEquationSection centerIdeal centerU))
        (gluedAffineEquation_eq_zero (exceptionalIdeal centerIdeal)
          (chartAffineOpen centerIdeal centerU) (chartEquationSection centerIdeal centerU)
          (exceptionalIdeal_chartEquationSection centerIdeal centerU)) := by
  rw [← Category.assoc, ← schemeModulePullbackFrame_postcomp, leftFrameIso_comparison]
  exact pulledConormalGenerator_comp _ _ _ _ _

/-- Further actual pullback of the second frame preserves its original equation. -/
theorem rightFrameIso_refinement {T : Scheme.{u}}
    (h : T ⟶ exceptionalChart centerIdeal (centerV (k := k))) :
    schemeModulePullbackFrame h rightFrameIso.hom ≫
      (schemeModulePullback h).map rightComparisonIso.hom ≫
        (schemeModulePullbackCompIso h
          (originalExceptionalChartLocalMap centerIdeal centerV)).hom.app _ =
      pulledConormalGenerator
        ((exceptionalIdeal centerIdeal).gluedTo ∣_ (chartAffineOpen centerIdeal centerV).1)
        (h ≫ originalExceptionalChartLocalMap centerIdeal centerV)
        (gluedAffineEquation (chartAffineOpen centerIdeal centerV)
          (chartEquationSection centerIdeal centerV))
        (gluedAffineEquation_eq_zero (exceptionalIdeal centerIdeal)
          (chartAffineOpen centerIdeal centerV) (chartEquationSection centerIdeal centerV)
          (exceptionalIdeal_chartEquationSection centerIdeal centerV)) := by
  rw [← Category.assoc, ← schemeModulePullbackFrame_postcomp, rightFrameIso_comparison]
  exact pulledConormalGenerator_comp _ _ _ _ _

/-- The actual exceptional overlap maps to P1 along its first chart. -/
def overlapToProjectiveLine :
    exceptionalOverlapScheme centerIdeal (centerU (k := k)) centerV ⟶ projectiveSpace k 1 :=
  exceptionalOverlapLeftMorphism centerIdeal centerU centerV ≫ leftToProjectiveLine

/-- The second chart gives this same actual overlap morphism. -/
theorem overlapToProjectiveLine_right :
    overlapToProjectiveLine (k := k) =
      exceptionalOverlapRightMorphism centerIdeal centerU centerV ≫ rightToProjectiveLine := by
  rw [overlapToProjectiveLine, ← chartToExceptional_left, ← Category.assoc]
  change overlapToExceptional ≫ exceptionalProjectiveLineIso.hom = _
  rw [overlapToExceptional_right, Category.assoc, chartToExceptional_right]

/-- Pullback of the actual first frame to the actual common overlap. -/
def leftOverlapFrameIso :
    _root_.SheafOfModules.unit
      (exceptionalOverlapScheme centerIdeal (centerU (k := k)) centerV).ringCatSheaf ≅
      (schemeModulePullback overlapToProjectiveLine).obj (conormalLine (k := k)).obj :=
  (schemeModulePullbackUnitIso
    (exceptionalOverlapLeftMorphism centerIdeal centerU centerV)).symm ≪≫
    (schemeModulePullback (exceptionalOverlapLeftMorphism centerIdeal centerU centerV)).mapIso
      leftFrameIso ≪≫
    (schemeModulePullbackCompIso
      (exceptionalOverlapLeftMorphism centerIdeal centerU centerV) leftToProjectiveLine).app _

/-- Pullback of the actual second frame, with the same global module as target. -/
def rightOverlapFrameIso :
    _root_.SheafOfModules.unit
      (exceptionalOverlapScheme centerIdeal (centerU (k := k)) centerV).ringCatSheaf ≅
      (schemeModulePullback overlapToProjectiveLine).obj (conormalLine (k := k)).obj :=
  (schemeModulePullbackUnitIso
    (exceptionalOverlapRightMorphism centerIdeal centerU centerV)).symm ≪≫
    (schemeModulePullback (exceptionalOverlapRightMorphism centerIdeal centerU centerV)).mapIso
      rightFrameIso ≪≫
    (schemeModulePullbackCompIso
      (exceptionalOverlapRightMorphism centerIdeal centerU centerV) rightToProjectiveLine).app _ ≪≫
    (eqToIso (congrArg schemeModulePullback overlapToProjectiveLine_right.symm)).app _

/-- This automorphism is extracted from the two constructed global-line
frames, without prescribing a Laurent coefficient. -/
def actualOverlapFrameChange :
    _root_.SheafOfModules.unit
      (exceptionalOverlapScheme centerIdeal (centerU (k := k)) centerV).ringCatSheaf ≅
      _root_.SheafOfModules.unit
        (exceptionalOverlapScheme centerIdeal (centerU (k := k)) centerV).ringCatSheaf :=
  rightOverlapFrameIso ≪≫ leftOverlapFrameIso.symm

/-- The extracted automorphism has the original frame-transition orientation. -/
theorem actualOverlapFrameChange_hom_leftFrame :
    (actualOverlapFrameChange (k := k)).hom ≫ leftOverlapFrameIso.hom =
      rightOverlapFrameIso.hom := by
  simp only [actualOverlapFrameChange, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

end KltDP.Examples.FrobeniusExceptionalChartFrames

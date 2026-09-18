import KltDP.Examples.FrobeniusContactTowerCanonicalFactorIdeals
import KltDP.Examples.FrobeniusContactTowerCanonicalFactorIdentity
import KltDP.Examples.FrobeniusContactTowerCanonicalFactorLocalIdeals

/-!
# Normalized recurrences for the original total exceptional lines

The total line is the actual creation-stage exceptional ideal pulled by the
original between-stage projection. The old-index comparison is the original
pullback-composition isomorphism; the newest comparison is the original
identity pullback. Their inclusion equations use the proved unit normalizations.
The translated specializations are literally the accepted tower lines and maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusContactTowerCanonicalFactorTotalLines

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusGlobalBlowupCanonicalTarget
open FrobeniusExceptionalFinalConfiguration FrobeniusTranslatedCharts
open FrobeniusMultiCentreSurface FrobeniusContactTowerCanonicalFactorIdentity
open FrobeniusContactTowerCanonicalFactorOffRange FrobeniusContactTowerCanonicalFactorLocalIdeals

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private def pullbackCompEqIso {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (t : Z ⟶ X) (h : g ≫ f = t) (M : X.Modules) :
    (schemeModulePullback g).obj ((schemeModulePullback f).obj M) ≅
      (schemeModulePullback t).obj M :=
  (schemeModulePullbackCompIso g f).app M ≪≫
    eqToIso (congrArg (fun r => (schemeModulePullback r).obj M) h)

private theorem pullbackCompEqIso_inclusion {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (t : Z ⟶ X) (h : g ≫ f = t)
    {I : X.Modules} (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) :
    (pullbackCompEqIso f g t h I).hom ≫ (schemeModulePullback t).map i ≫
        (schemeModulePullbackUnitIso t).hom =
      (schemeModulePullback g).map
        ((schemeModulePullback f).map i ≫ (schemeModulePullbackUnitIso f).hom) ≫
        (schemeModulePullbackUnitIso g).hom := by
  subst t
  simpa only [pullbackCompEqIso, Iso.trans_hom, eqToIso_refl,
    Iso.refl_hom, Category.comp_id, Iso.app_hom] using pulledInclusion_comp f g i

/-- Name the original forward composition map before an actual stage is specialized. -/
private def pullbackCompEqMap {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (t : Z ⟶ X) (h : g ≫ f = t) (M : X.Modules) :
    (schemeModulePullback g).obj ((schemeModulePullback f).obj M) ⟶
      (schemeModulePullback t).obj M :=
  (pullbackCompEqIso f g t h M).hom

private theorem pullbackCompEqMap_isIso {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (t : Z ⟶ X) (h : g ≫ f = t) (M : X.Modules) :
    IsIso (pullbackCompEqMap f g t h M) := by
  unfold pullbackCompEqMap
  infer_instance

private theorem pullbackCompEqMap_inclusion {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (t : Z ⟶ X) (h : g ≫ f = t)
    {I : X.Modules} (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) :
    pullbackCompEqMap f g t h I ≫ (schemeModulePullback t).map i ≫
        (schemeModulePullbackUnitIso t).hom =
      (schemeModulePullback g).map
        ((schemeModulePullback f).map i ≫ (schemeModulePullbackUnitIso f).hom) ≫
        (schemeModulePullbackUnitIso g).hom :=
  pullbackCompEqIso_inclusion f g t h i

private def pullbackEqIdIso {X : Scheme.{u}} (f : X ⟶ X) (h : f = 𝟙 X)
    (M : X.Modules) : (schemeModulePullback f).obj M ≅ M :=
  eqToIso (congrArg (fun r => (schemeModulePullback r).obj M) h) ≪≫
    (schemeModulePullbackIdIso X).app M

private theorem pullbackEqIdIso_inclusion {X : Scheme.{u}} (f : X ⟶ X) (h : f = 𝟙 X)
    {I : X.Modules} (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) :
    (pullbackEqIdIso f h I).hom ≫ i =
      (schemeModulePullback f).map i ≫ (schemeModulePullbackUnitIso f).hom := by
  subst f
  simpa only [pullbackEqIdIso, Iso.trans_hom, eqToIso_refl,
    Iso.refl_hom, Category.id_comp, Iso.app_hom] using pullbackIdIso_inclusion i

private theorem inclusion_of_map_eq {C : Type*} [Category C] {I J O : C}
    {a a' : I ⟶ J} {b b' : J ⟶ O} {c c' : I ⟶ O}
    (ha : a = a') (hb : b = b') (hc : c = c') (h : a' ≫ b' = c') :
    a ≫ b = c := by
  cases ha
  cases hb
  cases hc
  exact h

variable {k : Type u} [Field k] (A : PlaneChartedScheme k)

/-- The original step ideal, with its actual successor carrier stated explicitly. -/
def stepLine (n : ℕ) : InvertibleSheaf (A.stage (n + 1)).carrier :=
  wholeExceptionalIdealLine (A.stage n)

/-- Its literal original inclusion. -/
def stepInclusion (n : ℕ) :
    (stepLine A n).obj ⟶ _root_.SheafOfModules.unit (A.stage (n + 1)).carrier.ringCatSheaf :=
  wholeExceptionalInclusion (A.stage n)

/-- The actual total transform of the creation-stage ideal. -/
def totalLine (N : ℕ) (j : Fin N) : InvertibleSheaf (A.stage N).carrier :=
  pullbackInvertibleSheaf (between A j.isLt) (stepLine A j.val)

/-- The original total-transform inclusion, with its canonical pullback-unit map. -/
def totalInclusion (N : ℕ) (j : Fin N) :
    (totalLine A N j).obj ⟶ _root_.SheafOfModules.unit (A.stage N).carrier.ringCatSheaf :=
  (schemeModulePullback (between A j.isLt)).map (stepInclusion A j.val) ≫
    (schemeModulePullbackUnitIso (between A j.isLt)).hom

/-- The literal original comparison map of an older total line through the new step. -/
def castSuccMap (N : ℕ) (j : Fin N) :
    (schemeModulePullback (A.stepProjection N)).obj (totalLine A N j).obj ⟶
      (totalLine A (N + 1) j.castSucc).obj :=
  pullbackCompEqMap (between A j.isLt) (A.stepProjection N)
    (between A j.castSucc.isLt) (between_succ A j.isLt).symm (stepLine A j.val).obj

private theorem castSuccMap_isIso (N : ℕ) (j : Fin N) : IsIso (castSuccMap A N j) :=
  pullbackCompEqMap_isIso (between A j.isLt) (A.stepProjection N)
    (between A j.castSucc.isLt) (between_succ A j.isLt).symm (stepLine A j.val).obj

/-- An older total line is pulled through exactly the same original forward map. -/
def castSuccIso (N : ℕ) (j : Fin N) :
    (schemeModulePullback (A.stepProjection N)).obj (totalLine A N j).obj ≅
      (totalLine A (N + 1) j.castSucc).obj := by
  letI := castSuccMap_isIso A N j
  exact asIso (castSuccMap A N j)

@[simp] theorem castSuccIso_hom (N : ℕ) (j : Fin N) :
    (castSuccIso A N j).hom = castSuccMap A N j := rfl

private def castSucc_inclusion_proof (k : Type u) [Field k]
    (A : PlaneChartedScheme k) (N : ℕ) (j : Fin N) :=
  pullbackCompEqMap_inclusion (between A j.isLt) (A.stepProjection N)
    (between A j.castSucc.isLt) (between_succ A j.isLt).symm (stepInclusion A j.val)

private theorem castSuccIso_hom_eq (N : ℕ) (j : Fin N) :
    (castSuccIso A N j).hom =
      pullbackCompEqMap (between A j.isLt) (A.stepProjection N)
        (between A j.castSucc.isLt) (between_succ A j.isLt).symm (stepLine A j.val).obj := by
  simpa only [castSuccMap] using castSuccIso_hom A N j

private theorem castSucc_totalInclusion_eq (N : ℕ) (j : Fin N) :
    totalInclusion A (N + 1) j.castSucc =
      (schemeModulePullback (between A j.castSucc.isLt)).map (stepInclusion A j.val) ≫
        (schemeModulePullbackUnitIso (between A j.castSucc.isLt)).hom := rfl

private theorem totalInclusion_pullback_eq (N : ℕ) (j : Fin N) :
    (schemeModulePullback (A.stepProjection N)).map (totalInclusion A N j) ≫
        (schemeModulePullbackUnitIso (A.stepProjection N)).hom =
      (schemeModulePullback (A.stepProjection N)).map
        ((schemeModulePullback (between A j.isLt)).map (stepInclusion A j.val) ≫
          (schemeModulePullbackUnitIso (between A j.isLt)).hom) ≫
        (schemeModulePullbackUnitIso (A.stepProjection N)).hom := rfl

/-- The old-index isomorphism retains the original pulled total inclusion. -/
theorem castSuccIso_inclusion (N : ℕ) (j : Fin N) :
    (castSuccIso A N j).hom ≫ totalInclusion A (N + 1) j.castSucc =
      (schemeModulePullback (A.stepProjection N)).map (totalInclusion A N j) ≫
        (schemeModulePullbackUnitIso (A.stepProjection N)).hom :=
  inclusion_of_map_eq (castSuccIso_hom_eq A N j) (castSucc_totalInclusion_eq A N j)
    (totalInclusion_pullback_eq A N j) (castSucc_inclusion_proof k A N j)

/-- The newest total line is the original exceptional ideal through identity pullback. -/
def lastIso (N : ℕ) : (totalLine A (N + 1) (Fin.last N)).obj ≅ (stepLine A N).obj :=
  pullbackEqIdIso (between A (le_refl (N + 1))) (between_refl A (N + 1)) (stepLine A N).obj

/-- The newest comparison retains its original ideal inclusion. -/
theorem lastIso_inclusion (N : ℕ) :
    (lastIso A N).hom ≫ stepInclusion A N = totalInclusion A (N + 1) (Fin.last N) :=
  pullbackEqIdIso_inclusion (between A (le_refl (N + 1))) (between_refl A (N + 1))
    (stepInclusion A N)

/-- The translated total line is literally the already accepted tower exceptional line. -/
theorem translated_totalLine_eq (p : ℕ) (a : k) (j : Fin p) :
    totalLine (translatedInitial p a) p j = towerExceptionalLine p a j := rfl

/-- Its inclusion is literally the original map used in the compiled finite-centre restrictions. -/
theorem translated_totalInclusion_eq (p : ℕ) (a : k) (j : Fin p) :
    totalInclusion (translatedInitial p a) p j = towerTotalExceptionalInclusion p a j := rfl

end KltDP.Examples.FrobeniusContactTowerCanonicalFactorTotalLines


import KltDP.Examples.FrobeniusGlobalBlowupStages
import KltDP.Examples.FrobeniusBlowupGlobalDifferentialCharts
import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportIsIso
import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportSquare

/-!
# The original whole-stage blowup differential on its actual affine Rees open

The original projection of `PlaneChartedScheme.next` restricts to the original
contact-plane Rees blowdown. Both ambient top sheaves are identified through
their actual open-immersion differential maps. The square follows from the
proved scheme projection identity and original exterior-map composition.
No smoothness, projectivity, canonical formula or compatibility is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusGlobalBlowupDifferentialAffine

open KltDP.Geometry KltDP.Geometry.SchemeKaehlerSheaf
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusGlobalBlowupStages
open FrobeniusBlowupGlobalDifferentialCharts

private theorem square_of_map_eq {C : Type*} [Category C] {S P Q R T : C}
    {a a' : S ⟶ P} {b b' : P ⟶ T} {c c' : S ⟶ Q}
    {d d' : Q ⟶ R} {e e' : R ⟶ T}
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') (he : e = e')
    (h : a' ≫ b' = c' ≫ d' ≫ e') : a ≫ b = c ≫ d ≫ e := by
  cases ha
  cases hb
  cases hc
  cases hd
  cases he
  exact h

variable {k : Type u} [Field k] (A : PlaneChartedScheme k)

abbrev oldTop : A.carrier.Modules :=
  SchemeExteriorPower.sheaf (baseRingSheaf A.structureMap) 2

abbrev nextTop : A.nextScheme.Modules :=
  SchemeExteriorPower.sheaf (baseRingSheaf A.nextStructure) 2

/-- The actual affine Rees open retains its original field structure. -/
theorem affineBlowup_structure :
    A.nextAffineBlowup ≫ A.nextStructure = blowupStructure (k := k) := by
  change A.nextAffineBlowup ≫ (A.nextProjection ≫ A.structureMap) =
    AffineBlowup.toSpec (centerIdeal (k := k)) ≫ planeStructure
  rw [← Category.assoc, A.nextAffineBlowup_projection, Category.assoc, A.chart_structure]

/-- The original top differential of the whole next-stage projection. -/
def nextDifferentialMap :
    (schemeModulePullback A.nextProjection).obj (oldTop A) ⟶ nextTop A :=
  SchemeKaehlerExteriorPullbackTransport.map
    A.structureMap A.nextProjection A.nextStructure rfl 2

def oldChartMap :
    (schemeModulePullback A.chart).obj (oldTop A) ⟶ planeTop (k := k) :=
  SchemeKaehlerExteriorPullbackTransport.map
    A.structureMap A.chart planeStructure A.chart_structure 2

def affineBlowupMap :
    (schemeModulePullback A.nextAffineBlowup).obj (nextTop A) ⟶ blowupTop (k := k) :=
  SchemeKaehlerExteriorPullbackTransport.map A.nextStructure A.nextAffineBlowup
    blowupStructure (affineBlowup_structure A) 2

/-- The old affine-plane comparison is the original open differential isomorphism. -/
def oldChartIso :
    (schemeModulePullback A.chart).obj (oldTop A) ≅ planeTop (k := k) := by
  letI : IsIso (oldChartMap A) :=
    SchemeKaehlerExteriorPullbackTransport.map_isIso
      A.structureMap A.chart planeStructure A.chart_structure 2
  exact asIso (oldChartMap A)

theorem oldChartIso_hom : (oldChartIso A).hom = oldChartMap A := rfl

/-- The entire affine Rees open has the original new-stage differential isomorphism. -/
def affineBlowupIso :
    (schemeModulePullback A.nextAffineBlowup).obj (nextTop A) ≅ blowupTop (k := k) := by
  letI : IsIso (affineBlowupMap A) :=
    SchemeKaehlerExteriorPullbackTransport.map_isIso A.nextStructure A.nextAffineBlowup
      blowupStructure (affineBlowup_structure A) 2
  exact asIso (affineBlowupMap A)

theorem affineBlowupIso_hom : (affineBlowupIso A).hom = affineBlowupMap A := rfl

/-- The original two pullback compositions around the actual blowdown square. -/
def affineSquareSourceIso :
    (schemeModulePullback A.nextAffineBlowup).obj
        ((schemeModulePullback A.nextProjection).obj (oldTop A)) ≅
      (schemeModulePullback (AffineBlowup.toSpec (centerIdeal (k := k)))).obj
        ((schemeModulePullback A.chart).obj (oldTop A)) :=
  SchemeKaehlerExteriorPullbackTransport.squareSourceIso A.structureMap
    A.nextProjection A.nextAffineBlowup A.chart (AffineBlowup.toSpec centerIdeal)
    A.nextAffineBlowup_projection 2

private def nextDifferentialMap_affine_proof (k : Type u) [Field k]
    (A : PlaneChartedScheme k) :=
  SchemeKaehlerExteriorPullbackTransport.map_square A.structureMap
    A.nextProjection A.nextAffineBlowup A.chart (AffineBlowup.toSpec centerIdeal)
    A.nextAffineBlowup_projection 2 A.nextStructure rfl planeStructure
    A.chart_structure blowupStructure (affineBlowup_structure A) rfl

private theorem nextDifferentialMap_pullback_eq :
    (schemeModulePullback A.nextAffineBlowup).map (nextDifferentialMap A) =
      (schemeModulePullback A.nextAffineBlowup).map
        (SchemeKaehlerExteriorPullbackTransport.map
          A.structureMap A.nextProjection A.nextStructure rfl 2) := rfl

private theorem affineBlowupMap_eq : affineBlowupMap A =
    SchemeKaehlerExteriorPullbackTransport.map A.nextStructure A.nextAffineBlowup
      blowupStructure (affineBlowup_structure A) 2 := rfl

private theorem affineSquareSourceIso_hom_eq : (affineSquareSourceIso A).hom =
    (SchemeKaehlerExteriorPullbackTransport.squareSourceIso A.structureMap
      A.nextProjection A.nextAffineBlowup A.chart (AffineBlowup.toSpec centerIdeal)
      A.nextAffineBlowup_projection 2).hom := rfl

private theorem oldChartMap_pullback_eq :
    (schemeModulePullback (AffineBlowup.toSpec (centerIdeal (k := k)))).map (oldChartMap A) =
      (schemeModulePullback (AffineBlowup.toSpec (centerIdeal (k := k)))).map
        (SchemeKaehlerExteriorPullbackTransport.map
          A.structureMap A.chart planeStructure A.chart_structure 2) := rfl

private theorem blowdownMap_eq : blowdownMap (k := k) =
    SchemeKaehlerExteriorPullbackTransport.map planeStructure
      (AffineBlowup.toSpec (centerIdeal (k := k))) blowupStructure rfl 2 := rfl

/-- The actual whole-stage differential restricts to the same original Rees differential. -/
theorem nextDifferentialMap_affine :
    (schemeModulePullback A.nextAffineBlowup).map (nextDifferentialMap A) ≫ affineBlowupMap A =
      (affineSquareSourceIso A).hom ≫
        (schemeModulePullback (AffineBlowup.toSpec (centerIdeal (k := k)))).map (oldChartMap A) ≫
          blowdownMap (k := k) :=
  square_of_map_eq (nextDifferentialMap_pullback_eq A) (affineBlowupMap_eq A)
    (affineSquareSourceIso_hom_eq A) (oldChartMap_pullback_eq A) (blowdownMap_eq (k := k))
    (nextDifferentialMap_affine_proof k A)

/-- The actual source comparison includes the original old-chart exterior isomorphism. -/
def affineSourceIso :
    (schemeModulePullback A.nextAffineBlowup).obj
        ((schemeModulePullback A.nextProjection).obj (oldTop A)) ≅
      (schemeModulePullback (AffineBlowup.toSpec (centerIdeal (k := k)))).obj (planeTop (k := k)) :=
  affineSquareSourceIso A ≪≫
    (schemeModulePullback (AffineBlowup.toSpec (centerIdeal (k := k)))).mapIso (oldChartIso A)

/-- This is the original whole-map square through actual old and new open isomorphisms. -/
theorem nextDifferentialMap_affineIso :
    (schemeModulePullback A.nextAffineBlowup).map (nextDifferentialMap A) ≫
        (affineBlowupIso A).hom = (affineSourceIso A).hom ≫ blowdownMap (k := k) := by
  rw [affineBlowupIso_hom, nextDifferentialMap_affine]
  simp only [affineSourceIso, Iso.trans_hom, Functor.mapIso_hom, oldChartIso_hom,
    Category.assoc]

end KltDP.Examples.FrobeniusGlobalBlowupDifferentialAffine

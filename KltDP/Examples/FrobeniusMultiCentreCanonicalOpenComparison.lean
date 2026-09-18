import KltDP.Examples.FrobeniusContactTowerCanonicalIteration
import KltDP.Examples.FrobeniusMultiCentreIsoOpenClasses
import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportIsIso

/-!
# The actual canonical sheaf on the finite-centre covering opens

Each original cluster open maps openly to its own original translated tower.
The complement of all centres maps openly to the original projective product.
The actual open differential maps identify the respective pullbacks of the
actual atlas canonical sheaves with the same intrinsic exterior sheaf.
The resulting isomorphisms retain those original forward maps. No global
canonical formula or gluing of unrelated line isomorphisms is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCanonicalOpenComparison

open KltDP.Geometry KltDP.Geometry.SmoothSurfaceKaehlerAtlas
open KltDP.Geometry.SchemeKaehlerSheaf KltDP.Geometry.SchemeKernelIdealIsoTransport
open FrobeniusGlobalBlowupStages FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint
open FrobeniusMultiCentreSurface FrobeniusMultiCentreGraphNewest FrobeniusMultiCentreCurveKernels
open FrobeniusMultiCentreIsoOpenClasses FrobeniusContactTowerCanonicalIteration

variable {k : Type u} [Field k]

/-- Reuse the original atlas comparison and the original transported open differential. -/
private def canonicalToExteriorIso {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsSmoothOfRelativeDimension 2 f]
    (j : Y ⟶ X) [IsOpenImmersion j]
    (g : Y ⟶ Spec (CommRingCat.of k)) (h : j ≫ f = g) :
    (schemeModulePullback j).obj (canonicalSheafOfSmoothSurface f).obj ≅
      SchemeExteriorPower.sheaf (baseRingSheaf g) 2 := by
  letI := SchemeKaehlerExteriorPullbackTransport.map_isIso f j g h 2
  exact (schemeModulePullback j).mapIso
      (SmoothCanonicalExteriorComparison.canonicalSheafOfSmoothSurfaceIsoExterior f) ≪≫
    asIso (SchemeKaehlerExteriorPullbackTransport.map f j g h 2)

/-- The actual structure map on the original cluster open. -/
abbrev clusterStructure (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (isoPreimage q n a i).toScheme ⟶ Spec (CommRingCat.of k) :=
  (isoPreimage q n a i).ι ≫ multiStructure (q + 1) n a

/-- The original tower open map commutes with the same actual field structure. -/
theorem isoMap_structure (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    isoMap q n a i ≫ ((translatedInitial (q + 1) (a i)).stage (q + 1)).structureMap =
      clusterStructure q n a i := by
  rw [← selectedProjection_structure, ← Category.assoc, ← ι_multiProjection]
  rfl

/-- The actual tower canonical line maps to the intrinsic top sheaf on this original cluster. -/
def towerCanonicalToClusterExteriorIso (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (schemeModulePullback (isoMap q n a i)).obj
        (canonicalSheafOfSmoothSurface
          ((translatedInitial (q + 1) (a i)).stage (q + 1)).structureMap).obj ≅
      SchemeExteriorPower.sheaf (baseRingSheaf (clusterStructure q n a i)) 2 :=
  canonicalToExteriorIso _ (isoMap q n a i) (clusterStructure q n a i)
    (isoMap_structure q n a i)

/-- The original blowdown is an open map on the complement of all centres. -/
private theorem blowdownMap_isOpenImmersion (q n : ℕ) (a : Fin n → k) :
    IsOpenImmersion (blowdownMap q n a) := by
  unfold blowdownMap
  infer_instance

/-- The actual structure map on the original complement of all centres. -/
abbrev complementStructure (q n : ℕ) (a : Fin n → k) :
    (blowdownIsoOpen q n a).toScheme ⟶ Spec (CommRingCat.of k) :=
  (blowdownIsoOpen q n a).ι ≫ multiStructure (q + 1) n a

theorem blowdownMap_structure (q n : ℕ) (a : Fin n → k) :
    blowdownMap q n a ≫ (projectiveProductInitial (k := k)).structureMap =
      complementStructure q n a := by
  rw [blowdownMap_eq, Category.assoc]
  rfl

/-- The original product canonical line maps to the intrinsic top sheaf on the complement. -/
def baseCanonicalToComplementExteriorIso (q n : ℕ) (a : Fin n → k) :
    (schemeModulePullback (blowdownMap q n a)).obj
        (canonicalSheafOfSmoothSurface (projectiveProductInitial (k := k)).structureMap).obj ≅
      SchemeExteriorPower.sheaf (baseRingSheaf (complementStructure q n a)) 2 := by
  letI := blowdownMap_isOpenImmersion q n a
  exact canonicalToExteriorIso _ (blowdownMap q n a) (complementStructure q n a)
    (blowdownMap_structure q n a)

variable [IsAlgClosed k]

/-- The actual atlas canonical sheaf on the original finite-centre surface. -/
def multiCanonicalLine (p n : ℕ) (a : Fin n → k) (ha : Function.Injective a) :
    InvertibleSheaf (multiSurface p n a) := by
  letI := multiStructure_smoothTwo p n a ha
  exact canonicalSheafOfSmoothSurface (multiStructure p n a)

/-- Its actual Picard class; this definition contains no proposed class formula. -/
abbrev multiCanonicalClass (p n : ℕ) (a : Fin n → k) (ha : Function.Injective a) :
    Additive (multiSurface p n a).Pic :=
  Additive.ofMul (multiCanonicalLine p n a ha).toPic

/-- The original global canonical line maps to the same intrinsic top sheaf on a cluster. -/
def multiCanonicalToClusterExteriorIso (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) (i : Fin n) :
    (schemeModulePullback (isoPreimage q n a i).ι).obj
        (multiCanonicalLine (q + 1) n a ha).obj ≅
      SchemeExteriorPower.sheaf (baseRingSheaf (clusterStructure q n a i)) 2 := by
  letI := multiStructure_smoothTwo (q + 1) n a ha
  exact canonicalToExteriorIso _ (isoPreimage q n a i).ι (clusterStructure q n a i) rfl

/-- Both actual canonical restrictions are identified through their original open differentials. -/
def clusterCanonicalIso (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a) (i : Fin n) :
    (schemeModulePullback (isoPreimage q n a i).ι).obj
        (multiCanonicalLine (q + 1) n a ha).obj ≅
      (schemeModulePullback (isoMap q n a i)).obj
        (canonicalSheafOfSmoothSurface
          ((translatedInitial (q + 1) (a i)).stage (q + 1)).structureMap).obj :=
  multiCanonicalToClusterExteriorIso q n a ha i ≪≫
    (towerCanonicalToClusterExteriorIso q n a i).symm

/-- The comparison preserves the original forward map into the intrinsic exterior sheaf. -/
theorem clusterCanonicalIso_comp (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) (i : Fin n) :
    (clusterCanonicalIso q n a ha i).hom ≫ (towerCanonicalToClusterExteriorIso q n a i).hom =
      (multiCanonicalToClusterExteriorIso q n a ha i).hom := by
  simp only [clusterCanonicalIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The original global canonical line maps to the intrinsic top sheaf on the complement. -/
def multiCanonicalToComplementExteriorIso (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) :
    (schemeModulePullback (blowdownIsoOpen q n a).ι).obj
        (multiCanonicalLine (q + 1) n a ha).obj ≅
      SchemeExteriorPower.sheaf (baseRingSheaf (complementStructure q n a)) 2 := by
  letI := multiStructure_smoothTwo (q + 1) n a ha
  exact canonicalToExteriorIso _ (blowdownIsoOpen q n a).ι (complementStructure q n a) rfl

/-- The same comparison on the original complement uses its original blowdown open map. -/
def complementCanonicalIso (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a) :
    (schemeModulePullback (blowdownIsoOpen q n a).ι).obj
        (multiCanonicalLine (q + 1) n a ha).obj ≅
      (schemeModulePullback (blowdownMap q n a)).obj
        (canonicalSheafOfSmoothSurface (projectiveProductInitial (k := k)).structureMap).obj :=
  multiCanonicalToComplementExteriorIso q n a ha ≪≫
    (baseCanonicalToComplementExteriorIso q n a).symm

theorem complementCanonicalIso_comp (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) :
    (complementCanonicalIso q n a ha).hom ≫ (baseCanonicalToComplementExteriorIso q n a).hom =
      (multiCanonicalToComplementExteriorIso q n a ha).hom := by
  simp only [complementCanonicalIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- Restriction of the actual global canonical class equals the original tower restriction. -/
theorem clusterCanonicalClass_eq (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) (i : Fin n) :
    (schemePicardPullbackHom (isoPreimage q n a i).ι).toAdditive
        (multiCanonicalClass (q + 1) n a ha) =
      (schemePicardPullbackHom (isoMap q n a i)).toAdditive
        (translatedCanonicalClass (q + 1) (a i) (q + 1)) := by
  change Additive.ofMul (schemePicardPullbackHom (isoPreimage q n a i).ι
      (multiCanonicalLine (q + 1) n a ha).toPic) =
    Additive.ofMul (schemePicardPullbackHom (isoMap q n a i)
      (canonicalSheafOfSmoothSurface
        ((translatedInitial (q + 1) (a i)).stage (q + 1)).structureMap).toPic)
  rw [schemePicardPullbackHom_toPic, schemePicardPullbackHom_toPic]
  exact congrArg Additive.ofMul (toPic_eq_of_iso _ _ (clusterCanonicalIso q n a ha i))

/-- On the original complement, the actual canonical class is the original product restriction. -/
theorem complementCanonicalClass_eq (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) :
    (schemePicardPullbackHom (blowdownIsoOpen q n a).ι).toAdditive
        (multiCanonicalClass (q + 1) n a ha) =
      (schemePicardPullbackHom (blowdownMap q n a)).toAdditive
        (originalCanonicalClass (k := k) 0) := by
  change Additive.ofMul (schemePicardPullbackHom (blowdownIsoOpen q n a).ι
      (multiCanonicalLine (q + 1) n a ha).toPic) =
    Additive.ofMul (schemePicardPullbackHom (blowdownMap q n a)
      (canonicalSheafOfSmoothSurface (projectiveProductInitial (k := k)).structureMap).toPic)
  rw [schemePicardPullbackHom_toPic, schemePicardPullbackHom_toPic]
  exact congrArg Additive.ofMul (toPic_eq_of_iso _ _ (complementCanonicalIso q n a ha))

end KltDP.Examples.FrobeniusMultiCentreCanonicalOpenComparison

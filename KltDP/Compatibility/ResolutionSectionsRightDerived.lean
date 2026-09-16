/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Vasily Ilin

Adapted from Vilin97/MazurTheorem
9327963d4ec14fba49c7b14b004fd00707ffc2e9,
SheafDerivedGlobalSections: the sectionsCochainHomologyAddEquivCocomplex
and sectionsCocomplexHomologyAddEquivRightDerived blocks.
Existing project extension and canonical representing maps are reused.
-/
import KltDP.Compatibility.HomComplexGlobalSections
import KltDP.Compatibility.MapCochainExtension

/-!
# Actual resolution homology and the canonical right-derived functor

The integer extension of an actual injective resolution computes the
original right-derived functor. The comparison composes the existing
map/extension isomorphism, the pinned extension/homology isomorphism,
and the pinned comparison with the chosen injective resolution.
Its naturality retains the original resolution map. Specializing to
global sections gives the right-derived side of the Hom-complex
comparison. The identification with Ext is a separate obligation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v u

namespace KltDP.CochainComparison

variable {C : Type u} [Category.{v} C] [Abelian C]
  (G : C ⥤ AddCommGrp.{v}) [G.Additive] {F F' : C}

/-- Remove the integer extension using the original comparison maps. -/
def resolutionHomologyIsoCocomplex (R : InjectiveResolution F) (n : ℕ) :
    ((G.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex).homology (n : ℤ) ≅
      ((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology n :=
  (HomologicalComplex.homologyFunctor AddCommGrp.{v} (.up ℤ) (n : ℤ)).mapIso
      (mapExtendIso (G := G) R.cocomplex) ≪≫
    ((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)

/-- Naturality uses the actual map of resolutions, before taking homology. -/
theorem resolutionHomologyIsoCocomplex_naturality
    (R : InjectiveResolution F) (R' : InjectiveResolution F') {g : F ⟶ F'}
    (φ : InjectiveResolution.Hom R R' g) (n : ℕ) :
    (HomologicalComplex.homologyFunctor AddCommGrp.{v} (.up ℤ) (n : ℤ)).map
        ((G.mapHomologicalComplex (.up ℤ)).map φ.hom') ≫
      (resolutionHomologyIsoCocomplex G R' n).hom =
    (resolutionHomologyIsoCocomplex G R n).hom ≫
      (HomologicalComplex.homologyFunctor AddCommGrp.{v} (.up ℕ) n).map
        ((G.mapHomologicalComplex (.up ℕ)).map φ.hom) := by
  let HZ := HomologicalComplex.homologyFunctor AddCommGrp.{v} (.up ℤ) (n : ℤ)
  let HN := HomologicalComplex.homologyFunctor AddCommGrp.{v} (.up ℕ) n
  let fN := (G.mapHomologicalComplex (.up ℕ)).map φ.hom
  let fE := HomologicalComplex.extendMap fN ComplexShape.embeddingUpNat
  have hmap :
      HZ.map ((G.mapHomologicalComplex (.up ℤ)).map φ.hom') ≫
          HZ.map (mapExtendIso (G := G) R'.cocomplex).hom =
        HZ.map (mapExtendIso (G := G) R.cocomplex).hom ≫ HZ.map fE := by
    simpa only [Functor.map_comp, InjectiveResolution.Hom.hom', fE, fN] using
      congrArg HZ.map (mapExtendIso_naturality (G := G) φ.hom)
  let E := (((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).extendHomologyIso
    ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)).hom
  let E' := (((G.mapHomologicalComplex (.up ℕ)).obj R'.cocomplex).extendHomologyIso
    ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)).hom
  have hext : HZ.map fE ≫ E' = E ≫ HN.map fN :=
    HomologicalComplex.extendHomologyIso_hom_naturality fN
      ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)
  change HZ.map ((G.mapHomologicalComplex (.up ℤ)).map φ.hom') ≫
      (HZ.map (mapExtendIso (G := G) R'.cocomplex).hom ≫ E') =
    (HZ.map (mapExtendIso (G := G) R.cocomplex).hom ≫ E) ≫ HN.map fN
  calc
    _ = (HZ.map ((G.mapHomologicalComplex (.up ℤ)).map φ.hom') ≫
        HZ.map (mapExtendIso (G := G) R'.cocomplex).hom) ≫ E' :=
      (Category.assoc _ _ _).symm
    _ = (HZ.map (mapExtendIso (G := G) R.cocomplex).hom ≫ HZ.map fE) ≫ E' :=
      congrArg (fun q => q ≫ E') hmap
    _ = HZ.map (mapExtendIso (G := G) R.cocomplex).hom ≫ (E ≫ HN.map fN) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun q => HZ.map (mapExtendIso (G := G) R.cocomplex).hom ≫ q) hext)
    _ = _ := (Category.assoc _ _ _).symm

variable [HasInjectiveResolutions C]

/-- The original right-derived functor, computed from the integer resolution. -/
def resolutionHomologyIsoRightDerived (R : InjectiveResolution F) (n : ℕ) :
    ((G.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex).homology (n : ℤ) ≅
      (G.rightDerived n).obj F :=
  resolutionHomologyIsoCocomplex G R n ≪≫ (R.isoRightDerivedObj G n).symm

/-- The canonical right-derived map agrees with the original resolution map. -/
theorem resolutionHomologyIsoRightDerived_naturality
    (R : InjectiveResolution F) (R' : InjectiveResolution F') {g : F ⟶ F'}
    (φ : InjectiveResolution.Hom R R' g) (n : ℕ) :
    (HomologicalComplex.homologyFunctor AddCommGrp.{v} (.up ℤ) (n : ℤ)).map
        ((G.mapHomologicalComplex (.up ℤ)).map φ.hom') ≫
      (resolutionHomologyIsoRightDerived G R' n).hom =
    (resolutionHomologyIsoRightDerived G R n).hom ≫ (G.rightDerived n).map g := by
  have h := InjectiveResolution.isoRightDerivedObj_inv_naturality g R R' φ.hom
    (by simpa using φ.ι_f_zero_comp_hom_f_zero) G n
  simp only [Functor.comp_map] at h
  simp only [resolutionHomologyIsoRightDerived, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, resolutionHomologyIsoCocomplex_naturality,
    Category.assoc, ← h, ← Category.assoc]

end KltDP.CochainComparison

namespace KltDP.SheafCochainComparison

variable {X : TopCat.{u}}
  {F F' : Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u}}

/-- The actual constant-integer Hom-complex homology computes derived global sections. -/
def homComplexHomologyIsoRightDerived (R : InjectiveResolution F) (n : ℕ) :
    (((CochainComplex.singleFunctor _ 0).obj (constantIntegers X)).HomComplex
      R.cochainComplex).homology (n : ℤ) ≅
        ((globalSectionsFunctor X).rightDerived n).obj F :=
  resolutionHomologyIso R (n : ℤ) ≪≫
    KltDP.CochainComparison.resolutionHomologyIsoRightDerived (globalSectionsFunctor X) R n

/-- This comparison is natural for the map constructed from every original coefficient map. -/
theorem homComplexHomologyIsoRightDerived_naturality
    (R : InjectiveResolution F) (R' : InjectiveResolution F') (g : F ⟶ F') (n : ℕ) :
    (HomologicalComplex.homologyFunctor AddCommGrp.{u} (.up ℤ) (n : ℤ)).map
        (KltDP.HomComplexComparison.homComplexPostcomp
          (InjectiveResolution.Hom.ofMorphism R R' g).hom') ≫
      (homComplexHomologyIsoRightDerived R' n).hom =
    (homComplexHomologyIsoRightDerived R n).hom ≫
      ((globalSectionsFunctor X).rightDerived n).map g := by
  simp only [homComplexHomologyIsoRightDerived, Iso.trans_hom]
  rw [← Category.assoc, resolutionHomologyIso_naturality,
    Category.assoc, KltDP.CochainComparison.resolutionHomologyIsoRightDerived_naturality,
    ← Category.assoc]

end KltDP.SheafCochainComparison

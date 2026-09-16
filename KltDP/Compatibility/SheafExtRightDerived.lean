/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Vasily Ilin

Adapted from Vilin97/MazurTheorem
9327963d4ec14fba49c7b14b004fd00707ffc2e9,
SheafDerivedGlobalSections: the final comparison and naturality blocks.
The original pinned sheaf objects and previously constructed project
comparison maps are retained.
-/
import KltDP.Compatibility.InjectiveResolutionExtComparison
import KltDP.Compatibility.ResolutionSectionsRightDerived

/-!
# Original Ext sheaf cohomology and derived global sections

The original constant-integer Ext group is compared with the canonical
right-derived global-sections functor through an actual injective resolution.
The comparison is natural for the original coefficient morphisms. Its chosen
resolution specialization gives an isomorphism of the original functors.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.SheafCochainComparison

variable {X : TopCat.{u}}
  {F F' : Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u}}

/-- The original sheaf Ext group as the homology of the original
constant-integer Hom complex of an actual injective resolution. -/
def extHomologyAddEquiv (R : InjectiveResolution F) (n : ℕ) :
    Sheaf.H F n ≃+
      (((CochainComplex.singleFunctor _ 0).obj (constantIntegers X)).HomComplex
        R.cochainComplex).homology (n : ℤ) := by
  letI := HasDerivedCategory.standard
    (Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u})
  exact (InjectiveResolutionExtComparison.extAddEquiv R (constantIntegers X) n).trans
    (CochainComplex.HomComplex.homologyAddEquiv _ R.cochainComplex (n : ℤ)).symm

/-- The Hom-complex comparison uses the map constructed from the actual
coefficient morphism, rather than a separately chosen action on homology. -/
theorem extHomologyAddEquiv_naturality
    (R : InjectiveResolution F) (R' : InjectiveResolution F') (g : F ⟶ F')
    (n : ℕ) (x : Sheaf.H F n) :
    extHomologyAddEquiv R' n (Sheaf.H.map g n x) =
      (HomologicalComplex.homologyFunctor AddCommGrp.{u} (.up ℤ) (n : ℤ)).map
        (HomComplexComparison.homComplexPostcomp
          (InjectiveResolution.Hom.ofMorphism R R' g).hom')
        (extHomologyAddEquiv R n x) := by
  letI := HasDerivedCategory.standard
    (Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u})
  apply (CochainComplex.HomComplex.homologyAddEquiv _ R'.cochainComplex (n : ℤ)).injective
  change (CochainComplex.HomComplex.homologyAddEquiv _ R'.cochainComplex (n : ℤ))
      ((CochainComplex.HomComplex.homologyAddEquiv _ R'.cochainComplex (n : ℤ)).symm
        (InjectiveResolutionExtComparison.extAddEquiv R' (constantIntegers X) n
          (x.comp (CategoryTheory.Abelian.Ext.mk₀ g) (add_zero n)))) = _
  rw [AddEquiv.apply_symm_apply,
    InjectiveResolutionExtComparison.extAddEquiv_postcomp R R' (constantIntegers X) n g
      (InjectiveResolution.Hom.ofMorphism R R' g),
    HomComplexComparison.homologyAddEquiv_homComplexPostcomp]
  change _ = HomComplexComparison.cohomologyClassPostcomp _ _
    ((CochainComplex.HomComplex.homologyAddEquiv _ R.cochainComplex (n : ℤ))
      ((CochainComplex.HomComplex.homologyAddEquiv _ R.cochainComplex (n : ℤ)).symm _))
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- The original Ext cohomology group computes canonical derived global
sections, using the supplied actual injective resolution. -/
def extRightDerivedAddEquiv (R : InjectiveResolution F) (n : ℕ) :
    Sheaf.H F n ≃+ ((globalSectionsFunctor X).rightDerived n).obj F :=
  (extHomologyAddEquiv R n).trans
    (homComplexHomologyIsoRightDerived R n).addCommGroupIsoToAddEquiv

/-- The comparison intertwines every original sheaf coefficient map. -/
theorem extRightDerivedAddEquiv_naturality
    (R : InjectiveResolution F) (R' : InjectiveResolution F') (g : F ⟶ F')
    (n : ℕ) (x : Sheaf.H F n) :
    extRightDerivedAddEquiv R' n (Sheaf.H.map g n x) =
      ((globalSectionsFunctor X).rightDerived n).map g
        (extRightDerivedAddEquiv R n x) := by
  change (homComplexHomologyIsoRightDerived R' n).hom
      (extHomologyAddEquiv R' n (Sheaf.H.map g n x)) =
    ((globalSectionsFunctor X).rightDerived n).map g
      ((homComplexHomologyIsoRightDerived R n).hom (extHomologyAddEquiv R n x))
  rw [extHomologyAddEquiv_naturality]
  exact ConcreteCategory.congr_hom
    (homComplexHomologyIsoRightDerived_naturality R R' g n)
    (extHomologyAddEquiv R n x)

/-- Specialize to the pinned actual choice of an injective resolution
for each sheaf, retaining the original Ext and right-derived functors. -/
def sheafHRightDerivedIso (X : TopCat.{u}) (n : ℕ) :
    Sheaf.functorH (Opens.grothendieckTopology X) n ≅
      (globalSectionsFunctor X).rightDerived n :=
  NatIso.ofComponents
    (F := Sheaf.functorH (Opens.grothendieckTopology X) n)
    (G := (globalSectionsFunctor X).rightDerived n)
    (fun F => (extRightDerivedAddEquiv (injectiveResolution F) n).toAddCommGrpIso)
    (fun {F F'} (g : F ⟶ F') => by
      apply AddCommGrp.ext
      intro x
      change extRightDerivedAddEquiv (injectiveResolution F') n (Sheaf.H.map g n x) =
        ((globalSectionsFunctor X).rightDerived n).map g
          (extRightDerivedAddEquiv (injectiveResolution F) n x)
      exact extRightDerivedAddEquiv_naturality (X := X) (F := F) (F' := F')
        (injectiveResolution F) (injectiveResolution F') g n x)

/-- The natural isomorphism keeps the explicitly constructed resolution
comparison as its component map. -/
theorem sheafHRightDerivedIso_hom_app (n : ℕ) (x : Sheaf.H F n) :
    (sheafHRightDerivedIso X n).hom.app F x =
      extRightDerivedAddEquiv (injectiveResolution F) n x := rfl

end KltDP.SheafCochainComparison

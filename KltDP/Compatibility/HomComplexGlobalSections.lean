/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Vasily Ilin

Adapted from Vilin97/MazurTheorem
9327963d4ec14fba49c7b14b004fd00707ffc2e9,
SheafDerivedGlobalSections: the cochain-to-sections and canonical
constant-integer representability blocks. The existing project
postcomposition and integer-resolution definitions are reused.
-/
import KltDP.Compatibility.AbelianSheafCohomology
import KltDP.Compatibility.HomComplexSingleCochain
import KltDP.Compatibility.HomComplexCohomologyNaturality
import KltDP.Compatibility.InjectiveResolutionExtend
import Mathlib.CategoryTheory.Sites.GlobalSections

/-!
# The actual global-sections complex as a Hom complex

The representing object is the original constant integer sheaf, and the
representing equivalence is constructed by the canonical constant-sheaf
adjunction and evaluation at the lifted integer one. This gives an
isomorphism of the original complexes, compatible with differentials,
coefficient maps, and the constructed maps of actual injective resolutions.
No representing equivalence, K-injectivity, Ext comparison, or transported
scalar action is an input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.SheafCochainComparison

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The pinned canonical right adjoint to the constant sheaf functor. -/
abbrev globalSectionsFunctor (X : TopCat.{u}) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u} ⥤ AddCommGrp.{u} :=
  Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrp.{u}

/-- The same constant lifted-integer object used in the definition of `Sheaf.H`. -/
abbrev constantIntegers (X : TopCat.{u}) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u} :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrp.{u}).obj
    (AddCommGrp.of (ULift.{u} ℤ))

instance globalSectionsFunctor_additive (X : TopCat.{u}) :
    (globalSectionsFunctor X).Additive :=
  (constantSheafΓAdj (Opens.grothendieckTopology X) AddCommGrp.{u}).right_adjoint_additive

variable {X : TopCat.{u}}

/-- The canonical adjunction, followed by evaluation at one. -/
def homToGlobalSectionsEquiv
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u}) :
    (constantIntegers X ⟶ F) ≃+ (globalSectionsFunctor X).obj F :=
  ((constantSheafΓAdj (Opens.grothendieckTopology X) AddCommGrp.{u}).homAddEquiv
    (AddCommGrp.of (ULift.{u} ℤ)) F).trans
      (AddCommGrp.uliftZMultiplesAddEquiv ((globalSectionsFunctor X).obj F))

theorem homToGlobalSectionsEquiv_naturality
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u}}
    (a : constantIntegers X ⟶ F) (g : F ⟶ G) :
    homToGlobalSectionsEquiv G (a ≫ g) =
      (globalSectionsFunctor X).map g (homToGlobalSectionsEquiv F a) := by
  change AddCommGrp.uliftZMultiplesAddEquiv _
    ((constantSheafΓAdj (Opens.grothendieckTopology X) AddCommGrp.{u}).homEquiv _ _
      (a ≫ g)) = _
  rw [(constantSheafΓAdj (Opens.grothendieckTopology X)
    AddCommGrp.{u}).homEquiv_naturality_right]
  rfl

/-- The original degree-`n` cochain is sent to its canonical global section. -/
def cochainToSectionsEquiv
    (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u}) ℤ)
    (n : ℤ) :
    CochainComplex.HomComplex.Cochain
      ((CochainComplex.singleFunctor _ 0).obj (constantIntegers X)) K n ≃+
      (globalSectionsFunctor X).obj (K.X n) :=
  (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add n)).trans
    (homToGlobalSectionsEquiv (K.X n))

theorem cochainToSectionsEquiv_fromSingleMk
    (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u}) ℤ)
    (n : ℤ) (a : constantIntegers X ⟶ K.X n) :
    cochainToSectionsEquiv K n
      (CochainComplex.HomComplex.Cochain.fromSingleMk a (zero_add n)) =
      homToGlobalSectionsEquiv (K.X n) a :=
  congrArg (homToGlobalSectionsEquiv (K.X n))
    (CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk a (zero_add n))

/-- A canonical isomorphism of complexes, with the actual differentials. -/
def homComplexIsoSections
    (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u}) ℤ) :
    ((CochainComplex.singleFunctor _ 0).obj (constantIntegers X)).HomComplex K ≅
      ((globalSectionsFunctor X).mapHomologicalComplex (.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (cochainToSectionsEquiv K n).toAddCommGrpIso) fun i j _ => by
      apply AddCommGrp.ext
      intro z
      obtain ⟨a, rfl⟩ :=
        CochainComplex.HomComplex.Cochain.fromSingleMk_surjective z i (zero_add i)
      change (globalSectionsFunctor X).map (K.d i j)
          (cochainToSectionsEquiv K i
            (CochainComplex.HomComplex.Cochain.fromSingleMk a (zero_add i))) =
        cochainToSectionsEquiv K j (CochainComplex.HomComplex.δ i j
          (CochainComplex.HomComplex.Cochain.fromSingleMk a (zero_add i)))
      rw [cochainToSectionsEquiv_fromSingleMk,
        CochainComplex.HomComplex.Cochain.δ_fromSingleMk a (zero_add i) j j (zero_add j),
        cochainToSectionsEquiv_fromSingleMk]
      exact (homToGlobalSectionsEquiv_naturality a (K.d i j)).symm

/-- The component formula retains the canonical adjunction map. -/
theorem homComplexIsoSections_hom_f_apply
    (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u}) ℤ)
    (n : ℤ) (z : CochainComplex.HomComplex.Cochain
      ((CochainComplex.singleFunctor _ 0).obj (constantIntegers X)) K n) :
    ((homComplexIsoSections K).hom.f n).hom z = cochainToSectionsEquiv K n z := rfl

/-- Naturality for the original postcomposition chain map. -/
theorem homComplexIsoSections_naturality
    {K L : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u}) ℤ}
    (g : K ⟶ L) :
    KltDP.HomComplexComparison.homComplexPostcomp g ≫ (homComplexIsoSections L).hom =
      (homComplexIsoSections K).hom ≫
        ((globalSectionsFunctor X).mapHomologicalComplex (.up ℤ)).map g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrp.ext
  intro z
  obtain ⟨a, rfl⟩ :=
    CochainComplex.HomComplex.Cochain.fromSingleMk_surjective z n (zero_add n)
  change cochainToSectionsEquiv L n
      ((CochainComplex.HomComplex.Cochain.fromSingleMk a (zero_add n)).comp
        (.ofHom g) (add_zero n)) =
    (globalSectionsFunctor X).map (g.f n)
      (cochainToSectionsEquiv K n
        (CochainComplex.HomComplex.Cochain.fromSingleMk a (zero_add n)))
  rw [← CochainComplex.HomComplex.Cochain.fromSingleMk_postcomp,
    cochainToSectionsEquiv_fromSingleMk, cochainToSectionsEquiv_fromSingleMk]
  exact homToGlobalSectionsEquiv_naturality a (g.f n)

/-- Specialization to the original integer extension of an actual injective resolution. -/
def resolutionHomologyIso
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u}}
    (R : InjectiveResolution F) (n : ℤ) :
    (((CochainComplex.singleFunctor _ 0).obj (constantIntegers X)).HomComplex
      R.cochainComplex).homology n ≅
      (((globalSectionsFunctor X).mapHomologicalComplex (.up ℤ)).obj
        R.cochainComplex).homology n :=
  (HomologicalComplex.homologyFunctor AddCommGrp.{u} (.up ℤ) n).mapIso
    (homComplexIsoSections R.cochainComplex)

/-- The comparison commutes with the map constructed from each coefficient morphism. -/
theorem resolutionHomologyIso_naturality
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u}}
    (R : InjectiveResolution F) (R' : InjectiveResolution G) (g : F ⟶ G) (n : ℤ) :
    (HomologicalComplex.homologyFunctor AddCommGrp.{u} (.up ℤ) n).map
        (KltDP.HomComplexComparison.homComplexPostcomp
          (InjectiveResolution.Hom.ofMorphism R R' g).hom') ≫
      (resolutionHomologyIso R' n).hom =
    (resolutionHomologyIso R n).hom ≫
      (HomologicalComplex.homologyFunctor AddCommGrp.{u} (.up ℤ) n).map
        (((globalSectionsFunctor X).mapHomologicalComplex (.up ℤ)).map
          (InjectiveResolution.Hom.ofMorphism R R' g).hom') := by
  change (HomologicalComplex.homologyFunctor AddCommGrp.{u} (.up ℤ) n).map _ ≫
      (HomologicalComplex.homologyFunctor AddCommGrp.{u} (.up ℤ) n).map _ =
    (HomologicalComplex.homologyFunctor AddCommGrp.{u} (.up ℤ) n).map _ ≫
      (HomologicalComplex.homologyFunctor AddCommGrp.{u} (.up ℤ) n).map _
  simpa only [Functor.map_comp] using congrArg
    (HomologicalComplex.homologyFunctor AddCommGrp.{u} (.up ℤ) n).map
    (homComplexIsoSections_naturality (InjectiveResolution.Hom.ofMorphism R R' g).hom')

end KltDP.SheafCochainComparison

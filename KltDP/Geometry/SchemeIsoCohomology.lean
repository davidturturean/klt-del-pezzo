import KltDP.Compatibility.EquivalenceRightDerived
import KltDP.Compatibility.NatIsoRightDerived
import KltDP.Compatibility.SheafExtRightDerived
import KltDP.Geometry.SchemeAbelianSheafPushforward

/-!
# Cohomology under a scheme isomorphism

The original sheaf pushforward equivalence and its global-sections comparison
give a natural isomorphism on Ext-based sheaf cohomology. For scheme modules,
coefficient naturality preserves the original action of the base ring in every
degree. No acyclicity or finiteness hypothesis is imposed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

open KltDP.SheafCochainComparison

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}}

/-- The actual abelian-sheaf cohomology functors agree under an isomorphism. -/
def schemeAbelianSheafCohomologyIso (e : X ≅ Y) (n : ℕ) :
    schemeAbelianSheafPushforward e.hom ⋙
        Sheaf.functorH (Opens.grothendieckTopology Y) n ≅
      Sheaf.functorH (Opens.grothendieckTopology X) n := by
  letI : HasInjectiveResolutions
      (TopCat.Sheaf AddCommGrp.{u} (X : TopCat.{u})) :=
    inferInstanceAs (HasInjectiveResolutions
      (CategoryTheory.Sheaf
        (Opens.grothendieckTopology (X : TopCat.{u})) AddCommGrp.{u}))
  letI : HasInjectiveResolutions
      (TopCat.Sheaf AddCommGrp.{u} (Y : TopCat.{u})) :=
    inferInstanceAs (HasInjectiveResolutions
      (CategoryTheory.Sheaf
        (Opens.grothendieckTopology (Y : TopCat.{u})) AddCommGrp.{u}))
  letI : Functor.Additive
      (C := TopCat.Sheaf AddCommGrp.{u} (X : TopCat.{u})) (D := AddCommGrp.{u})
      (globalSectionsFunctor (X : TopCat.{u})) :=
    globalSectionsFunctor_additive (X : TopCat.{u})
  letI : Functor.Additive
      (C := TopCat.Sheaf AddCommGrp.{u} (Y : TopCat.{u})) (D := AddCommGrp.{u})
      (globalSectionsFunctor (Y : TopCat.{u})) :=
    globalSectionsFunctor_additive (Y : TopCat.{u})
  letI : (schemeAbelianSheafPushforward e.hom).Additive :=
    schemeAbelianSheafPushforward_additive e.hom
  letI : (schemeAbelianSheafPushforward e.hom ⋙
      globalSectionsFunctor (Y : TopCat.{u})).Additive := by
    infer_instance
  letI : (schemeAbelianSheafIsoEquivalence e).functor.Additive := by
    change (schemeAbelianSheafPushforward e.hom).Additive
    infer_instance
  exact isoWhiskerLeft (schemeAbelianSheafPushforward e.hom)
      (sheafHRightDerivedIso (Y : TopCat.{u}) n) ≪≫
    (schemeAbelianSheafIsoEquivalence e).rightDerivedIso
      (globalSectionsFunctor (Y : TopCat.{u})) n ≪≫
    NatIso.rightDerived (schemeAbelianPushforwardGlobalSectionsIso e.hom) n ≪≫
    (sheafHRightDerivedIso (X : TopCat.{u}) n).symm

namespace ModuleCohomology

/-- The original module pushforward and original cohomology form this comparison. -/
def pushforwardIsoCohomologyIso (e : X ≅ Y) (n : ℕ) :
    schemeModulePushforward e.hom ⋙ zariskiFunctor Y n ≅ zariskiFunctor X n :=
  (Functor.associator (schemeModulePushforward e.hom)
    (_root_.SheafOfModules.toSheaf Y.ringCatSheaf)
    (Sheaf.functorH (Opens.grothendieckTopology Y) n)).symm ≪≫
  isoWhiskerRight (schemeModulePushforwardToSheafIso e.hom)
    (Sheaf.functorH (Opens.grothendieckTopology Y) n) ≪≫
  Functor.associator (_root_.SheafOfModules.toSheaf X.ringCatSheaf)
    (schemeAbelianSheafPushforward e.hom)
    (Sheaf.functorH (Opens.grothendieckTopology Y) n) ≪≫
  isoWhiskerLeft (_root_.SheafOfModules.toSheaf X.ringCatSheaf)
    (schemeAbelianSheafCohomologyIso e n)

/-- The induced additive equivalence on the original cohomology groups. -/
def pushforwardIsoHAddEquiv (e : X ≅ Y) (M : X.Modules) (n : ℕ) :
    H ((schemeModulePushforward e.hom).obj M) n ≃+ H M n :=
  ((pushforwardIsoCohomologyIso e n).app M).addCommGroupIsoToAddEquiv

set_option maxRecDepth 4096 in
/-- The equivalence commutes with every original coefficient morphism. -/
theorem pushforwardIsoHAddEquiv_naturality (e : X ≅ Y)
    {M N : X.Modules} (f : M ⟶ N) (n : ℕ)
    (x : H ((schemeModulePushforward e.hom).obj M) n) :
    pushforwardIsoHAddEquiv e N n
        ((zariskiFunctor Y n).map ((schemeModulePushforward e.hom).map f) x) =
      (zariskiFunctor X n).map f (pushforwardIsoHAddEquiv e M n x) :=
  ConcreteCategory.congr_hom ((pushforwardIsoCohomologyIso e n).hom.naturality f) x

set_option maxRecDepth 4096 in
/-- Global scalars act through the actual pullback of the original function. -/
theorem pushforwardIsoHAddEquiv_smul (e : X ≅ Y) (M : X.Modules) (n : ℕ)
    (r : Γ(Y, ⊤)) (x : H ((schemeModulePushforward e.hom).obj M) n) :
    letI := globalSectionsCohomologyModule ((schemeModulePushforward e.hom).obj M) n
    letI := globalSectionsCohomologyModule M n
    pushforwardIsoHAddEquiv e M n (r • x) =
      e.hom.appTop r • pushforwardIsoHAddEquiv e M n x := by
  letI := globalSectionsCohomologyModule ((schemeModulePushforward e.hom).obj M) n
  letI := globalSectionsCohomologyModule M n
  change pushforwardIsoHAddEquiv e M n
      ((zariskiFunctor Y n).map
        (globalSmulHom ((schemeModulePushforward e.hom).obj M) r) x) =
    (zariskiFunctor X n).map (globalSmulHom M (e.hom.appTop r))
      (pushforwardIsoHAddEquiv e M n x)
  rw [globalSmulHom_pushforward]
  exact pushforwardIsoHAddEquiv_naturality e (globalSmulHom M (e.hom.appTop r)) n x

variable {A : Type u} [CommRing A]

set_option maxRecDepth 4096 in
/-- Cohomology is preserved linearly for the original morphisms to the base. -/
def pushforwardIsoHBaseRingLinearEquiv (e : X ≅ Y)
    (g : Y ⟶ Spec (CommRingCat.of A)) (M : X.Modules) (n : ℕ) :
    letI := baseRingModule g ((schemeModulePushforward e.hom).obj M) n
    letI := baseRingModule (e.hom ≫ g) M n
    H ((schemeModulePushforward e.hom).obj M) n ≃ₗ[A] H M n := by
  letI := baseRingModule g ((schemeModulePushforward e.hom).obj M) n
  letI := baseRingModule (e.hom ≫ g) M n
  refine { pushforwardIsoHAddEquiv e M n with map_smul' := ?_ }
  intro a x
  change pushforwardIsoHAddEquiv e M n
      ((zariskiFunctor Y n).map
        (globalSmulHom ((schemeModulePushforward e.hom).obj M)
          (g.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) x) =
    (zariskiFunctor X n).map
      (globalSmulHom M ((e.hom ≫ g).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))
      (pushforwardIsoHAddEquiv e M n x)
  rw [globalSmulHom_pushforward]
  simpa only [appTop_baseRingScalar] using
    pushforwardIsoHAddEquiv_naturality e
      (globalSmulHom M (e.hom.appTop
        (g.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))) n x

/-- The linear comparison has the same underlying map as the natural cohomology comparison. -/
theorem pushforwardIsoHBaseRingLinearEquiv_apply (e : X ≅ Y)
    (g : Y ⟶ Spec (CommRingCat.of A)) (M : X.Modules) (n : ℕ)
    (x : H ((schemeModulePushforward e.hom).obj M) n) :
    letI := baseRingModule g ((schemeModulePushforward e.hom).obj M) n
    letI := baseRingModule (e.hom ≫ g) M n
    pushforwardIsoHBaseRingLinearEquiv e g M n x = pushforwardIsoHAddEquiv e M n x := rfl

end ModuleCohomology

end KltDP.Geometry

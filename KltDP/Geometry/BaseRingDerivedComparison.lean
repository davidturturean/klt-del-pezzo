import KltDP.Geometry.BaseRingCohomology
import KltDP.Compatibility.SheafExtRightDerived

/-!
# The canonical base-ring action under derived global sections

The original module cohomology functor is compared with derived global
sections of its original underlying abelian sheaf. Multiplication by a base
scalar is carried to the right-derived map of the original multiplication
morphism. No action is defined by transport through an additive equivalence.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ModuleCohomology

/-- The existing Ext-based module cohomology functor identifies with
derived global sections of the original underlying abelian sheaf. -/
def zariskiRightDerivedIso (X : Scheme.{u}) (n : ℕ) :
    zariskiFunctor X n ≅
      SheafOfModules.toSheaf X.ringCatSheaf ⋙
        (SheafCochainComparison.globalSectionsFunctor (X : TopCat)).rightDerived n :=
  isoWhiskerLeft (SheafOfModules.toSheaf X.ringCatSheaf)
    (SheafCochainComparison.sheafHRightDerivedIso (X : TopCat) n)

/-- The comparison uses the original multiplication morphism and the
original cohomology scalar action induced by the actual map to Spec A. -/
theorem zariskiRightDerivedIso_hom_app_smul
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (M : X.Modules) (n : ℕ)
    (a : A) (x : H M n) :
    letI := baseRingModule f M n
    (zariskiRightDerivedIso X n).hom.app M (a • x) =
      ((SheafCochainComparison.globalSectionsFunctor (X : TopCat)).rightDerived n).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map
          (globalSmulHom M
            (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))))
        ((zariskiRightDerivedIso X n).hom.app M x) := by
  let r : Γ(X, ⊤) :=
    f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)
  let g : M ⟶ M := globalSmulHom M r
  change (zariskiRightDerivedIso X n).hom.app M ((zariskiFunctor X n).map g x) =
    ((SheafCochainComparison.globalSectionsFunctor (X : TopCat)).rightDerived n).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map g)
      ((zariskiRightDerivedIso X n).hom.app M x)
  exact ConcreteCategory.congr_hom ((zariskiRightDerivedIso X n).hom.naturality g) x

end KltDP.Geometry.ModuleCohomology

import KltDP.Geometry.AffineModuleCounitBasis
import KltDP.Geometry.AffineModuleForgetFullyFaithful
import KltDP.Geometry.AffineModuleTildeFunctor

/-!
# The actual affine tilde-Gamma counit

The compatible basic-open localization maps give a morphism of original
structure-sheaf modules from the tilde sheaf of global sections to M.
The proof that forgetting to R-module sheaves is fully faithful supplies
structure-sheaf linearity; it does not assume a comparison isomorphism.
The counit keeps the original restrictions of global sections and is
natural in M. Its invertibility for quasicoherent sheaves is a separate
geometric result.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineModuleTilde

variable {R : Type u} [CommRing R]

/-- The original basic-open maps, now as a morphism of actual structure-sheaf modules. -/
def counit (M : (Spec (.of R)).Modules) : (sectionModule M ⊤).tilde ⟶ M :=
  (modulesSpecToSheafFullyFaithful R).preimage (counitModuleSheaf M)

@[simp]
theorem modulesSpecToSheaf_map_counit (M : (Spec (.of R)).Modules) :
    (modulesSpecToSheaf R).map (counit M) = counitModuleSheaf M :=
  (modulesSpecToSheafFullyFaithful R).map_preimage _

/-- Passing back to actual module sheaves retains every original component function. -/
theorem counit_app_apply (M : (Spec (.of R)).Modules) (U : (Spec (.of R)).Opens)
    (s : (sectionModule M ⊤).tilde.val.obj (op U)) :
    (counit M).val.app (op U) s = (counitModuleSheaf M).val.app (op U) s := by
  have h := congrArg (fun φ => φ.val.app (op U)) (modulesSpecToSheaf_map_counit M)
  exact ConcreteCategory.congr_hom h s

/-- A canonical section goes to the actual restriction of the original global section. -/
@[simp]
theorem counit_toOpen (M : (Spec (.of R)).Modules) (U : (Spec (.of R)).Opens)
    (m : sectionModule M ⊤) :
    (counit M).val.app (op U) (ModuleCat.Tilde.toOpen (sectionModule M ⊤) U m) =
      M.val.map (homOfLE le_top).op m := by
  rw [counit_app_apply]
  exact ConcreteCategory.congr_hom (toOpen_counitModuleSheaf_app M U) m

/-- Morphisms out of the original tilde sheaf are determined by canonical basic-open sections. -/
theorem tilde_hom_ext {N : ModuleCat.{u} R} {M : (Spec (.of R)).Modules}
    {φ ψ : N.tilde ⟶ M}
    (h : ∀ (f : R) (n : N),
      φ.val.app (op (PrimeSpectrum.basicOpen f))
          (ModuleCat.Tilde.toOpen N (PrimeSpectrum.basicOpen f) n) =
        ψ.val.app (op (PrimeSpectrum.basicOpen f))
          (ModuleCat.Tilde.toOpen N (PrimeSpectrum.basicOpen f) n)) : φ = ψ := by
  apply (modulesSpecToSheafFullyFaithful R).map_injective
  apply CategoryTheory.Sheaf.hom_ext _ _
  apply TopCat.Sheaf.hom_ext _ _ PrimeSpectrum.isBasis_basic_opens
  intro f
  apply ModuleCat.hom_ext
  apply IsLocalizedModule.ext (Submonoid.powers f)
    (ModuleCat.Tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom
    (sectionScalar_map_units M f le_rfl)
  apply LinearMap.ext
  intro n
  exact h f n

/-- The actual counit commutes with every original morphism of affine module sheaves. -/
theorem counit_naturality {M N : (Spec (.of R)).Modules} (φ : M ⟶ N) :
    map ((globalSectionsFunctor R).map φ) ≫ counit N = counit M ≫ φ := by
  apply tilde_hom_ext
  intro f m
  change (counit N).val.app (op (PrimeSpectrum.basicOpen f))
      ((map ((globalSectionsFunctor R).map φ)).val.app (op (PrimeSpectrum.basicOpen f))
        (ModuleCat.Tilde.toOpen (sectionModule M ⊤) (PrimeSpectrum.basicOpen f) m)) =
    φ.val.app (op (PrimeSpectrum.basicOpen f))
      ((counit M).val.app (op (PrimeSpectrum.basicOpen f))
        (ModuleCat.Tilde.toOpen (sectionModule M ⊤) (PrimeSpectrum.basicOpen f) m))
  have hmap := congrArg
    (fun s : (sectionModule N ⊤).tilde.val.obj (op (PrimeSpectrum.basicOpen f)) =>
      (counit N).val.app (op (PrimeSpectrum.basicOpen f)) s)
    (map_app_toOpen (M := sectionModule M ⊤) (N := sectionModule N ⊤)
      ((globalSectionsFunctor R).map φ) (PrimeSpectrum.basicOpen f) m)
  have hN := counit_toOpen N (PrimeSpectrum.basicOpen f)
    (((globalSectionsFunctor R).map φ) m)
  have hnat :=
    (PresheafOfModules.naturality_apply φ.val
      (homOfLE (show PrimeSpectrum.basicOpen f ≤ (⊤ : (Spec (.of R)).Opens)
        from le_top)).op m).symm
  have hM := congrArg
    (fun s : M.val.obj (op (PrimeSpectrum.basicOpen f)) =>
      φ.val.app (op (PrimeSpectrum.basicOpen f)) s)
    (counit_toOpen M (PrimeSpectrum.basicOpen f) m).symm
  exact hmap.trans (hN.trans (hnat.trans hM))

/-- The canonical affine counit, bundled as its actual natural transformation. -/
def counitNatTrans (R : Type u) [CommRing R] :
    globalSectionsFunctor R ⋙ functor R ⟶ 𝟭 ((Spec (.of R)).Modules) where
  app := counit
  naturality := by
    intro M N φ
    exact counit_naturality φ

end KltDP.Geometry.AffineModuleTilde

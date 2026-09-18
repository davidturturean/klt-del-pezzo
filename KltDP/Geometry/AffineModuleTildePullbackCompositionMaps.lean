import KltDP.Geometry.AffineModuleTildePullbackComp
import KltDP.Geometry.AffineModuleTildeSemilinearMap

/-!
# Original semilinear maps through the actual affine pullback composition

The two routes around the quotient ambient square use the original
composition isomorphism on opposite sides of a semilinear map. The proved
affine comparison composition and its original naturality normalize both
routes to the same scalar-extension map. No new pullback is constructed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.AffineModuleTilde

open AffineModuleTildeSemilinearMap

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  (φ : A →+* B) (ψ : B →+* C)

/-- The original outer semilinear map follows the original affine composition. -/
theorem pullbackMap_after_pullbackIso_comp (M : ModuleCat.{u} A) (N : ModuleCat.{u} C)
    (a : (ModuleCat.extendScalars φ).obj M →ₛₗ[ψ] N) :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom ψ))).map (pullbackIso φ M).hom ≫
        pullbackMap ψ a =
      (schemeModulePullbackCompIso (Spec.map (CommRingCat.ofHom ψ))
        (Spec.map (CommRingCat.ofHom φ))).hom.app M.tilde ≫
      (eqToIso (congrArg (fun f => (schemeModulePullback f).obj M.tilde)
        (specMap_comp_eq φ ψ))).hom ≫
      (pullbackIso (ψ.comp φ) M).hom ≫
      map ((ModuleCat.extendScalarsComp φ ψ).hom.app M ≫ extendHom ψ a) := by
  unfold pullbackMap
  rw [← Category.assoc, pullbackIso_comp]
  simp only [map_comp, Category.assoc]

/-- The original inner semilinear map is natural through the same affine composition. -/
theorem pullbackIso_after_pullbackMap_comp (M : ModuleCat.{u} A) (N : ModuleCat.{u} B)
    (a : M →ₛₗ[φ] N) :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom ψ))).map (pullbackMap φ a) ≫
        (pullbackIso ψ N).hom =
      (schemeModulePullbackCompIso (Spec.map (CommRingCat.ofHom ψ))
        (Spec.map (CommRingCat.ofHom φ))).hom.app M.tilde ≫
      (eqToIso (congrArg (fun f => (schemeModulePullback f).obj M.tilde)
        (specMap_comp_eq φ ψ))).hom ≫
      (pullbackIso (ψ.comp φ) M).hom ≫
      map ((ModuleCat.extendScalarsComp φ ψ).hom.app M ≫
        (ModuleCat.extendScalars ψ).map (extendHom φ a)) := by
  have hn := (pullbackTildeIso ψ).hom.naturality (extendHom φ a)
  change (schemeModulePullback (Spec.map (CommRingCat.ofHom ψ))).map
      (map (extendHom φ a)) ≫ (pullbackIso ψ N).hom =
    (pullbackIso ψ ((ModuleCat.extendScalars φ).obj M)).hom ≫
      map ((ModuleCat.extendScalars ψ).map (extendHom φ a)) at hn
  unfold pullbackMap
  rw [CategoryTheory.Functor.map_comp, Category.assoc, hn, ← Category.assoc, pullbackIso_comp]
  simp only [map_comp, Category.assoc]

end KltDP.Geometry.AffineModuleTilde

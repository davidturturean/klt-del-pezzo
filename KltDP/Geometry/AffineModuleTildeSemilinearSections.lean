import KltDP.Geometry.AffineModuleTildeSemilinearMap

/-!
# Original affine semilinear pullback on original module sections

The original affine pullback transpose sends a module element to its
canonical section. The actual scalar-extension adjunction then gives the
canonical section of its original semilinear image.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineModuleTildeSemilinearMap

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)

/-- The original composite adjunction is evaluated on the original canonical section. -/
theorem pulledTilde_homEquiv_apply (M : ModuleCat.{u} A)
    (N : (Spec (CommRingCat.of B)).Modules)
    (a : (schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).obj M.tilde ⟶ N)
    (m : M) :
    (AffineModuleTilde.pulledTildeAdjunction φ).homEquiv M N a m =
      ((schemeModulePullbackPushforwardAdjunction
        (Spec.map (CommRingCat.ofHom φ))).homEquiv M.tilde N a).val.app (op ⊤)
        (ModuleCat.Tilde.toOpen M ⊤ m) := rfl

/-- The actual semilinear pullback map has the canonical section of the actual
semilinear image as its original affine transpose. -/
theorem pullbackMap_transpose_apply {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (a : M →ₛₗ[φ] N) (m : M) :
    (AffineModuleTilde.pulledTildeAdjunction φ).homEquiv M N.tilde
        (pullbackMap φ a) m = ModuleCat.Tilde.toOpen N ⊤ (a m) := by
  rw [pullbackMap, Adjunction.homEquiv_naturality_right]
  change (AffineModuleTilde.map (extendHom φ a)).val.app (op ⊤)
    ((AffineModuleTilde.pulledTildeAdjunction φ).homEquiv _ _
      ((AffineModuleTilde.pullbackTildeIso φ).hom.app M) m) = _
  rw [AffineModuleTilde.pullbackTildeIso_hom_transpose_apply,
    AffineModuleTilde.map_app_toOpen, extendHom_one_tmul]

end KltDP.Geometry.AffineModuleTildeSemilinearMap

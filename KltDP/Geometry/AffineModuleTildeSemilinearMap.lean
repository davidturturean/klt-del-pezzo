import KltDP.Geometry.AffineModuleTildePullback

/-!
# Original affine pullback maps induced by semilinear module maps

The pinned semilinear-map equivalence and extension/restriction adjunction
already produce the scalar-extension map. The original affine tilde
pullback comparison transports precisely that map to module sheaves.
Naturality follows from those same adjunctions and the original tilde functor.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

namespace KltDP.Geometry.AffineModuleTildeSemilinearMap

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)

/-- The existing scalar-extension adjunction applied to an original semilinear map. -/
def extendHom {M : ModuleCat.{u} A} {N : ModuleCat.{u} B} (a : M →ₛₗ[φ] N) :
    (ModuleCat.extendScalars φ).obj M ⟶ N :=
  ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv M N).symm
    (ModuleCat.semilinearMapAddEquiv φ M N a)

/-- The original extension map retains the original semilinear image on unit tensors. -/
theorem extendHom_one_tmul {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (a : M →ₛₗ[φ] N) (m : M) :
    extendHom φ a ((1 : B) ⊗ₜ[A,φ] m) = a m := by
  have h := ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv M N).apply_symm_apply
    (ModuleCat.semilinearMapAddEquiv φ M N a)
  exact congrArg (fun z : M ⟶ (ModuleCat.restrictScalars φ).obj N => z m) h

/-- The original affine tilde pullback map associated to an original semilinear map. -/
def pullbackMap {M : ModuleCat.{u} A} {N : ModuleCat.{u} B} (a : M →ₛₗ[φ] N) :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).obj M.tilde ⟶ N.tilde :=
  (AffineModuleTilde.pullbackIso φ M).hom ≫ AffineModuleTilde.map (extendHom φ a)

/-- A commuting square of original module maps extends by the existing scalar adjunction. -/
theorem extendHom_square {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (s : M ⟶ M') (t : N ⟶ N') (a : M →ₛₗ[φ] N) (b : M' →ₛₗ[φ] N')
    (h : ∀ m : M, b (s m) = t (a m)) :
    (ModuleCat.extendScalars φ).map s ≫ extendHom φ b = extendHom φ a ≫ t := by
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [extendHom, Equiv.apply_symm_apply]
  apply ModuleCat.hom_ext
  exact LinearMap.ext h

/-- The original affine pullback comparisons transport the same module square to sheaves. -/
theorem pullbackMap_square {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (s : M ⟶ M') (t : N ⟶ N') (a : M →ₛₗ[φ] N) (b : M' →ₛₗ[φ] N')
    (h : ∀ m : M, b (s m) = t (a m)) :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).map
        (AffineModuleTilde.map s) ≫ pullbackMap φ b =
      pullbackMap φ a ≫ AffineModuleTilde.map t := by
  unfold pullbackMap
  calc
    _ = (AffineModuleTilde.pullbackIso φ M).hom ≫
        AffineModuleTilde.map ((ModuleCat.extendScalars φ).map s) ≫
        AffineModuleTilde.map (extendHom φ b) := by
      have hh := congrArg (fun z => z ≫ AffineModuleTilde.map (extendHom φ b))
        ((AffineModuleTilde.pullbackTildeIso φ).hom.naturality s)
      simpa only [Functor.comp_map, Category.assoc] using hh
    _ = _ := by
      rw [← AffineModuleTilde.map_comp, extendHom_square φ s t a b h,
        AffineModuleTilde.map_comp]
      simp only [Category.assoc]

end KltDP.Geometry.AffineModuleTildeSemilinearMap

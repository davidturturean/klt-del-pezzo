import KltDP.Geometry.AffineModuleTildeSemilinearSections
import KltDP.Compatibility.ExteriorPowerBaseChange

/-!
# Small normalizations for the original affine tilde pullback adjunction

The original affine adjunction and its naturality evaluate both a native
module map and a pulled-back sheaf map on their original canonical sections.
The exterior scalar-extension formula is retained before specializing any
Rees ring or differential module.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct ChangeOfRings

universe u

namespace KltDP.Geometry.AffineModuleTildeTransposeNormalization

open AffineModuleTildeSemilinearMap

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The original exterior base-change map followed by an original linear map. -/
theorem exteriorBaseChange_map_ιMulti
    {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    (n : ℕ) (f : B ⊗[A] M →ₗ[B] N) (v : Fin n → M) :
    exteriorPower.map n f
        (KltDP.Compatibility.ExteriorPowerBaseChange.map A B n M
          (1 ⊗ₜ[A] exteriorPower.ιMulti A n v)) =
      exteriorPower.ιMulti B n (fun i => f (1 ⊗ₜ[A] v i)) :=
  (congrArg (exteriorPower.map n f)
    (KltDP.Compatibility.ExteriorPowerBaseChange.map_one_tmul_ιMulti A B n M v)).trans
      (exteriorPower.map_apply_ιMulti f (fun i => (1 : B) ⊗ₜ[A] v i))

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)

/-- The original native module map has its original canonical-section transpose. -/
theorem native_transpose (M : ModuleCat.{u} A) (P : ModuleCat.{u} B)
    (N : (Spec (CommRingCat.of B)).Modules)
    (d : (ModuleCat.extendScalars φ).obj M ⟶ P) (a : P.tilde ⟶ N) (m : M) :
    (AffineModuleTilde.pulledTildeAdjunction φ).homEquiv M N
        (((AffineModuleTilde.pullbackIso φ M).hom ≫ AffineModuleTilde.map d) ≫ a) m =
      a.val.app (op ⊤) (ModuleCat.Tilde.toOpen P ⊤ (d ((1 : B) ⊗ₜ[A,φ] m))) := by
  rw [Adjunction.homEquiv_naturality_right]
  change a.val.app (op ⊤)
    ((AffineModuleTilde.pulledTildeAdjunction φ).homEquiv M P.tilde
      ((AffineModuleTilde.pullbackIso φ M).hom ≫ AffineModuleTilde.map d) m) = _
  rw [Adjunction.homEquiv_naturality_right]
  change a.val.app (op ⊤) ((AffineModuleTilde.map d).val.app (op ⊤)
    ((AffineModuleTilde.pulledTildeAdjunction φ).homEquiv M _
      ((AffineModuleTilde.pullbackTildeIso φ).hom.app M) m)) = _
  rw [AffineModuleTilde.pullbackTildeIso_hom_transpose_apply,
    AffineModuleTilde.map_app_toOpen]

/-- Combine a proved native image and a proved canonical-section image abstractly. -/
theorem native_transpose_eq (M : ModuleCat.{u} A) (P : ModuleCat.{u} B)
    (N : (Spec (CommRingCat.of B)).Modules)
    (d : (ModuleCat.extendScalars φ).obj M ⟶ P) (a : P.tilde ⟶ N)
    (m : M) (p : P) (z : N.val.obj (op ⊤))
    (hd : d ((1 : B) ⊗ₜ[A,φ] m) = p)
    (ha : a.val.app (op ⊤) (ModuleCat.Tilde.toOpen P ⊤ p) = z) :
    (AffineModuleTilde.pulledTildeAdjunction φ).homEquiv M N
        (((AffineModuleTilde.pullbackIso φ M).hom ≫ AffineModuleTilde.map d) ≫ a) m = z := by
  rw [native_transpose, hd]
  exact ha

/-- Naturality in the original affine source, evaluated before specialization. -/
theorem pullback_transpose (M : ModuleCat.{u} A)
    (P : (Spec (CommRingCat.of A)).Modules) (N : (Spec (CommRingCat.of B)).Modules)
    (a : M.tilde ⟶ P)
    (t : (schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).obj P ⟶ N) (m : M) :
    (AffineModuleTilde.pulledTildeAdjunction φ).homEquiv M N
        ((schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).map a ≫ t) m =
      t.val.app (op ⊤)
        (((schemeModulePullbackPushforwardAdjunction
          (Spec.map (CommRingCat.ofHom φ))).unit.app P).val.app (op ⊤)
            (a.val.app (op ⊤) (ModuleCat.Tilde.toOpen M ⊤ m))) := by
  rw [pulledTilde_homEquiv_apply, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_unit]
  rfl

/-- Combine proved canonical-section and original-unit images abstractly. -/
theorem pullback_transpose_eq (M : ModuleCat.{u} A)
    (P : (Spec (CommRingCat.of A)).Modules) (N : (Spec (CommRingCat.of B)).Modules)
    (a : M.tilde ⟶ P)
    (t : (schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).obj P ⟶ N)
    (m : M) (p : P.val.obj (op ⊤)) (z : N.val.obj (op ⊤))
    (ha : a.val.app (op ⊤) (ModuleCat.Tilde.toOpen M ⊤ m) = p)
    (ht : t.val.app (op ⊤)
      (((schemeModulePullbackPushforwardAdjunction
        (Spec.map (CommRingCat.ofHom φ))).unit.app P).val.app (op ⊤) p) = z) :
    (AffineModuleTilde.pulledTildeAdjunction φ).homEquiv M N
        ((schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).map a ≫ t) m = z := by
  rw [pullback_transpose, ha]
  exact ht

end KltDP.Geometry.AffineModuleTildeTransposeNormalization

import KltDP.Geometry.AffineProductKaehlerProjectionMaps

/-!
# The original pulled affine factors are the original tensor extensions

The scalar-extension functor uses restriction along a ring homomorphism.
Its scalar action is identified explicitly with the supplied algebra action;
the resulting equivalence preserves every original pure tensor. This gives
factor isomorphisms for the original Spec projections, without changing
the already constructed differential inclusion maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct ChangeOfRings

universe u

namespace KltDP.Geometry.AffineProductKaehler

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section ScalarExtension

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- Identity on the original ring carrier, with its scalar actions proved equal. -/
def restrictionScalarEquiv :
    (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) ≃ₗ[A] B where
  toFun b := b
  invFun b := b
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a b := by
    change algebraMap A B a * (show B from b) = a • (show B from b)
    exact (Algebra.smul_def a (show B from b)).symm

/-- Scalar extension along the original algebra map is the original tensor module. -/
def extensionEquiv (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (algebraMap A B)).obj M ≃ₗ[B] B ⊗[A] M := by
  let e : ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B))
      ⊗[A] M ≃ₗ[A] B ⊗[A] M :=
    TensorProduct.congr (restrictionScalarEquiv A B) (LinearEquiv.refl A M)
  refine { __ := e.toAddEquiv, map_smul' := ?_ }
  intro b
  change ∀ x : ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B))
      ⊗[A] M, e (b • x) = b • e x
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul b' m => rfl

@[simp]
theorem extensionEquiv_tmul (M : ModuleCat.{u} A) (b : B) (m : M) :
    extensionEquiv A B M (b ⊗ₜ[A,algebraMap A B] m) = b ⊗ₜ[A] m := by
  change TensorProduct.congr (restrictionScalarEquiv A B) (LinearEquiv.refl A M)
    (b ⊗ₜ[A,algebraMap A B] m) = _
  rfl

/-- The actual affine pullback, identified with the supplied original tensor module. -/
def pullbackFactorIso (M : ModuleCat.{u} A) :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj M.tilde ≅
      (ModuleCat.of B (B ⊗[A] M)).tilde :=
  AffineModuleTilde.pullbackIso (algebraMap A B) M ≪≫
    AffineModuleTilde.linearEquivIso
      (M := (ModuleCat.extendScalars (algebraMap A B)).obj M)
      (N := ModuleCat.of B (B ⊗[A] M)) (extensionEquiv A B M)

/-- Its original affine transpose is exactly the canonical unit-tensor section. -/
theorem pullbackFactorIso_transpose_apply (M : ModuleCat.{u} A) (m : M) :
    (AffineModuleTilde.pulledTildeAdjunction (algebraMap A B)).homEquiv M
        (ModuleCat.of B (B ⊗[A] M)).tilde (pullbackFactorIso A B M).hom m =
      ModuleCat.Tilde.toOpen (ModuleCat.of B (B ⊗[A] M)) ⊤ (1 ⊗ₜ[A] m) := by
  rw [pullbackFactorIso, Iso.trans_hom, Adjunction.homEquiv_naturality_right]
  change (AffineModuleTilde.map (extensionEquiv A B M).toModuleIso.hom).val.app (op ⊤)
    ((AffineModuleTilde.pulledTildeAdjunction (algebraMap A B)).homEquiv _ _
      ((AffineModuleTilde.pullbackTildeIso (algebraMap A B)).hom.app M) m) = _
  rw [AffineModuleTilde.pullbackTildeIso_hom_transpose_apply,
    AffineModuleTilde.map_app_toOpen]
  exact congrArg (ModuleCat.Tilde.toOpen (ModuleCat.of B (B ⊗[A] M)) ⊤)
    (extensionEquiv_tmul A B M 1 m)

end ScalarExtension

section Factors

open AffineKaehlerTildeDerivation AffineModuleTildeSemilinearMap

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The first actual pulled-back differential factor. -/
def leftFactorIso :
    (schemeModulePullback (firstProjection R S T)).obj
        (SchemeKaehlerSheaf.baseRingSheaf
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))) ≅
      (leftModule R S T).tilde :=
  (schemeModulePullback (firstProjection R S T)).mapIso
      (AffineKaehlerTildeLocalization.iso R S) ≪≫
    pullbackFactorIso S (S ⊗[R] T) (differentialModule R S)

/-- The second actual pulled-back differential factor. -/
def rightFactorIso :
    (schemeModulePullback (secondProjection R S T)).obj
        (SchemeKaehlerSheaf.baseRingSheaf
          (Spec.map (CommRingCat.ofHom (algebraMap R T)))) ≅
      (rightModule R S T).tilde :=
  (schemeModulePullback (secondProjection R S T)).mapIso
      (AffineKaehlerTildeLocalization.iso R T) ≪≫
    pullbackFactorIso T (S ⊗[R] T) (differentialModule R T)

end Factors

end KltDP.Geometry.AffineProductKaehler

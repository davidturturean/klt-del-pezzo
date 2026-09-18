import KltDP.Geometry.AffineProductKaehlerPullbackFactors
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# The actual summed pullback isomorphism on an affine product

The existing tilde functor is a left adjoint, so the existing categorical
biproduct comparison applies. Both inclusions in the resulting isomorphism
are proved to be the original projection differential maps, rather than
chosen unnormalized summand maps. This remains an affine result; gluing
across product charts is a separate compatibility proof.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace KltDP.Geometry.AffineProductKaehler

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section BinarySum

variable (B : Type u) [CommRing B] (M N : ModuleCat.{u} B)

local instance : PreservesBinaryBiproduct M N (AffineModuleTilde.functor B) :=
  preservesBinaryBiproduct_of_preservesBinaryCoproduct (AffineModuleTilde.functor B)

/-- The existing categorical module biproduct keeps its original first inclusion. -/
theorem module_inl_biprodIsoProd_hom :
    (biprod.inl : M ⟶ M ⊞ N) ≫ (ModuleCat.biprodIsoProd M N).hom =
      ModuleCat.ofHom (LinearMap.inl B M N) := by
  apply (cancel_mono (ModuleCat.biprodIsoProd M N).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply biprod.hom_ext <;>
    simp only [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst,
      ModuleCat.biprodIsoProd_inv_comp_snd, biprod.inl_fst, biprod.inl_snd] <;> rfl

/-- The existing categorical module biproduct keeps its original second inclusion. -/
theorem module_inr_biprodIsoProd_hom :
    (biprod.inr : N ⟶ M ⊞ N) ≫ (ModuleCat.biprodIsoProd M N).hom =
      ModuleCat.ofHom (LinearMap.inr B M N) := by
  apply (cancel_mono (ModuleCat.biprodIsoProd M N).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply biprod.hom_ext <;>
    simp only [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst,
      ModuleCat.biprodIsoProd_inv_comp_snd, biprod.inr_fst, biprod.inr_snd] <;> rfl

/-- Tilde of the original binary product is the actual sheaf-module biproduct. -/
def tildeProdIso :
    (ModuleCat.of B (M × N)).tilde ≅ M.tilde ⊞ N.tilde :=
  AffineModuleTilde.mapIso (ModuleCat.biprodIsoProd M N).symm ≪≫
    (AffineModuleTilde.functor B).mapBiprod M N

@[reassoc]
theorem inl_tildeProdIso_inv :
    (biprod.inl : M.tilde ⟶ M.tilde ⊞ N.tilde) ≫ (tildeProdIso B M N).inv =
      AffineModuleTilde.map (ModuleCat.ofHom (LinearMap.inl B M N)) := by
  change biprod.inl ≫ ((AffineModuleTilde.functor B).mapBiprod M N).inv ≫
    (AffineModuleTilde.functor B).map (ModuleCat.biprodIsoProd M N).hom = _
  rw [← Category.assoc, Functor.mapBiprod_inv, biprod.inl_desc,
    ← Functor.map_comp, module_inl_biprodIsoProd_hom] <;> rfl

@[reassoc]
theorem inr_tildeProdIso_inv :
    (biprod.inr : N.tilde ⟶ M.tilde ⊞ N.tilde) ≫ (tildeProdIso B M N).inv =
      AffineModuleTilde.map (ModuleCat.ofHom (LinearMap.inr B M N)) := by
  change biprod.inr ≫ ((AffineModuleTilde.functor B).mapBiprod M N).inv ≫
    (AffineModuleTilde.functor B).map (ModuleCat.biprodIsoProd M N).hom = _
  rw [← Category.assoc, Functor.mapBiprod_inv, biprod.inr_desc,
    ← Functor.map_comp, module_inr_biprodIsoProd_hom] <;> rfl

end BinarySum

section Normalization

open AffineModuleTildeSemilinearMap

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The factor comparison followed by a tilde map is the original semilinear
pullback map whenever their original unit tensors agree. -/
theorem pullbackFactorIso_hom_map_eq (M : ModuleCat.{u} A) (N : ModuleCat.{u} B)
    (g : ModuleCat.of B (B ⊗[A] M) ⟶ N)
    (a : M →ₛₗ[algebraMap A B] N) (h : ∀ m : M, g (1 ⊗ₜ[A] m) = a m) :
    (pullbackFactorIso A B M).hom ≫ AffineModuleTilde.map g =
      pullbackMap (algebraMap A B) a := by
  apply ((AffineModuleTilde.pulledTildeAdjunction (algebraMap A B)).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rw [Adjunction.homEquiv_naturality_right]
  change (AffineModuleTilde.map g).val.app (op ⊤)
    ((AffineModuleTilde.pulledTildeAdjunction (algebraMap A B)).homEquiv _ _
      (pullbackFactorIso A B M).hom m) = _
  rw [pullbackFactorIso_transpose_apply, AffineModuleTilde.map_app_toOpen,
    pullbackMap_transpose_apply, h]

end Normalization

private theorem factorIso_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} {Z W : D} (e : X ≅ Y) (f : F.obj Y ≅ Z)
    (g : Z ⟶ W) (a : F.obj Y ⟶ W) (h : f.hom ≫ g = a) :
    (F.mapIso e ≪≫ f).hom ≫ g = F.map e.hom ≫ a := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, h]

section Product

open AffineKaehlerTildeDerivation

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Expose only the original first factor's forward composition. -/
private theorem leftFactorIso_hom_eq :
    (leftFactorIso R S T).hom =
      (schemeModulePullback (firstProjection R S T)).map
        (AffineKaehlerTildeLocalization.iso R S).hom ≫
          (pullbackFactorIso S (S ⊗[R] T) (differentialModule R S)).hom := by
  rw [leftFactorIso, Iso.trans_hom, Functor.mapIso_hom]

theorem leftFactorIso_hom_inl :
    (leftFactorIso R S T).hom ≫
        AffineModuleTilde.map (ModuleCat.ofHom
          (LinearMap.inl (S ⊗[R] T) (leftModule R S T) (rightModule R S T))) =
      leftComparison R S T := by
  have h := pullbackFactorIso_hom_map_eq S (S ⊗[R] T)
    (differentialModule R S) (splitModule R S T)
    (ModuleCat.ofHom (LinearMap.inl (S ⊗[R] T) (leftModule R S T) (rightModule R S T)))
    (leftUnitSemilinear R S T) (fun _ => rfl)
  rw [leftFactorIso_hom_eq, leftComparison, Category.assoc]
  exact congrArg (fun z => (schemeModulePullback (firstProjection R S T)).map
    (AffineKaehlerTildeLocalization.iso R S).hom ≫ z) h

theorem rightFactorIso_hom_inr :
    (rightFactorIso R S T).hom ≫
        AffineModuleTilde.map (ModuleCat.ofHom
          (LinearMap.inr (S ⊗[R] T) (leftModule R S T) (rightModule R S T))) =
      rightComparison R S T := by
  have h := pullbackFactorIso_hom_map_eq T (S ⊗[R] T)
    (differentialModule R T) (splitModule R S T)
    (ModuleCat.ofHom (LinearMap.inr (S ⊗[R] T) (leftModule R S T) (rightModule R S T)))
    (rightUnitSemilinear R S T) (fun _ => rfl)
  exact factorIso_comp
    (schemeModulePullback (secondProjection R S T))
    (AffineKaehlerTildeLocalization.iso R T)
    (pullbackFactorIso T (S ⊗[R] T) (differentialModule R T))
    (AffineModuleTilde.map (ModuleCat.ofHom
      (LinearMap.inr (S ⊗[R] T) (leftModule R S T) (rightModule R S T))))
    (rightTildeInclusion R S T) h

/-- The actual absolute differential sheaf is the binary sum of the two
actual projection pullbacks. -/
def pulledSumIso :
    SchemeKaehlerSheaf.baseRingSheaf
        (Spec.map (CommRingCat.ofHom (algebraMap R (S ⊗[R] T)))) ≅
      (schemeModulePullback (firstProjection R S T)).obj
          (SchemeKaehlerSheaf.baseRingSheaf
            (Spec.map (CommRingCat.ofHom (algebraMap R S)))) ⊞
        (schemeModulePullback (secondProjection R S T)).obj
          (SchemeKaehlerSheaf.baseRingSheaf
            (Spec.map (CommRingCat.ofHom (algebraMap R T)))) :=
  iso R S T ≪≫ tildeProdIso (S ⊗[R] T) (leftModule R S T) (rightModule R S T) ≪≫
    biprod.mapIso (leftFactorIso R S T).symm (rightFactorIso R S T).symm

/-- The first inclusion is exactly the already constructed original differential map. -/
theorem inl_pulledSumIso_inv :
    biprod.inl ≫ (pulledSumIso R S T).inv = leftDifferentialMap R S T := by
  simp only [pulledSumIso, Iso.trans_inv, Category.assoc]
  change biprod.inl ≫ biprod.map (leftFactorIso R S T).hom (rightFactorIso R S T).hom ≫
    (tildeProdIso (S ⊗[R] T) (leftModule R S T) (rightModule R S T)).inv ≫
      (iso R S T).inv = _
  rw [biprod.inl_map_assoc, inl_tildeProdIso_inv_assoc, ← Category.assoc,
    leftFactorIso_hom_inl] <;> rfl

/-- The second inclusion is exactly the already constructed original differential map. -/
theorem inr_pulledSumIso_inv :
    biprod.inr ≫ (pulledSumIso R S T).inv = rightDifferentialMap R S T := by
  simp only [pulledSumIso, Iso.trans_inv, Category.assoc]
  change biprod.inr ≫ biprod.map (leftFactorIso R S T).hom (rightFactorIso R S T).hom ≫
    (tildeProdIso (S ⊗[R] T) (leftModule R S T) (rightModule R S T)).inv ≫
      (iso R S T).inv = _
  rw [biprod.inr_map_assoc, inr_tildeProdIso_inv_assoc, ← Category.assoc,
    rightFactorIso_hom_inr] <;> rfl

end Product

end KltDP.Geometry.AffineProductKaehler

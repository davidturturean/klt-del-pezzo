/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.AffineSymmetricAlgebraSheaf

/-!
# Actual ring-sheaf maps in the affine symmetric universal property

The map of sheaves of rings is constructed from the original map Spec B →
Spec A and its original structure-sheaf maps. Its equation with the base-ring
sheaf is proved from the original algebra-map equation. Its underlying module
map is then identified with the independently constructed tilde map, using the
original canonical sections. Consequently the extension maps in the affine
symmetric universal property are actual maps of the original algebra sheaves.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineSymmetricAlgebraSheaf

open AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- The original spectrum morphism attached to the original algebra map. -/
def algebraSpecMap (φ : A →ₐ[R] B) : Spec (.of B) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom φ.toRingHom)

/-- Its structure-map equation follows from the given algebra-map equation. -/
theorem algebraSpecMap_structure (φ : A →ₐ[R] B) :
    algebraSpecMap φ ≫ RationalTreePicard.componentAffineMap R A =
      RationalTreePicard.componentAffineMap R B := by
  rw [algebraSpecMap, RationalTreePicard.componentAffineMap,
    RationalTreePicard.componentAffineMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext φ.commutes

/-- The actual inverse image on every original base open. -/
theorem algebraSpecMap_preimage (φ : A →ₐ[R] B) (U : (Spec (.of R)).Opens) :
    algebraSpecMap φ ⁻¹ᵁ (RationalTreePicard.componentAffineMap R A ⁻¹ᵁ U) =
      RationalTreePicard.componentAffineMap R B ⁻¹ᵁ U := by
  rw [← Scheme.preimage_comp, algebraSpecMap_structure]

/-- The actual map of ring sheaves uses the existing scheme section maps. -/
def algebraSheafMap (φ : A →ₐ[R] B) : algebraSheaf R A ⟶ algebraSheaf R B where
  val :=
    { app U := (algebraSpecMap φ).appLE
        (RationalTreePicard.componentAffineMap R A ⁻¹ᵁ U.unop)
        (RationalTreePicard.componentAffineMap R B ⁻¹ᵁ U.unop)
        (algebraSpecMap_preimage φ U.unop).symm.le
      naturality {U V} i := by
        change (Spec (.of A)).presheaf.map _ ≫ (algebraSpecMap φ).appLE _ _ _ =
          (algebraSpecMap φ).appLE _ _ _ ≫ (Spec (.of B)).presheaf.map _
        rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map] }

private theorem appLE_of_morphism_eq {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (hfg : f = g) (U : Y.Opens) (hU : g ⁻¹ᵁ U ≤ f ⁻¹ᵁ U) :
    f.appLE U (g ⁻¹ᵁ U) hU = g.app U := by
  subst g
  exact Scheme.Hom.appLE_eq_app f

/-- The ring-sheaf map respects the original base structure sheaf. -/
theorem algebraSheafStructure_comp_map (φ : A →ₐ[R] B) :
    algebraSheafStructure R A ≫ algebraSheafMap φ = algebraSheafStructure R B := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change (RationalTreePicard.componentAffineMap R A).app U.unop ≫
      (algebraSpecMap φ).appLE _ _ _ =
    (RationalTreePicard.componentAffineMap R B).app U.unop
  rw [Scheme.Hom.app_eq_appLE, Scheme.appLE_comp_appLE]
  exact appLE_of_morphism_eq (algebraSpecMap_structure φ) U.unop _

/-- The original coefficient function on every open maps to the coefficient
function of its actual image in B. -/
theorem algebraSheafMap_toOpen (φ : A →ₐ[R] B) (U : (Spec (.of R)).Opens) (a : A) :
    (algebraSheafMap φ).val.app (op U)
        (StructureSheaf.toOpen A (RationalTreePicard.componentAffineMap R A ⁻¹ᵁ U) a) =
      StructureSheaf.toOpen B (RationalTreePicard.componentAffineMap R B ⁻¹ᵁ U) (φ a) := by
  have h := ConcreteCategory.congr_hom
    (StructureSheaf.toOpen_comp_comap φ.toRingHom
      (RationalTreePicard.componentAffineMap R A ⁻¹ᵁ U)) a
  change (algebraSpecMap φ).app (RationalTreePicard.componentAffineMap R A ⁻¹ᵁ U)
      (StructureSheaf.toOpen A (RationalTreePicard.componentAffineMap R A ⁻¹ᵁ U) a) =
    StructureSheaf.toOpen B
      (algebraSpecMap φ ⁻¹ᵁ (RationalTreePicard.componentAffineMap R A ⁻¹ᵁ U)) (φ a) at h
  change (Spec (.of B)).presheaf.map _
      ((algebraSpecMap φ).app _ (StructureSheaf.toOpen A _ a)) = _
  rw [h]
  rfl

/-- Forgetting the actual ring-sheaf map yields an actual module-sheaf map. -/
def algebraSheafMapModule (φ : A →ₐ[R] B) :
    underlyingModule R A ⟶ underlyingModule R B where
  val :=
    { app U := (ModuleCat.homEquiv
        (M := (underlyingModule R A).val.obj U)
        (N := (underlyingModule R B).val.obj U)).symm
        { toFun := (algebraSheafMap φ).val.app U
          map_add' a b := map_add _ a b
          map_smul' r a := by
            have h := congrArg (fun f : (Spec (.of R)).sheaf ⟶ algebraSheaf R B =>
              f.val.app U r) (algebraSheafStructure_comp_map φ)
            change (algebraSheafMap φ).val.app U
                ((RationalTreePicard.componentAffineMap R A).app U.unop r) =
              (RationalTreePicard.componentAffineMap R B).app U.unop r at h
            change (algebraSheafMap φ).val.app U
                ((RationalTreePicard.componentAffineMap R A).app U.unop r *
                  (show Γ(Spec (.of A), RationalTreePicard.componentAffineMap R A ⁻¹ᵁ U.unop) from a)) =
              (RationalTreePicard.componentAffineMap R B).app U.unop r *
                (show Γ(Spec (.of B), RationalTreePicard.componentAffineMap R B ⁻¹ᵁ U.unop) from
                  (algebraSheafMap φ).val.app U a)
            rw [map_mul, h] }
      naturality {U V} i := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        exact ConcreteCategory.congr_hom ((algebraSheafMap φ).val.naturality i) a }

/-- The accepted affine comparison retains the original structure-sheaf
function of every module element on every open. -/
theorem tildeIso_toOpen (U : (Spec (.of R)).Opens) (a : A) :
    (tildeIso R A).hom.val.app (op U) (ModuleCat.Tilde.toOpen (ModuleCat.of R A) U a) =
      StructureSheaf.toOpen A (RationalTreePicard.componentAffineMap R A ⁻¹ᵁ U) a :=
  RationalTreePicard.componentUnitTildePushforwardIso_toOpen R A U a

/-- The independently constructed module map is precisely the underlying
module map of the original ring-sheaf morphism. -/
theorem algebraSheafMapModule_eq (φ : A →ₐ[R] B) :
    algebraSheafMapModule φ = algebraModuleMap φ := by
  apply (cancel_epi (tildeIso R A).hom).mp
  rw [tildeIso_hom_algebraModuleMap]
  apply tilde_hom_ext
  intro f a
  change (algebraSheafMap φ).val.app (op (PrimeSpectrum.basicOpen f))
      ((tildeIso R A).hom.val.app (op (PrimeSpectrum.basicOpen f))
        (ModuleCat.Tilde.toOpen (ModuleCat.of R A) (PrimeSpectrum.basicOpen f) a)) =
    (tildeIso R B).hom.val.app (op (PrimeSpectrum.basicOpen f))
      ((AffineModuleTilde.map (ModuleCat.ofHom φ.toLinearMap)).val.app
        (op (PrimeSpectrum.basicOpen f))
        (ModuleCat.Tilde.toOpen (ModuleCat.of R A) (PrimeSpectrum.basicOpen f) a))
  rw [tildeIso_toOpen, algebraSheafMap_toOpen, AffineModuleTilde.map_app_toOpen,
    tildeIso_toOpen]
  rfl

variable (E : (Spec (.of R)).Modules) [E.IsQuasicoherent]

/-- The extension in the affine symmetric universal property uses an actual
map of ring sheaves over the original structure sheaf. -/
theorem generator_comp_lift_ringMap (α : E ⟶ underlyingModule R A) :
    generator E ≫ algebraSheafMapModule (liftEquiv (R := R) (A := A) E α) = α := by
  rw [algebraSheafMapModule_eq]
  exact generator_comp_lift (R := R) (A := A) E α

/-- Uniqueness also holds for the actual underlying maps of these ring-sheaf
morphisms, not only for an abstract linear extension. -/
theorem existsUnique_lift_ringMap (α : E ⟶ underlyingModule R A) :
    ∃! φ : KltDP.SymmetricAlgebra R (sectionModule E ⊤) →ₐ[R] A,
      generator E ≫ algebraSheafMapModule φ = α := by
  simpa only [algebraSheafMapModule_eq] using existsUnique_lift (R := R) (A := A) E α

end KltDP.Geometry.AffineSymmetricAlgebraSheaf

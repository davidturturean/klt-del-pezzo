/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.AffineAlgebraSheafMap

/-!
# All morphisms of the actual affine algebra sheaves

An algebra-sheaf morphism here is an actual ring-sheaf morphism commuting with
the original base structure sheaf. Its original global sections recover a
unique ordinary algebra map. The converse uses the actual Spec map; equality
is proved on the original tilde generators. Thus the symmetric extension
property quantifies over every such algebra-sheaf morphism, rather than only
over a chosen collection of maps induced from module homomorphisms.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineSymmetricAlgebraSheaf

open AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- Actual ring-sheaf morphisms compatible with the original O-module action. -/
def Hom := {η : algebraSheaf R A ⟶ algebraSheaf R B //
  algebraSheafStructure R A ≫ η = algebraSheafStructure R B}

variable {R A B}

/-- Every original algebra map induces such a ring-sheaf morphism. -/
def ofAlgHom (φ : A →ₐ[R] B) : Hom R A B :=
  ⟨algebraSheafMap φ, algebraSheafStructure_comp_map φ⟩

/-- Forget only ring multiplication, retaining the original section functions. -/
def toModuleHom (η : Hom R A B) : underlyingModule R A ⟶ underlyingModule R B where
  val :=
    { app U := (ModuleCat.homEquiv
        (M := (underlyingModule R A).val.obj U)
        (N := (underlyingModule R B).val.obj U)).symm
        { toFun := η.val.val.app U
          map_add' a b := map_add _ a b
          map_smul' r a := by
            have h := congrArg (fun f : (Spec (.of R)).sheaf ⟶ algebraSheaf R B =>
              f.val.app U r) η.property
            change η.val.val.app U
                ((RationalTreePicard.componentAffineMap R A).app U.unop r) =
              (RationalTreePicard.componentAffineMap R B).app U.unop r at h
            change η.val.val.app U
                ((RationalTreePicard.componentAffineMap R A).app U.unop r *
                  (show Γ(Spec (.of A), RationalTreePicard.componentAffineMap R A ⁻¹ᵁ U.unop) from a)) =
              (RationalTreePicard.componentAffineMap R B).app U.unop r *
                (show Γ(Spec (.of B), RationalTreePicard.componentAffineMap R B ⁻¹ᵁ U.unop) from
                  η.val.val.app U a)
            rw [map_mul, h] }
      naturality {U V} i := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        exact ConcreteCategory.congr_hom (η.val.val.naturality i) a }

/-- For a map induced from an algebra homomorphism this is the already proved
underlying map of the actual ring-sheaf morphism. -/
theorem toModuleHom_ofAlgHom (φ : A →ₐ[R] B) :
    toModuleHom (ofAlgHom φ) = algebraSheafMapModule φ := rfl

/-- Original global functions pull back through the original algebra action. -/
theorem structure_top_apply (r : R) :
    (RationalTreePicard.componentAffineMap R A).appTop
        ((Scheme.ΓSpecIso (.of R)).inv r) =
      (Scheme.ΓSpecIso (.of A)).inv (algebraMap R A r) :=
  ConcreteCategory.congr_hom
    (StructureSheaf.toOpen_comp_comap (algebraMap R A) ⊤) r

/-- Recover the original ring map from original global sections. -/
def globalRingHom (η : Hom R A B) : A →+* B :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ η.val.val.app (op ⊤) ≫
    (Scheme.ΓSpecIso (.of B)).hom).hom

/-- The structure-sheaf equation gives the original base-algebra equation. -/
def globalAlgHom (η : Hom R A B) : A →ₐ[R] B where
  __ := globalRingHom η
  commutes' r := by
    have h := congrArg (fun f : (Spec (.of R)).sheaf ⟶ algebraSheaf R B =>
      f.val.app (op ⊤) ((Scheme.ΓSpecIso (.of R)).inv r)) η.property
    change η.val.val.app (op ⊤)
        ((RationalTreePicard.componentAffineMap R A).appTop ((Scheme.ΓSpecIso (.of R)).inv r)) =
      (RationalTreePicard.componentAffineMap R B).appTop ((Scheme.ΓSpecIso (.of R)).inv r) at h
    change (Scheme.ΓSpecIso (.of B)).hom
      (η.val.val.app (op ⊤) ((Scheme.ΓSpecIso (.of A)).inv (algebraMap R A r))) =
        algebraMap R B r
    rw [← structure_top_apply, h, structure_top_apply]
    exact (Scheme.ΓSpecIso (.of B)).inv_hom_id_apply _

/-- Naturality determines the image of each original canonical section by its
actual global image. -/
theorem hom_app_toOpen (η : Hom R A B) (U : (Spec (.of R)).Opens) (a : A) :
    η.val.val.app (op U)
        (StructureSheaf.toOpen A (RationalTreePicard.componentAffineMap R A ⁻¹ᵁ U) a) =
      (algebraSheaf R B).val.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (η.val.val.app (op ⊤) ((Scheme.ΓSpecIso (.of A)).inv a)) :=
  ConcreteCategory.congr_hom
    (η.val.val.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
    ((Scheme.ΓSpecIso (.of A)).inv a)

/-- All such ring-sheaf morphisms are determined by original global elements. -/
theorem hom_ext (η θ : Hom R A B)
    (h : ∀ a : A, η.val.val.app (op ⊤) ((Scheme.ΓSpecIso (.of A)).inv a) =
      θ.val.val.app (op ⊤) ((Scheme.ΓSpecIso (.of A)).inv a)) : η = θ := by
  have hm : toModuleHom η = toModuleHom θ := by
    apply (cancel_epi (tildeIso R A).hom).mp
    apply tilde_hom_ext
    intro f a
    change η.val.val.app (op (PrimeSpectrum.basicOpen f))
        ((tildeIso R A).hom.val.app (op (PrimeSpectrum.basicOpen f))
          (ModuleCat.Tilde.toOpen (ModuleCat.of R A) (PrimeSpectrum.basicOpen f) a)) =
      θ.val.val.app (op (PrimeSpectrum.basicOpen f))
        ((tildeIso R A).hom.val.app (op (PrimeSpectrum.basicOpen f))
          (ModuleCat.Tilde.toOpen (ModuleCat.of R A) (PrimeSpectrum.basicOpen f) a))
    rw [tildeIso_toOpen, hom_app_toOpen, hom_app_toOpen, h]
  apply Subtype.ext
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact congrArg (fun f : underlyingModule R A ⟶ underlyingModule R B => f.val.app U a) hm

theorem globalAlgHom_ofAlgHom (φ : A →ₐ[R] B) : globalAlgHom (ofAlgHom φ) = φ := by
  apply AlgHom.ext
  intro a
  change (Scheme.ΓSpecIso (.of B)).hom
    ((algebraSheafMap φ).val.app (op ⊤)
      (StructureSheaf.toOpen A (RationalTreePicard.componentAffineMap R A ⁻¹ᵁ ⊤) a)) = φ a
  rw [algebraSheafMap_toOpen]
  exact (Scheme.ΓSpecIso (.of B)).inv_hom_id_apply _

theorem ofAlgHom_globalAlgHom (η : Hom R A B) : ofAlgHom (globalAlgHom η) = η := by
  apply hom_ext
  intro a
  change (algebraSheafMap (globalAlgHom η)).val.app (op ⊤)
      (StructureSheaf.toOpen A (RationalTreePicard.componentAffineMap R A ⁻¹ᵁ ⊤) a) = _
  rw [algebraSheafMap_toOpen]
  change (Scheme.ΓSpecIso (.of B)).inv
    ((Scheme.ΓSpecIso (.of B)).hom
      (η.val.val.app (op ⊤) ((Scheme.ΓSpecIso (.of A)).inv a))) = _
  exact (Scheme.ΓSpecIso (.of B)).hom_inv_id_apply _

/-- Full faithfulness for actual affine algebra sheaves over the original base. -/
def algHomEquiv : (A →ₐ[R] B) ≃ Hom R A B where
  toFun := ofAlgHom
  invFun := globalAlgHom
  left_inv := globalAlgHom_ofAlgHom
  right_inv := ofAlgHom_globalAlgHom

variable (E : (Spec (.of R)).Modules) [E.IsQuasicoherent]

/-- The symmetric universal bijection now has every actual affine algebra-sheaf
morphism as its codomain. -/
def liftSheafEquiv :
    (E ⟶ underlyingModule R A) ≃
      Hom R (KltDP.SymmetricAlgebra R (sectionModule E ⊤)) A :=
  (liftEquiv (R := R) (A := A) E).trans algHomEquiv

/-- The actual symmetric generator extends uniquely through actual ring-sheaf
morphisms over O, with no choice of linear extensions supplied as a premise. -/
theorem existsUnique_sheaf_lift (α : E ⟶ underlyingModule R A) :
    ∃! η : Hom R (KltDP.SymmetricAlgebra R (sectionModule E ⊤)) A,
      generator E ≫ toModuleHom η = α := by
  refine ⟨ofAlgHom (liftEquiv (R := R) (A := A) E α), ?_, ?_⟩
  · change generator E ≫
      toModuleHom (ofAlgHom (liftEquiv (R := R) (A := A) E α)) = α
    rw [toModuleHom_ofAlgHom]
    exact generator_comp_lift_ringMap E α
  · intro η hη
    rw [← ofAlgHom_globalAlgHom η, toModuleHom_ofAlgHom,
      algebraSheafMapModule_eq] at hη
    have h := lift_unique (R := R) (A := A) E α (globalAlgHom η) hη
    rw [← ofAlgHom_globalAlgHom η, h]

end KltDP.Geometry.AffineSymmetricAlgebraSheaf

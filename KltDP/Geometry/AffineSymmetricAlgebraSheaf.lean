/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Compatibility.SymmetricAlgebra.Basic
import KltDP.Geometry.AffineModuleTildeAdjunction
import KltDP.Geometry.AffineQuasicoherentCounit
import KltDP.Geometry.RationalTreePicardClosedPushforward
import Mathlib.CategoryTheory.HomCongr

/-!
# The affine symmetric algebra and its original sheaf generators

For an R-algebra A the sheaf is the original pushforward of the structure
sheaf of Spec A along Spec A → Spec R. Its underlying module is the accepted
actual pushforward unit, and the proved affine comparison identifies it with
the original tilde of A. No algebra structure is transferred onto a replacement
section carrier.

For an original quasicoherent E, the actual affine counit and full faithfulness
identify maps E → A-tilde with linear maps Γ(E) → A. The symmetric universal
property then gives a unique algebra map extending every such original sheaf
map. The construction and uniqueness are proved here; neither finite type nor
a desired symmetric-sheaf comparison is a premise.

This is the affine universal-property adapter. A definition of general relative
Proj or an admission of the published regular-proper-surface theorem is not
part of this file.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineSymmetricAlgebraSheaf

open AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The actual sheaf of rings of the affine algebra, on the original base. -/
def algebraSheaf : TopCat.Sheaf CommRingCat (Spec (.of R)) :=
  (TopCat.Sheaf.pushforward CommRingCat
    (RationalTreePicard.componentAffineMap R A).base).obj (Spec (.of A)).sheaf

/-- The original structure-sheaf morphism gives its R-algebra structure. -/
def algebraSheafStructure : (Spec (.of R)).sheaf ⟶ algebraSheaf R A :=
  ⟨(RationalTreePicard.componentAffineMap R A).c⟩

/-- The actual underlying module sheaf, with the same sections and restrictions. -/
abbrev underlyingModule : (Spec (.of R)).Modules :=
  RationalTreePicard.componentUnitPushforward R A

/-- The existing affine reconstruction isomorphism, with its original maps. -/
def tildeIso : (ModuleCat.of R A).tilde ≅ underlyingModule R A :=
  RationalTreePicard.componentUnitTildePushforwardIso R A

/-- The ring-sheaf and module-sheaf section carriers are literally the same. -/
theorem section_carrier (U : (Spec (.of R)).Opens) :
    ((algebraSheaf R A).val.obj (op U) : Type u) =
      (underlyingModule R A).val.obj (op U) := rfl

variable {R A} {B : Type u} [CommRing B] [Algebra R B]

/-- An original algebra map acts on the original affine algebra modules. -/
def algebraModuleMap (φ : A →ₐ[R] B) : underlyingModule R A ⟶ underlyingModule R B :=
  (tildeIso R A).inv ≫
    AffineModuleTilde.map (ModuleCat.ofHom φ.toLinearMap) ≫ (tildeIso R B).hom

/-- The affine module comparison intertwines the original map on algebra elements. -/
theorem tildeIso_hom_algebraModuleMap (φ : A →ₐ[R] B) :
    (tildeIso R A).hom ≫ algebraModuleMap φ =
      AffineModuleTilde.map (ModuleCat.ofHom φ.toLinearMap) ≫ (tildeIso R B).hom := by
  simp only [algebraModuleMap, Iso.hom_inv_id_assoc]

/-- Canonical original sections are sent to the section of the actual algebra image. -/
theorem algebraModuleMap_toOpen (φ : A →ₐ[R] B) (U : (Spec (.of R)).Opens) (a : A) :
    (algebraModuleMap φ).val.app (op U)
        ((tildeIso R A).hom.val.app (op U) (ModuleCat.Tilde.toOpen (ModuleCat.of R A) U a)) =
      (tildeIso R B).hom.val.app (op U)
        (ModuleCat.Tilde.toOpen (ModuleCat.of R B) U (φ a)) := by
  have h := congrArg (fun f : (ModuleCat.of R A).tilde ⟶ underlyingModule R B =>
    f.val.app (op U) (ModuleCat.Tilde.toOpen (ModuleCat.of R A) U a))
      (tildeIso_hom_algebraModuleMap φ)
  exact h.trans (congrArg ((tildeIso R B).hom.val.app (op U))
    (AffineModuleTilde.map_app_toOpen (ModuleCat.ofHom φ.toLinearMap) U a))

variable (E : (Spec (.of R)).Modules) [E.IsQuasicoherent]

/-- The original affine counit, with its isomorphism property proved from QC. -/
def counitIso : (sectionModule E ⊤).tilde ≅ E := by
  letI : IsIso (counit E) := counit_isIso_of_isQuasicoherent E
  exact asIso (counit E)

variable (A)

/-- Original sheaf maps into an affine algebra correspond to original global
linear maps. The counit and target tilde comparison are proved, not supplied. -/
def linearHomEquiv :
    (E ⟶ underlyingModule R A) ≃ (sectionModule E ⊤ →ₗ[R] A) :=
  (Iso.homCongr (counitIso E).symm (tildeIso R A).symm).trans
    ((fullyFaithfulFunctor R).homEquiv.symm.trans ModuleCat.homEquiv)

/-- Its inverse uses exactly the original sheaf maps of the given linear map. -/
theorem linearHomEquiv_symm (f : sectionModule E ⊤ →ₗ[R] A) :
    (linearHomEquiv (R := R) (A := A) E).symm f =
      (counitIso E).inv ≫ AffineModuleTilde.map ((ModuleCat.homEquiv (M := sectionModule E ⊤) (N := ModuleCat.of R A)).symm f) ≫ (tildeIso R A).hom := rfl

variable {A}

/-- Postcomposing the actual sheaf extension agrees with composing the given
linear maps. This is proved before invoking the symmetric universal property. -/
theorem linearHomEquiv_symm_comp (f : sectionModule E ⊤ →ₗ[R] A) (φ : A →ₐ[R] B) :
    (linearHomEquiv (R := R) (A := A) E).symm f ≫ algebraModuleMap φ =
      (linearHomEquiv (R := R) (A := B) E).symm (φ.toLinearMap.comp f) := by
  rw [linearHomEquiv_symm, linearHomEquiv_symm]
  simp only [algebraModuleMap, Category.assoc, Iso.hom_inv_id_assoc]
  have hcomp :
      (ModuleCat.homEquiv (M := sectionModule E ⊤) (N := ModuleCat.of R B)).symm
        (φ.toLinearMap.comp f) =
      (ModuleCat.homEquiv (M := sectionModule E ⊤) (N := ModuleCat.of R A)).symm f ≫
        ModuleCat.ofHom φ.toLinearMap := rfl
  rw [hcomp, AffineModuleTilde.map_comp]
  simp only [Category.assoc]

/-- The original affine symmetric algebra module sheaf. -/
abbrev symmetricModule := underlyingModule R (KltDP.SymmetricAlgebra R (sectionModule E ⊤))

/-- Its actual sheaf generator, induced by the original quotient inclusion. -/
def generator : E ⟶ symmetricModule E :=
  (linearHomEquiv (R := R) (A := KltDP.SymmetricAlgebra R (sectionModule E ⊤)) E).symm
    (KltDP.SymmetricAlgebra.ι R (sectionModule E ⊤))

variable (A)

/-- The affine symmetric universal property on the original sheaf maps. -/
def liftEquiv :
    (E ⟶ underlyingModule R A) ≃
      (KltDP.SymmetricAlgebra R (sectionModule E ⊤) →ₐ[R] A) :=
  (linearHomEquiv (R := R) (A := A) E).trans KltDP.SymmetricAlgebra.lift

/-- The algebra extension actually extends the original sheaf map. -/
theorem generator_comp_lift (α : E ⟶ underlyingModule R A) :
    generator E ≫ algebraModuleMap (liftEquiv (R := R) (A := A) E α) = α := by
  rw [generator, linearHomEquiv_symm_comp]
  change (linearHomEquiv (R := R) (A := A) E).symm
    ((KltDP.SymmetricAlgebra.lift (linearHomEquiv (R := R) (A := A) E α)).toLinearMap.comp
      (KltDP.SymmetricAlgebra.ι R (sectionModule E ⊤))) = α
  have h : (KltDP.SymmetricAlgebra.lift (linearHomEquiv (R := R) (A := A) E α)).toLinearMap.comp
      (KltDP.SymmetricAlgebra.ι R (sectionModule E ⊤)) =
      linearHomEquiv (R := R) (A := A) E α := by
    apply LinearMap.ext
    intro m
    exact KltDP.SymmetricAlgebra.lift_ι_apply _ m
  rw [h]
  exact (linearHomEquiv (R := R) (A := A) E).symm_apply_apply α

/-- An algebra map extending the same original sheaf generator is unique. -/
theorem lift_unique (α : E ⟶ underlyingModule R A)
    (φ : KltDP.SymmetricAlgebra R (sectionModule E ⊤) →ₐ[R] A)
    (hφ : generator E ≫ algebraModuleMap φ = α) : φ = liftEquiv (R := R) (A := A) E α := by
  rw [generator, linearHomEquiv_symm_comp] at hφ
  have hlinear := congrArg (linearHomEquiv (R := R) (A := A) E) hφ
  rw [(linearHomEquiv (R := R) (A := A) E).apply_symm_apply] at hlinear
  apply KltDP.SymmetricAlgebra.algHom_ext
  change φ.toLinearMap.comp (KltDP.SymmetricAlgebra.ι R (sectionModule E ⊤)) =
    (KltDP.SymmetricAlgebra.lift (linearHomEquiv (R := R) (A := A) E α)).toLinearMap.comp
      (KltDP.SymmetricAlgebra.ι R (sectionModule E ⊤))
  calc
    _ = linearHomEquiv (R := R) (A := A) E α := hlinear
    _ = _ := by
      apply LinearMap.ext
      intro m
      exact (KltDP.SymmetricAlgebra.lift_ι_apply _ m).symm

/-- Existence and uniqueness, retaining the actual original module-sheaf map. -/
theorem existsUnique_lift (α : E ⟶ underlyingModule R A) :
    ∃! φ : KltDP.SymmetricAlgebra R (sectionModule E ⊤) →ₐ[R] A,
      generator E ≫ algebraModuleMap φ = α :=
  ⟨liftEquiv (R := R) (A := A) E α, generator_comp_lift (R := R) (A := A) E α, fun φ hφ => lift_unique (R := R) (A := A) E α φ hφ⟩

end KltDP.Geometry.AffineSymmetricAlgebraSheaf

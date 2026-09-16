import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Ring.Adjunctions
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Units of an actual sheaf of commutative rings

This adapter reuses the pinned Mathlib functor `CommMonCat.units`, the
right-adjoint instances for it and `forget₂ CommRingCat CommMonCat`, and
`CategoryTheory.sheafCompose`. Right adjoints preserve the limits required
by the sheaf condition. Thus sections are the actual units of the rings of
sections, with restriction and morphism maps given by `Units.map`.

No sheafification, Cartier quotient, or comparison with a divisor class
group is defined or assumed here.
-/

noncomputable section

open CategoryTheory

universe u v w

namespace KltDP.Sheaf

/-- The existing categorical units functor after forgetting addition. -/
def commRingUnitsFunctor : CommRingCat.{u} ⥤ CommGrp.{u} :=
  forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units

instance : commRingUnitsFunctor.{u}.IsRightAdjoint :=
  inferInstanceAs
    (forget₂ CommRingCat.{u} CommMonCat.{u} ⋙ CommMonCat.units).IsRightAdjoint

variable {C : Type w} [Category.{v} C] (J : GrothendieckTopology C)

/-- Taking units sectionwise is a functor on actual sheaves. -/
def unitsSheafFunctor : CategoryTheory.Sheaf J CommRingCat.{u} ⥤
    CategoryTheory.Sheaf J CommGrp.{u} :=
  sheafCompose J commRingUnitsFunctor

variable {J}

/-- The sheaf of units of a sheaf of commutative rings. -/
abbrev unitsSheaf (R : CategoryTheory.Sheaf J CommRingCat.{u}) :
    CategoryTheory.Sheaf J CommGrp.{u} :=
  (unitsSheafFunctor J).obj R

/-- A morphism of ring sheaves induces the actual map on their units. -/
abbrev unitsSheafMap {R S : CategoryTheory.Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    unitsSheaf R ⟶ unitsSheaf S :=
  (unitsSheafFunctor J).map φ

@[simp]
theorem unitsSheaf_obj (R : CategoryTheory.Sheaf J CommRingCat.{u}) (U : Cᵒᵖ) :
    (unitsSheaf R).val.obj U = CommGrp.of (R.val.obj U)ˣ := rfl

/-- The underlying type of sections is the group of units, definitionally. -/
theorem unitsSheaf_obj_coe (R : CategoryTheory.Sheaf J CommRingCat.{u}) (U : Cᵒᵖ) :
    ((unitsSheaf R).val.obj U : Type u) = (R.val.obj U)ˣ := rfl

@[simp]
theorem unitsSheaf_map (R : CategoryTheory.Sheaf J CommRingCat.{u})
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (unitsSheaf R).val.map f = CommGrp.ofHom (Units.map (R.val.map f).hom) := rfl

@[simp]
theorem unitsSheaf_map_apply (R : CategoryTheory.Sheaf J CommRingCat.{u})
    {U V : Cᵒᵖ} (f : U ⟶ V) (a : (R.val.obj U)ˣ) :
    (unitsSheaf R).val.map f a = Units.map (R.val.map f).hom a := rfl

@[simp]
theorem unitsSheafMap_app {R S : CategoryTheory.Sheaf J CommRingCat.{u}}
    (φ : R ⟶ S) (U : Cᵒᵖ) :
    (unitsSheafMap φ).val.app U = CommGrp.ofHom (Units.map (φ.val.app U).hom) := rfl

@[simp]
theorem unitsSheafMap_app_apply {R S : CategoryTheory.Sheaf J CommRingCat.{u}}
    (φ : R ⟶ S) (U : Cᵒᵖ) (a : (R.val.obj U)ˣ) :
    (unitsSheafMap φ).val.app U a = Units.map (φ.val.app U).hom a := rfl

end KltDP.Sheaf

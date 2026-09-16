import KltDP.Compatibility.SheafDualUnit
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.CategoryTheory.Endomorphism

/-!
# Actual unit-sheaf automorphisms and transition units

The existing evaluation-at-one equivalence and scalar endomorphism ring map
identify automorphisms of the rank-one unit sheaf on an over-site with units
of the original section ring. This also extracts the unique transition unit
between two actual trivializations of the same module sheaf.

No sheaf gluing, existence of chart trivializations, Picard comparison, or
geometric degree statement is assumed. All constructions use the existing
actual sheaves, section rings, scalar actions, and categorical isomorphisms.
-/

noncomputable section

open CategoryTheory Opposite

universe u

namespace KltDP.SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  [∀ U, IsMulCommutative (R.val.obj U)]

/-- Scalar multiplication is a ring equivalence onto the actual endomorphism ring. -/
def overUnitScalarEndRingEquiv (U : C) :
    R.val.obj (op U) ≃+* End (_root_.SheafOfModules.unit (R.over U)) :=
  RingEquiv.ofBijective (overUnitScalarEndRingHom R U)
    (dualUnitSectionsEquiv R U).symm.bijective

@[simp]
theorem overUnitScalarEndRingEquiv_apply (U : C) (r : R.val.obj (op U)) :
    overUnitScalarEndRingEquiv R U r = overUnitScalarEnd R U r := rfl

/-- Units of the original section ring are exactly actual unit-sheaf automorphisms. -/
def overUnitSectionUnitsEquivAut (U : C) :
    (R.val.obj (op U))ˣ ≃* Aut (_root_.SheafOfModules.unit (R.over U)) :=
  (Units.mapEquiv (overUnitScalarEndRingEquiv R U).toMulEquiv).trans
    (Aut.unitsEndEquivAut _)

@[simp]
theorem overUnitSectionUnitsEquivAut_hom (U : C) (r : (R.val.obj (op U))ˣ) :
    (overUnitSectionUnitsEquivAut R U r).hom =
      overUnitScalarEnd R U (r : R.val.obj (op U)) := rfl

@[simp]
theorem overUnitSectionUnitsEquivAut_inv (U : C) (r : (R.val.obj (op U))ˣ) :
    (overUnitSectionUnitsEquivAut R U r).inv =
      overUnitScalarEnd R U ((r⁻¹ : (R.val.obj (op U))ˣ) : R.val.obj (op U)) := rfl

/-- The automorphism multiplies by the actual restriction of the original unit. -/
@[simp]
theorem overUnitSectionUnitsEquivAut_hom_app_apply (U : C)
    (r : (R.val.obj (op U))ˣ) (V : (Over U)ᵒᵖ) (x : (R.over U).val.obj V) :
    (overUnitSectionUnitsEquivAut R U r).hom.val.app V x =
      x * (show (R.over U).val.obj V from
        R.val.map V.unop.hom.op (r : R.val.obj (op U))) := by
  rw [overUnitSectionUnitsEquivAut_hom, overUnitScalarEnd_app_apply]

/-- Every actual unit-sheaf automorphism has a unique original section unit. -/
theorem existsUnique_overUnitSectionUnit (U : C)
    (α : Aut (_root_.SheafOfModules.unit (R.over U))) :
    ∃! r : (R.val.obj (op U))ˣ, overUnitSectionUnitsEquivAut R U r = α := by
  obtain ⟨r, hr⟩ := (overUnitSectionUnitsEquivAut R U).surjective α
  refine ⟨r, hr, ?_⟩
  intro s hs
  exact (overUnitSectionUnitsEquivAut R U).injective (hs.trans hr.symm)

/-- Comparing two actual trivializations yields a unique transition unit. -/
theorem existsUnique_trivialization_transition_unit (U : C)
    (M : _root_.SheafOfModules (R.over U))
    (a b : M ≅ _root_.SheafOfModules.unit (R.over U)) :
    ∃! r : (R.val.obj (op U))ˣ,
      overUnitSectionUnitsEquivAut R U r = a.symm ≪≫ b :=
  existsUnique_overUnitSectionUnit R U (a.symm ≪≫ b)

/-- The transition automorphism is the original composite of sheaf maps. -/
theorem trivialization_transition_hom (U : C)
    (M : _root_.SheafOfModules (R.over U))
    (a b : M ≅ _root_.SheafOfModules.unit (R.over U))
    (r : (R.val.obj (op U))ˣ)
    (h : overUnitSectionUnitsEquivAut R U r = a.symm ≪≫ b) :
    overUnitScalarEnd R U (r : R.val.obj (op U)) = a.inv ≫ b.hom :=
  congrArg Iso.hom h

end KltDP.SheafOfModules

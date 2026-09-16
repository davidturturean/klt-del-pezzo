import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Etale.Basic

/-!
# The actual residue field at a closed point of a finite-type algebra

For a maximal ideal of a finite-type algebra over an algebraically closed
field, the canonical map from the base field to the residue field of the
prime localization is bijective. The proof uses the pinned canonical
quotient-to-residue-field map, Zariski's lemma, and algebraic closedness.

The resulting algebra equivalence retains that canonical map. Its inverse
constructs an actual base-field-valued character with exactly the given
maximal ideal as kernel. No chosen character or residue-field identification
is supplied as an additional hypothesis.
-/

noncomputable section

namespace KltDP.Compatibility

universe u

/-- The identity base extension has a unique lift, since base-algebra
homomorphisms from the base ring are unique. -/
private theorem formallyEtale_self (k : Type u) [CommRing k] :
    Algebra.FormallyEtale k k := by
  constructor
  intro B _ _ I _
  constructor
  · intro f g _
    exact Subsingleton.elim f g
  · intro f
    exact ⟨Algebra.ofId k B, Subsingleton.elim _ _⟩

/-- At a maximal ideal, the canonical map from the original ring to its
actual localized residue field is surjective. -/
theorem algebraMap_closedResidueField_surjective
    {A : Type u} [CommRing A] (q : Ideal A) [q.IsMaximal] :
    Function.Surjective (algebraMap A q.ResidueField) := by
  intro z
  obtain ⟨b, hb⟩ := (Ideal.bijective_algebraMap_quotient_residueField q).surjective z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨a, hb⟩

section FiniteType

variable (k : Type u) {A : Type u} [Field k] [CommRing A] [Algebra k A]
variable [Algebra.FiniteType k A] (q : Ideal A) [q.IsMaximal]

/-- The canonical base-field map to the actual closed-point residue field
is of finite type, by the surjection from the original finite-type algebra. -/
theorem closedResidueField_algebraMap_finiteType :
    (algebraMap k q.ResidueField).FiniteType := by
  rw [IsScalarTower.algebraMap_eq k A q.ResidueField]
  exact RingHom.FiniteType.comp_surjective
    (algebraMap_finiteType_iff_algebra_finiteType.mpr inferInstance)
    (algebraMap_closedResidueField_surjective q)

/-- Zariski's lemma makes the canonical closed-point residue extension finite. -/
theorem closedResidueField_algebraMap_finite :
    (algebraMap k q.ResidueField).Finite :=
  RingHom.finite_iff_finiteType_of_isJacobsonRing.mpr
    (closedResidueField_algebraMap_finiteType k q)

variable [IsAlgClosed k]

/-- The canonical map to the residue field of the actual prime localization
is bijective over an algebraically closed base field. -/
theorem closedResidueField_algebraMap_bijective :
    Function.Bijective
      (algebraMap k (IsLocalRing.ResidueField (Localization.AtPrime q))) :=
  IsAlgClosed.ringHom_bijective_of_isIntegral (algebraMap k q.ResidueField)
    (closedResidueField_algebraMap_finite k q).to_isIntegral

/-- The algebra equivalence whose forward map is the canonical base-field map. -/
def closedResidueFieldAlgEquiv : k ≃ₐ[k] q.ResidueField :=
  AlgEquiv.ofBijective (Algebra.ofId k q.ResidueField)
    (closedResidueField_algebraMap_bijective k q)

@[simp] theorem closedResidueFieldAlgEquiv_apply (a : k) :
    closedResidueFieldAlgEquiv k q a = algebraMap k q.ResidueField a := rfl

/-- The actual closed-point residue extension is formally étale. -/
theorem closedResidueField_formallyEtale :
    Algebra.FormallyEtale k (IsLocalRing.ResidueField (Localization.AtPrime q)) := by
  letI : Algebra.FormallyEtale k k := formallyEtale_self k
  exact Algebra.FormallyEtale.of_equiv (closedResidueFieldAlgEquiv k q)

/-- The actual character obtained from the canonical residue map and the
inverse of the proved canonical base-field equivalence. -/
def closedPointCharacter : A →ₐ[k] k :=
  (closedResidueFieldAlgEquiv k q).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom k A q.ResidueField)

/-- Applying the canonical base-field embedding to the character recovers
the original ring's canonical residue map. -/
theorem closedResidueFieldAlgEquiv_comp_closedPointCharacter :
    (closedResidueFieldAlgEquiv k q).toAlgHom.comp (closedPointCharacter k q) =
      IsScalarTower.toAlgHom k A q.ResidueField := by
  ext a
  exact (closedResidueFieldAlgEquiv k q).apply_symm_apply _

/-- The character vanishes exactly on the chosen maximal ideal. -/
theorem closedPointCharacter_eq_zero_iff (a : A) :
    closedPointCharacter k q a = 0 ↔ a ∈ q := by
  change (closedResidueFieldAlgEquiv k q).symm (algebraMap A q.ResidueField a) = 0 ↔ _
  constructor
  · intro h
    have hz : algebraMap A q.ResidueField a = 0 := by
      simpa only [AlgEquiv.apply_symm_apply, map_zero] using
        congrArg (closedResidueFieldAlgEquiv k q) h
    exact Ideal.algebraMap_residueField_eq_zero.mp hz
  · intro ha
    rw [Ideal.algebraMap_residueField_eq_zero.mpr ha, map_zero]

/-- The constructed character has precisely the given maximal ideal as
its kernel, rather than merely a point with the same residue field. -/
theorem closedPointCharacter_ker :
    RingHom.ker (closedPointCharacter k q).toRingHom = q := by
  ext a
  exact closedPointCharacter_eq_zero_iff k q a

end FiniteType

end KltDP.Compatibility

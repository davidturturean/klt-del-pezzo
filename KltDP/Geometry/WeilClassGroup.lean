import KltDP.Geometry.PrincipalDivisor
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The actual Weil divisor class group

The group is the existing additive-group quotient of the original surface
divisors by the range of the actual principal-divisor homomorphism. The
quotient construction, its group operations, and surjectivity are reused
from pinned Mathlib. No new quotient relation or quotient machinery is
implemented.

Linear equivalence has the explicit orientation `D - E = div(f)`, where
`f` is an actual unit of the original scheme function field. Class equality
and vanishing are proved equivalent to the corresponding actual principal
divisor witnesses. This group has no assumed identification with a scheme
Picard group, Cartier class group, or numerical divisor group.

Reused source: Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b,
`GroupTheory/QuotientGroup/Defs.lean` and
`Algebra/Group/Subgroup/Ker.lean` (Apache-2.0). The external reviewed
Weil-divisor source has the same difference orientation for linear
equivalence, but its class-group quotient is not used here.
See `docs/WEIL_CLASS_GROUP_FOUNDATION.md` for the remaining bridge.
-/

noncomputable section

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The actual subgroup of principal Weil divisors, as the image of the
proved principal-divisor homomorphism on nonzero rational functions. -/
def principalDivisors : AddSubgroup X.WeilDivisor := X.principalDivisorHom.range

/-- Membership in the image has an actual rational-function witness.
The equation is oriented from the divisor to its principal expression. -/
theorem mem_principalDivisors_iff (D : X.WeilDivisor) :
    D ∈ X.principalDivisors ↔
      ∃ f : X.toScheme.functionFieldˣ, D = X.principalDivisor f := by
  change D ∈ X.principalDivisorHom.range ↔ _
  rw [AddMonoidHom.mem_range]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f.toMul, hf.symm⟩
  · rintro ⟨f, hf⟩
    exact ⟨Additive.ofMul f, hf.symm⟩

/-- The actual Weil divisor class group, using Mathlib's quotient of an
additive group by a subgroup. Its additive commutative group is inherited. -/
abbrev WeilClassGroup := X.WeilDivisor ⧸ X.principalDivisors

/-- The canonical additive class map from actual divisors. -/
def weilClassMap : X.WeilDivisor →+ X.WeilClassGroup :=
  QuotientAddGroup.mk' X.principalDivisors

/-- Every class has an actual finitely supported divisor representative. -/
theorem weilClassMap_surjective : Function.Surjective X.weilClassMap :=
  QuotientAddGroup.mk'_surjective X.principalDivisors

theorem exists_weilClass_representative (c : X.WeilClassGroup) :
    ∃ D : X.WeilDivisor, X.weilClassMap D = c := X.weilClassMap_surjective c

/-- Exact class equality with the convention `D - E = div(f)`. The
witness belongs to the original surface's actual function-field unit group. -/
theorem weilClassMap_eq_iff (D E : X.WeilDivisor) :
    X.weilClassMap D = X.weilClassMap E ↔
      ∃ f : X.toScheme.functionFieldˣ, D - E = X.principalDivisor f := by
  change (D : X.WeilDivisor ⧸ X.principalDivisors) = E ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem, X.mem_principalDivisors_iff]

/-- An actual divisor represents zero precisely when it is the actual
principal divisor of a nonzero rational function. -/
theorem weilClassMap_eq_zero_iff (D : X.WeilDivisor) :
    X.weilClassMap D = 0 ↔
      ∃ f : X.toScheme.functionFieldˣ, D = X.principalDivisor f := by
  change (D : X.WeilDivisor ⧸ X.principalDivisors) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff, X.mem_principalDivisors_iff]

/-- Equivalently, equality of classes means that the first representative
is the second plus an actual principal divisor, in this explicit order. -/
theorem weilClassMap_eq_iff_exists_add_principal (D E : X.WeilDivisor) :
    X.weilClassMap D = X.weilClassMap E ↔
      ∃ f : X.toScheme.functionFieldˣ, D = E + X.principalDivisor f := by
  rw [X.weilClassMap_eq_iff]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, (sub_eq_iff_eq_add.mp hf).trans (add_comm _ _)⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, sub_eq_iff_eq_add.mpr (hf.trans (add_comm _ _))⟩

@[simp]
theorem weilClassMap_principalDivisor (f : X.toScheme.functionFieldˣ) :
    X.weilClassMap (X.principalDivisor f) = 0 :=
  (X.weilClassMap_eq_zero_iff _).mpr ⟨f, rfl⟩

/-- The kernel is exactly the already constructed image of principal
divisors. This is the existing quotient-kernel theorem. -/
theorem weilClassMap_ker : X.weilClassMap.ker = X.principalDivisors :=
  QuotientAddGroup.ker_mk' X.principalDivisors

/-- Linear equivalence of actual Weil divisors, with orientation
`D - E = div(f)` for an actual nonzero rational function. -/
def LinearlyEquivalent (D E : X.WeilDivisor) : Prop :=
  ∃ f : X.toScheme.functionFieldˣ, D - E = X.principalDivisor f

theorem linearlyEquivalent_iff_weilClassMap_eq (D E : X.WeilDivisor) :
    X.LinearlyEquivalent D E ↔ X.weilClassMap D = X.weilClassMap E :=
  (X.weilClassMap_eq_iff D E).symm

theorem linearlyEquivalent_refl (D : X.WeilDivisor) : X.LinearlyEquivalent D D :=
  (X.linearlyEquivalent_iff_weilClassMap_eq D D).mpr rfl

theorem linearlyEquivalent_symm {D E : X.WeilDivisor}
    (h : X.LinearlyEquivalent D E) : X.LinearlyEquivalent E D :=
  (X.linearlyEquivalent_iff_weilClassMap_eq E D).mpr
    ((X.linearlyEquivalent_iff_weilClassMap_eq D E).mp h).symm

theorem linearlyEquivalent_trans {D E F : X.WeilDivisor}
    (hDE : X.LinearlyEquivalent D E) (hEF : X.LinearlyEquivalent E F) :
    X.LinearlyEquivalent D F :=
  (X.linearlyEquivalent_iff_weilClassMap_eq D F).mpr
    (((X.linearlyEquivalent_iff_weilClassMap_eq D E).mp hDE).trans
      ((X.linearlyEquivalent_iff_weilClassMap_eq E F).mp hEF))

/-- Adding an actual principal divisor preserves the Weil class. -/
theorem weilClassMap_add_principalDivisor (D : X.WeilDivisor)
    (f : X.toScheme.functionFieldˣ) :
    X.weilClassMap (D + X.principalDivisor f) = X.weilClassMap D := by
  rw [map_add, X.weilClassMap_principalDivisor, add_zero]

end KltDP.Geometry.NormalProjectiveSurface

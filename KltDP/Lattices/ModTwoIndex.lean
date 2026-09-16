import KltDP.Codes.IntegralNodeCode
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Reduction modulo two and a finite subgroup index

For an actual finite-index subgroup `Γ` of an additive abelian group `M`,
this module constructs the reduced image of `Γ` in `M / (2 M)` and the
surjection from `M / Γ` onto the quotient by that image. Its order therefore
divides the actual index. Since that quotient is a finite binary vector
space, its order is two to its dimension, giving the bound

`finrank F₂ ((M / 2M) / image Γ) ≤ Γ.index.factorization 2`.

The exponent on the right is the manuscript's `v₂([M : Γ])`. Finiteness
of the index is an explicit property of the actual subgroup. Finiteness of
the binary quotient is proved from the constructed surjection before any
cardinality/dimension argument, so infinite types cannot acquire a spurious
bound through the zero convention for `Nat.card` or `Module.finrank`.

This group-theoretic statement needs neither freeness nor finite generation
of `M`, and therefore applies in particular to the finite free integral
Picard lattices used in `lem:picard-index` and `lem:picard-parity`. It does
not construct a surface's Picard group or assert that any node classes are
orthogonal to this reduced image; those are separate adapters.
-/

namespace KltDP.Lattices

open KltDP.Codes

variable {M : Type*} [AddCommGroup M]

/-- The actual image of a subgroup in the quotient modulo doubles, with its
binary submodule structure obtained from its additive subgroup structure. -/
def modTwoImage (Γ : AddSubgroup M) : Submodule (ZMod 2) (ModTwo M) :=
  AddSubgroup.toZModSubmodule 2 (Γ.map (modTwoMk M))

@[simp]
theorem mem_modTwoImage_iff (Γ : AddSubgroup M) (x : ModTwo M) :
    x ∈ modTwoImage Γ ↔ ∃ m ∈ Γ, modTwoMk M m = x := by
  rfl

/-- Reduction of a subgroup element belongs to its reduced image. -/
theorem modTwoMk_mem_modTwoImage (Γ : AddSubgroup M) {m : M} (hm : m ∈ Γ) :
    modTwoMk M m ∈ modTwoImage Γ :=
  ⟨m, hm, rfl⟩

/-- The composite of reduction modulo two with quotient by the reduced
subgroup. This is an actual additive homomorphism. -/
def modTwoProjection (Γ : AddSubgroup M) : M →+ ModTwo M ⧸ modTwoImage Γ :=
  (modTwoImage Γ).mkQ.toAddMonoidHom.comp (modTwoMk M)

theorem le_ker_modTwoProjection (Γ : AddSubgroup M) :
    Γ ≤ AddMonoidHom.ker (modTwoProjection Γ) := by
  intro m hm
  change (Submodule.Quotient.mk (modTwoMk M m) : ModTwo M ⧸ modTwoImage Γ) = 0
  exact (Submodule.Quotient.mk_eq_zero (modTwoImage Γ)).mpr
    (modTwoMk_mem_modTwoImage Γ hm)

/-- The projection factors through the actual finite-index quotient `M/Γ`. -/
def modTwoIndexMap (Γ : AddSubgroup M) :
    M ⧸ Γ →+ ModTwo M ⧸ modTwoImage Γ :=
  QuotientAddGroup.lift Γ (modTwoProjection Γ) (le_ker_modTwoProjection Γ)

@[simp]
theorem modTwoIndexMap_mk (Γ : AddSubgroup M) (m : M) :
    modTwoIndexMap Γ (QuotientAddGroup.mk m) =
      (modTwoImage Γ).mkQ (modTwoMk M m) := by
  rfl

/-- Every element of the binary quotient has a representative in the
finite-index quotient. -/
theorem modTwoIndexMap_surjective (Γ : AddSubgroup M) :
    Function.Surjective (modTwoIndexMap Γ) := by
  intro y
  obtain ⟨x, hx⟩ := (modTwoImage Γ).mkQ_surjective y
  obtain ⟨m, hm⟩ := QuotientAddGroup.mk'_surjective (twiceSubgroup M) x
  refine ⟨QuotientAddGroup.mk m, ?_⟩
  rw [modTwoIndexMap_mk]
  change (modTwoImage Γ).mkQ ((QuotientAddGroup.mk' (twiceSubgroup M)) m) = y
  rw [hm, hx]

/-- Finiteness is inherited from the actual finite-index quotient. -/
instance finite_modTwoImage_quotient (Γ : AddSubgroup M) [Γ.FiniteIndex] :
    Finite (ModTwo M ⧸ modTwoImage Γ) :=
  Finite.of_surjective (modTwoIndexMap Γ) (modTwoIndexMap_surjective Γ)

/-- The order of the binary quotient divides the actual subgroup index. -/
theorem modTwoImage_quotient_card_dvd_index (Γ : AddSubgroup M) :
    Nat.card (ModTwo M ⧸ modTwoImage Γ) ∣ Γ.index := by
  rw [AddSubgroup.index_eq_card]
  exact AddSubgroup.card_dvd_of_surjective (modTwoIndexMap Γ) (modTwoIndexMap_surjective Γ)

/-- The finite quotient has exactly two to its dimension elements. -/
theorem modTwoImage_quotient_card (Γ : AddSubgroup M) [Γ.FiniteIndex] :
    Nat.card (ModTwo M ⧸ modTwoImage Γ) =
      2 ^ Module.finrank (ZMod 2) (ModTwo M ⧸ modTwoImage Γ) := by
  have h := Module.natCard_eq_pow_finrank
    (K := ZMod 2) (V := ModTwo M ⧸ modTwoImage Γ)
  have htwo : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [htwo] at h
  exact h

/-- A power of two determined by the actual quotient dimension divides the
index; the rank/index relation is a conclusion of this theorem. -/
theorem two_pow_modTwoImage_quotient_finrank_dvd_index
    (Γ : AddSubgroup M) [Γ.FiniteIndex] :
    2 ^ Module.finrank (ZMod 2) (ModTwo M ⧸ modTwoImage Γ) ∣ Γ.index := by
  rw [← modTwoImage_quotient_card Γ]
  exact modTwoImage_quotient_card_dvd_index Γ

/-- The reduced subgroup's quotient dimension is bounded by the exponent of
two in the actual finite index. -/
theorem modTwoImage_quotient_finrank_le_index_factorization
    (Γ : AddSubgroup M) [Γ.FiniteIndex] :
    Module.finrank (ZMod 2) (ModTwo M ⧸ modTwoImage Γ) ≤ Γ.index.factorization 2 := by
  apply (Nat.prime_two.pow_dvd_iff_le_factorization
    (AddSubgroup.FiniteIndex.index_ne_zero (H := Γ))).mp
  exact two_pow_modTwoImage_quotient_finrank_dvd_index Γ

/-- Integral submodules use the same actual additive index. This wrapper
applies directly to finite-index sublattices of any finite free integer module. -/
theorem submodule_modTwoImage_quotient_finrank_le_index_factorization
    [Module ℤ M] (Γ : Submodule ℤ M) [Γ.toAddSubgroup.FiniteIndex] :
    Module.finrank (ZMod 2) (ModTwo M ⧸ modTwoImage Γ.toAddSubgroup) ≤
      Γ.toAddSubgroup.index.factorization 2 :=
  modTwoImage_quotient_finrank_le_index_factorization Γ.toAddSubgroup

end KltDP.Lattices

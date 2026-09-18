import KltDP.Examples.FrobeniusBlowupDifferential
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# A common factor in an actual differential wedge

Leibniz and alternation imply that `d(t*a) ∧ d(t*b)` is a multiple of `t`.
Consequently every scalar evaluation of the wedge of two elements of a
DVR's maximal ideal belongs to that same maximal ideal. The wedge is the
existing native exterior product, and the derivation is arbitrary.

This is a local differential calculation. It does not identify a canonical
divisor coefficient or define singularity by a determinant condition.
-/

noncomputable section

namespace KltDP.RingTheory.DerivationCommonFactorWedge

open KltDP.Examples.FrobeniusBlowupDifferential

variable {k A M : Type*} [CommRing k] [CommRing A] [Algebra k A]
  [AddCommGroup M] [Module A M] [Module k M]

private theorem wedge_add_left (x y z : M) :
    wedgeTwo (A := A) (x + y) z = wedgeTwo x z + wedgeTwo y z :=
  (exteriorPower.ιMulti A 2).map_vecCons_add ![z] x y

private theorem wedge_smul_left (c : A) (x y : M) :
    wedgeTwo (A := A) (c • x) y = c • wedgeTwo x y :=
  (exteriorPower.ιMulti A 2).map_vecCons_smul ![y] c x

/-- The common original ring factor divides the native differential wedge. -/
theorem wedge_common_factor (D : Derivation k A M) (t a b : A) :
    wedgeTwo (A := A) (D (t * a)) (D (t * b)) =
      t • (wedgeTwo (D a) (D (t * b)) + a • wedgeTwo (D t) (D b)) := by
  rw [D.leibniz, wedge_add_left, wedge_smul_left, wedge_smul_left,
    wedgeTwo_derivation_mul, smul_comm a t, smul_add]

/-- Evaluating the actual wedge preserves divisibility by the common factor. -/
theorem coefficient_mem_span (D : Derivation k A M)
    (ell : (⋀[A]^2 M) →ₗ[A] A) (t a b : A)
    (ha : a ∈ Ideal.span {t}) (hb : b ∈ Ideal.span {t}) :
    ell (wedgeTwo (A := A) (D a) (D b)) ∈ Ideal.span {t} := by
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp ha
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp hb
  apply Ideal.mem_span_singleton.mpr
  refine ⟨ell (wedgeTwo (D r) (D (t * s)) + r • wedgeTwo (D t) (D s)), ?_⟩
  rw [wedge_common_factor, map_smul, smul_eq_mul]

/-- The original DVR supplies its own uniformizer; no generator is assumed. -/
theorem coefficient_mem_maximalIdeal [IsDomain A] [IsDiscreteValuationRing A]
    (D : Derivation k A M) (ell : (⋀[A]^2 M) →ₗ[A] A) (a b : A)
    (ha : a ∈ IsLocalRing.maximalIdeal A)
    (hb : b ∈ IsLocalRing.maximalIdeal A) :
    ell (wedgeTwo (A := A) (D a) (D b)) ∈ IsLocalRing.maximalIdeal A := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible A
  rw [ht.maximalIdeal_eq] at ha hb ⊢
  exact coefficient_mem_span D ell t a b ha hb

end KltDP.RingTheory.DerivationCommonFactorWedge

#check @KltDP.RingTheory.DerivationCommonFactorWedge.wedge_common_factor
#check @KltDP.RingTheory.DerivationCommonFactorWedge.coefficient_mem_maximalIdeal
#print axioms KltDP.RingTheory.DerivationCommonFactorWedge.coefficient_mem_maximalIdeal

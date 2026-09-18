import KltDP.Geometry.CartierLocalClass
import KltDP.Geometry.DivisorOrderLength

/-!
# Positive order of an actual nonzero nonunit in a DVR stalk

The existing integer divisor order is nonnegative on original local
elements. Its proved zero-order characterization and the actual fraction
field embedding make that order strictly positive for a nonzero element
of the original maximal ideal.
-/

noncomputable section

universe u v

namespace KltDP.RingTheory

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The original local nonunit has positive, rather than merely
nonnegative, order after the original fraction-field embedding. -/
theorem divisorOrder_algebraMap_pos_of_mem_maximalIdeal
    (r : R) (hr : r ≠ 0) (hm : r ∈ IsLocalRing.maximalIdeal R) :
    0 < divisorOrder R K (fractionFieldUnit R K r hr) := by
  have hn : divisorOrder R K (fractionFieldUnit R K r hr) ≠ 0 := by
    intro hz
    obtain ⟨u, hu⟩ := (divisorOrder_eq_zero_iff_exists_unit R K _).mp hz
    have huv : algebraMap R K (u : R) = algebraMap R K r :=
      congrArg (fun w : Kˣ => (w : K)) hu
    have heq : (u : R) = r := (IsFractionRing.injective R K) huv
    exact (IsLocalRing.mem_maximalIdeal r).mp hm (heq ▸ u.isUnit)
  exact lt_of_le_of_ne (divisorOrder_algebraMap_nonneg R K r hr) hn.symm

end KltDP.RingTheory

namespace KltDP.Geometry

open AlgebraicGeometry

attribute [local instance] integralSchemeStalk_isDomain

/-- The same positivity for the literal scheme stalk and function field. -/
theorem stalkDivisorOrder_algebraMap_pos_of_mem_maximalIdeal
    (X : Scheme.{u}) [IsIntegral X] (x : X)
    [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (r : X.presheaf.stalk x) (hr : r ≠ 0)
    (hm : r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    0 < stalkDivisorOrder X x
      (RingTheory.fractionFieldUnit (X.presheaf.stalk x) X.functionField r hr) :=
  RingTheory.divisorOrder_algebraMap_pos_of_mem_maximalIdeal
    (X.presheaf.stalk x) X.functionField r hr hm

end KltDP.Geometry

#print axioms KltDP.Geometry.stalkDivisorOrder_algebraMap_pos_of_mem_maximalIdeal

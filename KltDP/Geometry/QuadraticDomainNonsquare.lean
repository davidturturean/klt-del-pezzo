import KltDP.Geometry.QuadraticCoverIntegral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# The actual quadratic domain supplies its nonsquare coefficient

A hypothetical square root in the original fraction field is integral
over the normal base and hence lies in that base. The actual quadratic
root then has a product of its two scalar differences equal to zero.
Either vanishing factor contradicts the original root-coordinate map.
No nonsquare coefficient or irreducibility premise is introduced.
-/

noncomputable section
universe u v

namespace KltDP.Geometry.QuadraticCover

/-- The actual domain quotient of a normal base has no fraction-field scalar root. -/
theorem nonsquare_of_coverAlgebra_isDomain
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (s : R) [IsDomain (CoverAlgebra s)] :
    ∀ x : K, x ^ 2 ≠ algebraMap R K s := by
  intro x hx
  have hint : IsIntegral R (x ^ 2) := by
    rw [hx]
    exact isIntegral_algebraMap
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R := R) (K := K) (x := x) (n := 2) (by decide) hint
  have ha2 : a ^ 2 = s := by
    apply IsFractionRing.injective R K
    rw [map_pow, ha, hx]
  have hprod : (root s - algebraMap R (CoverAlgebra s) a) *
      (root s + algebraMap R (CoverAlgebra s) a) = 0 := by
    calc
      _ = root s ^ 2 - (algebraMap R (CoverAlgebra s) a) ^ 2 := by ring
      _ = 0 := by rw [root_sq, ← map_pow, ha2, sub_self]
  rcases mul_eq_zero.mp hprod with hminus | hplus
  · have h := congrArg (rootCoeff s) hminus
    have hbad : (1 : R) = 0 := by
      simpa only [map_sub, rootCoeff_root, rootCoeff_algebraMap, map_zero, sub_zero] using h
    exact one_ne_zero hbad
  · have h := congrArg (rootCoeff s) hplus
    have hbad : (1 : R) = 0 := by
      simpa only [map_add, rootCoeff_root, rootCoeff_algebraMap, map_zero, add_zero] using h
    exact one_ne_zero hbad

end KltDP.Geometry.QuadraticCover

#print axioms KltDP.Geometry.QuadraticCover.nonsquare_of_coverAlgebra_isDomain

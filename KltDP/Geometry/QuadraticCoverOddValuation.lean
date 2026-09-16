import KltDP.Geometry.QuadraticCoverIntegral
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.RingTheory.Valuation.Basic

/-!
# A finite odd valuation gives an integral quadratic cover

The valuation is an actual `AddValuation K (WithTop ℤ)`. Its finite value on
the original branch coefficient is specified by an integer `z`, and `Odd z`
excludes a square root. In particular, zero is excluded by the valuation's
actual value at zero, rather than by a separate nonzero-branch assumption.

The cover conclusions apply the injective coefficient-map and nonsquare
criterion from `QuadraticCoverIntegral`. No domain, irreducibility, or
integrality conclusion is supplied as an input. No characteristic, unit-two,
positivity, or surjectivity assumption on the valuation is needed here.

Reuse: pinned Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b,
`RingTheory/Valuation/Basic.lean` (`AddValuation.map_zero`, `map_pow`),
`Order/WithBot.lean` and `Algebra/Ring/Int/Parity.lean` (Apache-2.0).
The newer official revision 80cbd0498ab39e21d24d6730b3f932cec672a702
retains the same valuation APIs in `RingTheory/Valuation/Basic.lean`
(Apache-2.0). The finite-value parity argument is a local adapter; no newer
foundational source is ported, and no scheme-wide valuation is constructed.
-/

namespace KltDP.Geometry.QuadraticCover

section Valuation

variable {K : Type*} [Ring K]

/-- A branch with a specified finite integer valuation is nonzero. -/
theorem ne_zero_of_addValuation_eq_int (v : AddValuation K (WithTop ℤ))
    (b : K) (z : ℤ) (hv : v b = (z : WithTop ℤ)) : b ≠ 0 := by
  intro hb
  rw [hb, v.map_zero] at hv
  exact WithTop.top_ne_coe hv

/-- A finite odd value of an actual additive valuation excludes every square root. -/
theorem nonsquare_of_odd_addValuation (v : AddValuation K (WithTop ℤ))
    (b : K) (z : ℤ) (hv : v b = (z : WithTop ℤ)) (hz : Odd z) :
    ∀ x : K, x ^ 2 ≠ b := by
  intro x hx
  have hvalue : v x + v x = (z : WithTop ℤ) := by
    simpa only [v.map_pow, two_nsmul, hv] using congrArg (fun y : K => v y) hx
  by_cases htop : v x = ⊤
  · rw [htop, WithTop.top_add] at hvalue
    exact WithTop.top_ne_coe hvalue
  · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hm, ← WithTop.coe_add] at hvalue
    have heven : Even z := ⟨m, (WithTop.coe_inj.mp hvalue).symm⟩
    exact (Int.not_even_iff_odd.mpr hz) heven

end Valuation

universe u v

variable {R : Type u} [CommRing R]

/-- An odd valuation of the original branch in an injective field extension
makes the actual quadratic quotient a domain. -/
theorem coverAlgebra_isDomain_of_odd_addValuation (K : Type v) [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K)) (s : R)
    (valuation : AddValuation K (WithTop ℤ)) (z : ℤ)
    (hv : valuation (algebraMap R K s) = (z : WithTop ℤ)) (hz : Odd z) :
    IsDomain (CoverAlgebra s) :=
  coverAlgebra_isDomain_of_nonsquare K hinj s
    (nonsquare_of_odd_addValuation valuation (algebraMap R K s) z hv hz)

/-- The actual affine quadratic scheme is integral under the same odd-valuation
criterion, with the original coefficient ring and branch coefficient. -/
theorem affineScheme_isIntegral_of_odd_addValuation (K : Type v) [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K)) (s : R)
    (valuation : AddValuation K (WithTop ℤ)) (z : ℤ)
    (hv : valuation (algebraMap R K s) = (z : WithTop ℤ)) (hz : Odd z) :
    AlgebraicGeometry.IsIntegral (affineScheme s) :=
  affineScheme_isIntegral_of_nonsquare K hinj s
    (nonsquare_of_odd_addValuation valuation (algebraMap R K s) z hv hz)

end KltDP.Geometry.QuadraticCover

import Mathlib.Tactic

/-!
# The scalar equality forced by the actual selected-cover invariants

This arithmetic adapter eliminates the original canonical square and H1
from the computed Euler and Noether identities. Its geometric consumer
derives every identity on one original cover and one original blowdown.
-/

namespace KltDP.Geometry.EvenSelectionRankArithmetic

/-- The derived target invariants force exactly the full forest rank. -/
theorem target_rank_eq_twice_complement
    (r n rhoS rhoV : ℕ) (KSsq KVsq chiV qV : ℤ)
    (hEuler : (chiV : ℚ) = 2 - (n : ℚ) / 4)
    (hEulerH1 : chiV = 1 - qV)
    (hSource : KSsq + (rhoS : ℤ) = 10)
    (hResolution : rhoS = r + 1)
    (hSquare : KVsq = 2 * KSsq)
    (hTarget : KVsq + (rhoV : ℤ) = 10 - 8 * qV) :
    rhoV = 2 * (r - n) := by
  have hEulerFour : 4 * chiV = 8 - (n : ℤ) := by
    have h : 4 * (chiV : ℚ) = 8 - (n : ℚ) := by linarith
    exact_mod_cast h
  omega

end KltDP.Geometry.EvenSelectionRankArithmetic

#print axioms KltDP.Geometry.EvenSelectionRankArithmetic.target_rank_eq_twice_complement

import Mathlib.Tactic

/-!
# Irregularity cancellation for the original double cover and blowdown

The original surface and the target each retain their actual H1 dimension.
The double-cover Euler formula cancels both dimensions from the Noether
relations. No rationality or cohomology-vanishing assumption is needed.
-/

namespace KltDP.Geometry.EvenSelectionIrregularityCancellation

/-- The actual Euler and Noether identities force the full retained-forest
rank, without assuming rationality of either surface. -/
theorem target_rank_eq_twice_complement
    (r n rhoS rhoV : ℕ) (KSsq KVsq chiS chiV qS qV : ℤ)
    (hEuler : (chiV : ℚ) = 2 * (chiS : ℚ) - (n : ℚ) / 4)
    (hSourceEuler : chiS = 1 - qS)
    (hTargetEuler : chiV = 1 - qV)
    (hSource : KSsq + (rhoS : ℤ) = 10 - 8 * qS)
    (hResolution : rhoS = r + 1)
    (hSquare : KVsq = 2 * KSsq)
    (hTarget : KVsq + (rhoV : ℤ) = 10 - 8 * qV) :
    rhoV = 2 * (r - n) := by
  have hEulerFour : 4 * chiV = 8 * chiS - (n : ℤ) := by
    have h : 4 * (chiV : ℚ) = 8 * (chiS : ℚ) - (n : ℚ) := by linarith
    exact_mod_cast h
  omega

end KltDP.Geometry.EvenSelectionIrregularityCancellation

#print axioms KltDP.Geometry.EvenSelectionIrregularityCancellation.target_rank_eq_twice_complement

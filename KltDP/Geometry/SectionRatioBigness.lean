import KltDP.Geometry.SectionRatioHZero

/-!
# Independent original section ratios imply the unchanged bigness predicate

At the actual powers qd the original H0 dimension is at least (q+1)^d.
If the original natural dimension e is at most d and d is positive,
the positive rational coefficient (d^e)⁻¹ turns (qd)^e into q^e,
which is at most (q+1)^d. The powers qd are cofinal. This proves the
existing Picard-section-growth definition for the original Cartier line.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.SectionRatioBigness

open SectionMonomialGrowth

private theorem scaled_power_le_box (d e q : ℕ) (hd : 0 < d) (he : e ≤ d) :
    ((d : ℚ) ^ e)⁻¹ * ((q * d : ℕ) : ℚ) ^ e ≤ (((q + 1) ^ d : ℕ) : ℚ) := by
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  have hz : (d : ℚ) ^ e ≠ 0 := ne_of_gt (pow_pos hdQ e)
  have hscale : ((d : ℚ) ^ e)⁻¹ * ((q * d : ℕ) : ℚ) ^ e = (q : ℚ) ^ e := by
    rw [Nat.cast_mul, mul_pow, mul_left_comm, inv_mul_cancel₀ hz, mul_one]
  rw [hscale]
  have hnat : q ^ e ≤ (q + 1) ^ d :=
    (Nat.pow_le_pow_left (Nat.le_succ q) e).trans
      (Nat.pow_le_pow_right (Nat.succ_pos q) he)
  exact_mod_cast hnat

/-- Algebraically independent ratios of original same-line Cartier sections give actual
bigness. Properness supplies H0 finiteness; the monomial construction supplies all growth. -/
theorem isBig_of_algebraicallyIndependent_ratios
    {X : Scheme.{u}} [IsIntegral X] {k : Type u} [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (D : CartierDivisor X)
    (s₀ : sections (cartierDivisorModule X D)) (hs₀ : s₀ ≠ 0) {d : ℕ}
    (s : Fin d → sections (cartierDivisorModule X D))
    (hs : letI := functionFieldAlgebra f
      AlgebraicIndependent k (fun i => cartierGlobalSectionRationalValue X D (s i) /
        cartierGlobalSectionRationalValue X D s₀))
    (hd : 0 < d) (hdim : Positivity.natDim X ≤ d) :
    Positivity.IsBig f (cartierDivisorInvertibleSheaf X D) := by
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  refine ⟨((d : ℚ) ^ Positivity.natDim X)⁻¹,
    inv_pos.mpr (pow_pos hdQ _), ?_⟩
  intro N
  refine ⟨N * d, Nat.le_mul_of_pos_right N hd, ?_⟩
  calc
    ((d : ℚ) ^ Positivity.natDim X)⁻¹ * ((N * d : ℕ) : ℚ) ^ Positivity.natDim X ≤
        (((N + 1) ^ d : ℕ) : ℚ) := scaled_power_le_box d (Positivity.natDim X) N hd hdim
    _ ≤ (Positivity.picardHZero f
        ((cartierDivisorInvertibleSheaf X D).toPic ^ (N * d)) : ℚ) := by
      exact_mod_cast SectionRatioHZero.box_picardHZero_lowerBound f D s₀ hs₀ s hs N

end KltDP.Geometry.SectionRatioBigness

import KltDP.Geometry.CompleteLinearSystemSectionTuple
import KltDP.Geometry.InvertibleSheafSectionPowers

/-!
# Original nonzero power sections from the unchanged growth predicate

The positive rational growth bound forces positive dimension of the
original H0 for arbitrarily large positive actual tensor powers. The
already constructed complete-section basis supplies an original nonzero
compatible section when the original structure morphism is proper.
This constructs the inputs of a rational map, without claiming birationality.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u

namespace KltDP.Geometry.BigPowerSections

open CompleteLinearSystemSections InvertibleSheafSectionPowers

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (L : InvertibleSheaf X)

/-- The actual power's original H0 dimension is the dimension in the growth predicate. -/
theorem dimension_power_eq_picardHZero (n : ℕ) :
    dimension f (power L n) = Positivity.picardHZero f (L.toPic ^ n) := by
  rw [← power_toPic L n, Positivity.picardHZero_toPic]

/-- The unchanged cofinal growth bound supplies positive-dimensional original power systems. -/
theorem exists_ge_power_dimension_pos (hL : Positivity.IsBig f L) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ 0 < dimension f (power L n) := by
  obtain ⟨c, hc, hgrowth⟩ := hL
  obtain ⟨n, hn, hbound⟩ := hgrowth (max N 1)
  have hnpos : 0 < n :=
    lt_of_lt_of_le Nat.zero_lt_one ((le_max_right N 1).trans hn)
  have hpositive : (0 : ℚ) < c * (n : ℚ) ^ Positivity.natDim X :=
    mul_pos hc (pow_pos (by exact_mod_cast hnpos) _)
  have hdimension : 0 < Positivity.picardHZero f (L.toPic ^ n) := by
    exact_mod_cast (hpositive.trans_le hbound)
  refine ⟨n, (le_max_left N 1).trans hn, hnpos, ?_⟩
  rwa [dimension_power_eq_picardHZero f L n]

/-- Properness turns those positive dimensions into actual nonzero original global sections. -/
theorem exists_ge_nonzero_power_section [IsProper f]
    (hL : Positivity.IsBig f L) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 0 < n ∧
      ∃ s : (power L n).obj.sections, s.val (op ⊤) ≠ 0 := by
  obtain ⟨n, hn, hnpos, hdimension⟩ := exists_ge_power_dimension_pos f L hL N
  obtain ⟨s, hs⟩ :=
    (dimension_pos_iff_exists_nonzero_top_section f (power L n)).mp hdimension
  exact ⟨n, hn, hnpos, s, hs⟩

end KltDP.Geometry.BigPowerSections

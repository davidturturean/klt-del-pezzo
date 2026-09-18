import KltDP.Geometry.BigPowerSections

/-!
# Reflection of original section-growth bigness through positive powers

The unchanged positive rational coefficient scales by `m ^ natDim X`.
Cofinal exponents for the original positive power give the actual
cofinal exponents `m * r` for the original line sheaf.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry.BirationalSectionGrowth

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (L M : InvertibleSheaf X)

/-- Original bigness of an actual positive Picard power implies original
bigness of the input sheaf, with the original field and power exponents. -/
theorem isBig_of_toPic_eq_pow (m : ℕ) (hm : 0 < m)
    (hclass : M.toPic = L.toPic ^ m) (hM : Positivity.IsBig f M) :
    Positivity.IsBig f L := by
  obtain ⟨c, hc, hgrowth⟩ := hM
  have hmQ : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hden : (0 : ℚ) < (m : ℚ) ^ Positivity.natDim X := pow_pos hmQ _
  refine ⟨c / (m : ℚ) ^ Positivity.natDim X, div_pos hc hden, ?_⟩
  intro N
  obtain ⟨r, hr, hbound⟩ := hgrowth N
  refine ⟨m * r, hr.trans (Nat.le_mul_of_pos_left r hm), ?_⟩
  rw [hclass, ← pow_mul] at hbound
  calc
    c / (m : ℚ) ^ Positivity.natDim X * ((m * r : ℕ) : ℚ) ^ Positivity.natDim X =
        c * (r : ℚ) ^ Positivity.natDim X := by
      rw [Nat.cast_mul, mul_pow, ← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hden)]
    _ ≤ (Positivity.picardHZero f (L.toPic ^ (m * r)) : ℚ) := hbound

/-- The same reflection for the existing actual tensor-power object. -/
theorem isBig_of_positive_power (m : ℕ) (hm : 0 < m)
    (hM : Positivity.IsBig f (InvertibleSheafSectionPowers.power L m)) :
    Positivity.IsBig f L :=
  isBig_of_toPic_eq_pow f L (InvertibleSheafSectionPowers.power L m) m hm
    (InvertibleSheafSectionPowers.power_toPic L m) hM

end KltDP.Geometry.BirationalSectionGrowth

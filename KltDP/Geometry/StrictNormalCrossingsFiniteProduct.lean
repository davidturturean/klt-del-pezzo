import KltDP.Geometry.StrictNormalCrossings

/-!
# Finite products with at most two nonunit branches

All unit factors combine into one actual unit. With no three nonunit
factors, the remaining product is empty, one factor, or two factors.
The existing SNC equation predicate is invariant under that unit, so the
one- and two-branch proofs suffice for the whole original product.
-/

noncomputable section

universe u v

namespace KltDP.Geometry.IsStrictNormalCrossingsEquation

/-- Local one- and two-branch SNC equations assemble into the actual finite
product when any three nonunit factors have repeated indices. -/
theorem finprod_of_no_three_nonunits
    {R : Type u} [CommRing R] [IsLocalRing R] {I : Type v} [Fintype I]
    (f : I → R) (hsingle : ∀ i, IsStrictNormalCrossingsEquation R (f i))
    (hdouble : ∀ i j, i ≠ j → ¬ IsUnit (f i) → ¬ IsUnit (f j) →
      IsStrictNormalCrossingsEquation R (f i * f j))
    (hno : ∀ i j l, ¬ IsUnit (f i) → ¬ IsUnit (f j) → ¬ IsUnit (f l) →
      i = j ∨ i = l ∨ j = l) :
    IsStrictNormalCrossingsEquation R (∏ i, f i) := by
  classical
  by_cases hall : ∀ i, IsUnit (f i)
  · exact Or.inl (IsUnit.prod_univ_iff.mpr hall)
  push_neg at hall
  obtain ⟨i, hi⟩ := hall
  by_cases hrest : ∀ j, j ≠ i → IsUnit (f j)
  · have hu : IsUnit (∏ j ∈ Finset.univ.erase i, f j) :=
      IsUnit.prod_iff.mpr fun j hj => hrest j (Finset.mem_erase.mp hj).1
    obtain ⟨u, hu⟩ := hu
    have hprod : (∏ j, f j) = (u : R) * f i := by
      rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i), ← hu, mul_comm]
    rw [hprod]
    exact (hsingle i).unit_mul u
  · push_neg at hrest
    obtain ⟨j, hji, hj⟩ := hrest
    have hu : IsUnit (∏ l ∈ (Finset.univ.erase i).erase j, f l) := by
      apply IsUnit.prod_iff.mpr
      intro l hl
      by_contra hlu
      have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
      have hli : l ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
      rcases hno i j l hi hj hlu with hij | hil | hjl
      · exact hji hij.symm
      · exact hli hil.symm
      · exact hlj hjl.symm
    obtain ⟨u, hu⟩ := hu
    have hjmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
    have hprod : (∏ l, f l) = (u : R) * (f i * f j) := by
      rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i),
        ← Finset.mul_prod_erase (Finset.univ.erase i) f hjmem, ← hu]
      ac_rfl
    rw [hprod]
    exact (hdouble i j (Ne.symm hji) hi hj).unit_mul u

end KltDP.Geometry.IsStrictNormalCrossingsEquation

#print axioms KltDP.Geometry.IsStrictNormalCrossingsEquation.finprod_of_no_three_nonunits

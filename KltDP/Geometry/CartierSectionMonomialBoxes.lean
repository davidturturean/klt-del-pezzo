import KltDP.Geometry.CartierSectionFiniteProducts

/-!
# Actual homogeneous section boxes and their original field ratios

For each coordinate, multiply its selected power by enough copies of the
original denominator section to reach degree q. The product of these d
blocks belongs to the original module O(qdD). Dividing its original field
value by the denominator to degree qd gives the expected monomial.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped BigOperators

universe u

namespace KltDP.Geometry.SectionMonomialGrowth

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X]

/-- An actual degree-q section, padded by the original denominator section. -/
def paddedPower (D : CartierDivisor X)
    (s₀ s : (cartierDivisorModule X D).val.obj (op ⊤))
    (q : ℕ) (a : Fin (q + 1)) :
    (cartierDivisorModule X (q • D)).val.obj (op ⊤) :=
  castSection X (by
    rw [← add_nsmul, Nat.add_sub_of_le (Nat.le_of_lt_succ a.is_lt)])
      (globalProduct X ((a : ℕ) • D) ((q - (a : ℕ)) • D)
        (sectionPower X D s a) (sectionPower X D s₀ (q - (a : ℕ))))

theorem rationalValue_paddedPower (D : CartierDivisor X)
    (s₀ s : (cartierDivisorModule X D).val.obj (op ⊤))
    (q : ℕ) (a : Fin (q + 1)) :
    cartierGlobalSectionRationalValue X (q • D) (paddedPower X D s₀ s q a) =
      cartierGlobalSectionRationalValue X D s ^ (a : ℕ) *
        cartierGlobalSectionRationalValue X D s₀ ^ (q - (a : ℕ)) := by
  simp only [paddedPower, rationalValue_castSection, rationalValue_globalProduct,
    rationalValue_sectionPower]

/-- The actual homogeneous section family indexed by the original exponent box. -/
def boxSection (D : CartierDivisor X)
    (s₀ : (cartierDivisorModule X D).val.obj (op ⊤)) {d : ℕ}
    (s : Fin d → (cartierDivisorModule X D).val.obj (op ⊤))
    (q : ℕ) (a : Fin d → Fin (q + 1)) :
    (cartierDivisorModule X ((q * d) • D)).val.obj (op ⊤) :=
  castSection X (mul_nsmul D q d).symm
    (finiteProduct X (q • D) d (fun i => paddedPower X D s₀ (s i) q (a i)))

theorem rationalValue_boxSection (D : CartierDivisor X)
    (s₀ : (cartierDivisorModule X D).val.obj (op ⊤)) {d : ℕ}
    (s : Fin d → (cartierDivisorModule X D).val.obj (op ⊤))
    (q : ℕ) (a : Fin d → Fin (q + 1)) :
    cartierGlobalSectionRationalValue X ((q * d) • D) (boxSection X D s₀ s q a) =
      ∏ i, (cartierGlobalSectionRationalValue X D (s i) ^ (a i : ℕ) *
        cartierGlobalSectionRationalValue X D s₀ ^ (q - (a i : ℕ))) := by
  simp only [boxSection, rationalValue_castSection, rationalValue_finiteProduct,
    rationalValue_paddedPower]

private theorem padded_power_div {K : Type*} [Field K]
    (x y : K) (hy : y ≠ 0) (q a : ℕ) (ha : a ≤ q) :
    (x ^ a * y ^ (q - a)) / y ^ q = (x / y) ^ a := by
  have hp : y ^ q = y ^ a * y ^ (q - a) := by
    rw [← pow_add, Nat.add_sub_of_le ha]
  rw [div_pow, hp]
  exact mul_div_mul_right _ _ (pow_ne_zero _ hy)

/-- Normalize by the actual original nonzero denominator. The result is
the ordinary monomial in the original function-field section ratios. -/
theorem ratio_boxSection (D : CartierDivisor X)
    (s₀ : (cartierDivisorModule X D).val.obj (op ⊤)) (hs₀ : s₀ ≠ 0) {d : ℕ}
    (s : Fin d → (cartierDivisorModule X D).val.obj (op ⊤))
    (q : ℕ) (a : Fin d → Fin (q + 1)) :
    cartierGlobalSectionRationalValue X ((q * d) • D) (boxSection X D s₀ s q a) /
        cartierGlobalSectionRationalValue X D s₀ ^ (q * d) =
      ∏ i, (cartierGlobalSectionRationalValue X D (s i) /
        cartierGlobalSectionRationalValue X D s₀) ^ (a i : ℕ) := by
  rw [rationalValue_boxSection, pow_mul,
    ← Fin.prod_const d (cartierGlobalSectionRationalValue X D s₀ ^ q),
    ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact padded_power_div _ _ (cartierGlobalSectionRationalValue_ne_zero X D s₀ hs₀)
    q (a i) (Nat.le_of_lt_succ (a i).is_lt)

end KltDP.Geometry.SectionMonomialGrowth

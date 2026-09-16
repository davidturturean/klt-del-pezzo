import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic

/-!
# Moving the positive direction of a Hodge form

The proof uses only bilinearity, symmetry and the ordered-field square laws.
A negative definite orthogonal complement of one vector implies the same
property for every positive-square vector. No dimension or diagonalization
assumption is needed. This supplies the form needed for actual numerical
classes that have positive square but are not given by an ample sheaf.
-/

namespace KltDP.LinearAlgebra.HodgePositiveOrthogonal

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V]

/-- A positive-square vector has negative definite orthogonal complement. -/
theorem neg_of_orthogonal_to_positive (B : LinearMap.BilinForm K V)
    (hsymm : B.IsSymm) (a : V)
    (hnegative : ∀ x : V, B a x = 0 → x ≠ 0 → B x x < 0)
    (h : V) (hpos : 0 < B h h) (c : V)
    (hperp : B h c = 0) (hc : c ≠ 0) : B c c < 0 := by
  classical
  by_contra hnot
  have hcc : 0 ≤ B c c := le_of_not_gt hnot
  by_cases hac : B a c = 0
  · exact not_lt_of_ge hcc (hnegative c hac hc)
  let y := B a h • c - B a c • h
  have hy : B a y = 0 := by
    dsimp [y]
    simp only [map_sub, map_smul, smul_eq_mul]
    ring
  have hy_nonpos : B y y ≤ 0 := by
    by_cases hy0 : y = 0
    · simp only [hy0, map_zero, LinearMap.zero_apply, le_refl]
    · exact le_of_lt (hnegative y hy hy0)
  have hcp : B c h = 0 := (hsymm.eq c h).trans hperp
  have hy_square : B y y = (B a h) ^ 2 * B c c + (B a c) ^ 2 * B h h := by
    dsimp [y]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hperp, hcp]
    ring
  have hleft : 0 ≤ (B a h) ^ 2 * B c c := mul_nonneg (sq_nonneg _) hcc
  have hright : 0 < (B a c) ^ 2 * B h h :=
    mul_pos (sq_pos_of_ne_zero hac) hpos
  rw [hy_square] at hy_nonpos
  linarith

/-- The non-strict version includes the zero vector. -/
theorem nonpos_of_orthogonal_to_positive (B : LinearMap.BilinForm K V)
    (hsymm : B.IsSymm) (a : V)
    (hnegative : ∀ x : V, B a x = 0 → x ≠ 0 → B x x < 0)
    (h : V) (hpos : 0 < B h h) (c : V) (hperp : B h c = 0) : B c c ≤ 0 := by
  classical
  by_cases hc : c = 0
  · simp only [hc, map_zero, LinearMap.zero_apply, le_refl]
  · exact le_of_lt (neg_of_orthogonal_to_positive B hsymm a hnegative h hpos c hperp hc)

/-- The Hodge square inequality for an arbitrary positive-square vector. -/
theorem square_inequality (B : LinearMap.BilinForm K V)
    (hsymm : B.IsSymm) (a : V)
    (hnegative : ∀ x : V, B a x = 0 → x ≠ 0 → B x x < 0)
    (h : V) (hpos : 0 < B h h) (c : V) : B h h * B c c ≤ (B h c) ^ 2 := by
  classical
  let y := B h h • c - B h c • h
  have hy : B h y = 0 := by
    dsimp [y]
    simp only [map_sub, map_smul, smul_eq_mul]
    ring
  have hy_nonpos := nonpos_of_orthogonal_to_positive B hsymm a hnegative h hpos y hy
  have hy_square : B y y = B h h * (B h h * B c c - (B h c) ^ 2) := by
    dsimp [y]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hsymm.eq c h]
    ring
  rw [hy_square] at hy_nonpos
  by_contra hnot
  exact not_lt_of_ge hy_nonpos (mul_pos hpos (sub_pos.mpr (lt_of_not_ge hnot)))

end KltDP.LinearAlgebra.HodgePositiveOrthogonal

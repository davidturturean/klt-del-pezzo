import KltDP.Manuscript.S06.AdjacentContactAdjoint
import KltDP.Manuscript.S03.PrimitiveSquareZero

/-!
# Manuscript Proposition 6.5: an effective adjoint from three `(-2)`-contacts

Source: `source/manuscript.tex`, lines 1818–1878, label `prop:cubic-adjoint`.

Let `C₀, C₁, C₂ ⊂ D` be pairwise disjoint exceptional `(-2)`-curves and `P` an exterior
`(-1)`-curve with `P · C_i = 1`. With `F₁ = C₀ + 2P + C₁`, `F₂ = C₀ + 2P + C₂` and
`A = C₀ + C₁ + C₂ + 3P`:

* `F₁, F₂` are nef with `F_i² = 0`, `K_S · F_i = -2` (so they are fibre classes of rational rulings
  by Lemma 3.1, `primitiveSquareZero_ruling`), `F₁ · F₂ = 2`; `A` is nef with `A² = 3`,
  `K_S · A = -3` and `(A·C₀, A·C₁, A·C₂, A·P) = (1, 1, 1, 0)`;
* there is a unique effective `E ∼ K_S + C₀ + C₁ + C₂ + 2P` with support disjoint from
  `C₀ ∪ C₁ ∪ C₂ ∪ P`, null for `F₁` and `F₂`, with `L · E = 2 L·P - L²`;
* every exterior `Q ≠ P` null for both rulings is a `(-1)`-curve occurring in `E`;
* if `E = 0`, or there is no such `Q`, then `#Sing(X) ≤ 7`.

The infrastructure (numerical classes of Weil divisors, Riemann–Roch for adjoints, Hodge
uniqueness, negative definiteness of the exceptional locus) is that of
`S06.AdjacentContactAdjoint`.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.DisjointNegativeCurvesRank KltDP.Geometry.SurfaceRiemannRochSource
open KltDP.Manuscript KltDP.Manuscript.S02 KltDP.Manuscript.S04

universe u

namespace KltDP.Manuscript.S06Adj

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)

/-! ### Intersection numbers of exceptional curves -/

theorem inter_self (i : R.Vertices) :
    ((i.val).intersectionNumber (R.S.primeCurveCartier R.hreg i.val) : ℚ) = -R.w i := by
  rw [inter_vertices, M_diag]

theorem inter_of_not_adj {i j : R.Vertices} (hne : i ≠ j) (h : ¬ R.graph.Adj i j) :
    ((i.val).intersectionNumber (R.S.primeCurveCartier R.hreg j.val) : ℚ) = 0 := by
  rw [inter_vertices, M_eq_zero_of_not_adj R hne h]

theorem inter_contact (P : R.S.PrimeCurve) (i : R.Vertices) (h : R.contact P i = 1) :
    (P.intersectionNumber (R.S.primeCurveCartier R.hreg i.val) : ℚ) = 1 := by
  exact_mod_cast h

theorem inter_contact' (P : R.S.PrimeCurve) (i : R.Vertices) (h : R.contact P i = 1) :
    ((i.val).intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) = 1 := by
  rw [inter_comm]
  exact_mod_cast h

theorem inter_self_minusOne (P : R.S.PrimeCurve) (hP : IsMinusOneCurve R.hreg P) :
    (P.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) = -1 := by
  have h : P.intersectionNumber (R.S.primeCurveCartier R.hreg P) = -1 := hP.selfIntersection
  rw [h]
  push_cast
  ring

theorem exterior_ne_vertex (P : R.S.PrimeCurve) (hP : ¬ IsExceptionalCurve R.π P) (i : R.Vertices) :
    P ≠ i.val := fun h => hP (h ▸ i.property)

theorem vertex_ne_of_ne {i j : R.Vertices} (h : i ≠ j) : i.val ≠ j.val :=
  fun h' => h (Subtype.ext h')

/-! ## Proposition 6.5: the three-contact configuration -/

section Cubic

variable (P : R.S.PrimeCurve) (C₀ C₁ C₂ : R.Vertices)

/-- The divisor `a₀ C₀ + a₁ C₁ + a₂ C₂ + q P`. -/
def cubDiv (a₀ a₁ a₂ q : ℤ) : R.S.WeilDivisor :=
  Finsupp.single C₀.val a₀ + Finsupp.single C₁.val a₁ + Finsupp.single C₂.val a₂ +
    Finsupp.single P q

theorem numW_cubDiv (a₀ a₁ a₂ q : ℤ) :
    numW R (cubDiv R P C₀ C₁ C₂ a₀ a₁ a₂ q) = (a₀ : ℚ) • curveClass R.S R.hreg C₀.val +
      (a₁ : ℚ) • curveClass R.S R.hreg C₁.val + (a₂ : ℚ) • curveClass R.S R.hreg C₂.val +
      (q : ℚ) • curveClass R.S R.hreg P := by
  simp only [cubDiv, map_add, numW_single]

theorem degW_cubDiv (a₀ a₁ a₂ q : ℤ) (Q : R.S.PrimeCurve) :
    degW R Q (cubDiv R P C₀ C₁ C₂ a₀ a₁ a₂ q) =
      (a₀ : ℚ) * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C₀.val) : ℚ) +
      (a₁ : ℚ) * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C₁.val) : ℚ) +
      (a₂ : ℚ) * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C₂.val) : ℚ) +
      (q : ℚ) * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) := by
  simp only [cubDiv, degW_add, degW_single]

/-- The pairing of `a₀ C₀ + a₁ C₁ + a₂ C₂ + q P` with an arbitrary Weil divisor `D`. -/
theorem pairing_cubDiv (a₀ a₁ a₂ q : ℤ) (D : R.S.WeilDivisor) :
    R.S.numericalIntersectionBilinForm R.hreg (numW R (cubDiv R P C₀ C₁ C₂ a₀ a₁ a₂ q)) (numW R D) =
      (a₀ : ℚ) * degW R C₀.val D + (a₁ : ℚ) * degW R C₁.val D + (a₂ : ℚ) * degW R C₂.val D +
        (q : ℚ) * degW R P D := by
  rw [numW_cubDiv]
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, degW_eq_pairing]

theorem Knum_pairing_cubDiv (hP : R.IsExteriorMinusOne P) (a₀ a₁ a₂ q : ℤ) :
    R.S.numericalIntersectionBilinForm R.hreg R.Knum (numW R (cubDiv R P C₀ C₁ C₂ a₀ a₁ a₂ q)) =
      (a₀ : ℚ) * (R.w C₀ - 2) + (a₁ : ℚ) * (R.w C₁ - 2) + (a₂ : ℚ) * (R.w C₂ - 2) - q := by
  rw [numW_cubDiv]
  simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, Knum_pairing_cc,
    R.Kdeg_exceptional, Kdeg_eq_neg_one_of_isMinusOne R P hP.1, ResolutionDatum.q]
  push_cast
  ring

theorem Lnum_pairing_cubDiv (a₀ a₁ a₂ q : ℤ) :
    R.S.numericalIntersectionBilinForm R.hreg R.Lnum (numW R (cubDiv R P C₀ C₁ C₂ a₀ a₁ a₂ q)) =
      (q : ℚ) * R.Ldeg P := by
  rw [numW_cubDiv]
  simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, Lnum_pairing_curveClass,
    R.Ldeg_exceptional]
  ring

/-- Nefness of `a₀ C₀ + a₁ C₁ + a₂ C₂ + q P` from its degrees on the configuration. -/
theorem cubDiv_nef (a₀ a₁ a₂ q : ℤ) (h₀ : 0 ≤ a₀) (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂) (hq : 0 ≤ q)
    (d₀ : 0 ≤ degW R C₀.val (cubDiv R P C₀ C₁ C₂ a₀ a₁ a₂ q))
    (d₁ : 0 ≤ degW R C₁.val (cubDiv R P C₀ C₁ C₂ a₀ a₁ a₂ q))
    (d₂ : 0 ≤ degW R C₂.val (cubDiv R P C₀ C₁ C₂ a₀ a₁ a₂ q))
    (dP : 0 ≤ degW R P (cubDiv R P C₀ C₁ C₂ a₀ a₁ a₂ q)) :
    ∀ Q : R.S.PrimeCurve, 0 ≤ degW R Q (cubDiv R P C₀ C₁ C₂ a₀ a₁ a₂ q) := by
  intro Q
  by_cases hQ₀ : Q = C₀.val
  · rw [hQ₀]; exact d₀
  by_cases hQ₁ : Q = C₁.val
  · rw [hQ₁]; exact d₁
  by_cases hQ₂ : Q = C₂.val
  · rw [hQ₂]; exact d₂
  by_cases hQP : Q = P
  · rw [hQP]; exact dP
  rw [degW_cubDiv]
  have h₀' : (0 : ℚ) ≤ a₀ := by exact_mod_cast h₀
  have h₁' : (0 : ℚ) ≤ a₁ := by exact_mod_cast h₁
  have h₂' : (0 : ℚ) ≤ a₂ := by exact_mod_cast h₂
  have hq' : (0 : ℚ) ≤ q := by exact_mod_cast hq
  exact add_nonneg (add_nonneg (add_nonneg (mul_nonneg h₀' (inter_nonneg R Q C₀.val hQ₀))
    (mul_nonneg h₁' (inter_nonneg R Q C₁.val hQ₁))) (mul_nonneg h₂' (inter_nonneg R Q C₂.val hQ₂)))
    (mul_nonneg hq' (inter_nonneg R Q P hQP))

/-- A curve outside the configuration which is null for `C₀ + C₁ + C₂ + 3P` is disjoint from
the four curves. -/
theorem null_A_inter_eq_zero (Q : R.S.PrimeCurve) (hQ₀ : Q ≠ C₀.val) (hQ₁ : Q ≠ C₁.val)
    (hQ₂ : Q ≠ C₂.val) (hQP : Q ≠ P) (h0 : degW R Q (cubDiv R P C₀ C₁ C₂ 1 1 1 3) = 0) :
    (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C₀.val) : ℚ) = 0 ∧
    (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C₁.val) : ℚ) = 0 ∧
    (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C₂.val) : ℚ) = 0 ∧
    (Q.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) = 0 := by
  rw [degW_cubDiv] at h0
  have h₀ := inter_nonneg R Q C₀.val hQ₀
  have h₁ := inter_nonneg R Q C₁.val hQ₁
  have h₂ := inter_nonneg R Q C₂.val hQ₂
  have hp := inter_nonneg R Q P hQP
  push_cast at h0
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- A curve outside the configuration which is null for both rulings `F₁ = C₀ + 2P + C₁`,
`F₂ = C₀ + 2P + C₂` is disjoint from the four curves. -/
theorem null_rulings_inter_eq_zero (Q : R.S.PrimeCurve) (hQ₀ : Q ≠ C₀.val) (hQ₁ : Q ≠ C₁.val)
    (hQ₂ : Q ≠ C₂.val) (hQP : Q ≠ P) (h1 : degW R Q (cubDiv R P C₀ C₁ C₂ 1 1 0 2) = 0)
    (h2 : degW R Q (cubDiv R P C₀ C₁ C₂ 1 0 1 2) = 0) :
    (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C₀.val) : ℚ) = 0 ∧
    (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C₁.val) : ℚ) = 0 ∧
    (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C₂.val) : ℚ) = 0 ∧
    (Q.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) = 0 := by
  rw [degW_cubDiv] at h1 h2
  have h₀ := inter_nonneg R Q C₀.val hQ₀
  have h₁ := inter_nonneg R Q C₁.val hQ₁
  have h₂ := inter_nonneg R Q C₂.val hQ₂
  have hp := inter_nonneg R Q P hQP
  push_cast at h1 h2
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

variable (hP : R.IsExteriorMinusOne P) (h01 : C₀ ≠ C₁) (h02 : C₀ ≠ C₂) (h12 : C₁ ≠ C₂)
  (hn01 : ¬ R.graph.Adj C₀ C₁) (hn02 : ¬ R.graph.Adj C₀ C₂) (hn12 : ¬ R.graph.Adj C₁ C₂)
  (hw0 : R.w C₀ = 2) (hw1 : R.w C₁ = 2) (hw2 : R.w C₂ = 2)
  (hc0 : R.contact P C₀ = 1) (hc1 : R.contact P C₁ = 1) (hc2 : R.contact P C₂ = 1)

/-! ### The intersection table (manuscript lines 1839–1844) -/

include hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2 in
/-- The degrees of `F₁ = C₀ + 2P + C₁`, `F₂ = C₀ + 2P + C₂` and `A = C₀ + C₁ + C₂ + 3P` on the
configuration. -/
theorem cubic_degrees :
    (degW R C₀.val (cubDiv R P C₀ C₁ C₂ 1 1 0 2) = 0 ∧ degW R C₁.val (cubDiv R P C₀ C₁ C₂ 1 1 0 2) = 0 ∧
      degW R C₂.val (cubDiv R P C₀ C₁ C₂ 1 1 0 2) = 2 ∧ degW R P (cubDiv R P C₀ C₁ C₂ 1 1 0 2) = 0) ∧
    (degW R C₀.val (cubDiv R P C₀ C₁ C₂ 1 0 1 2) = 0 ∧ degW R C₁.val (cubDiv R P C₀ C₁ C₂ 1 0 1 2) = 2 ∧
      degW R C₂.val (cubDiv R P C₀ C₁ C₂ 1 0 1 2) = 0 ∧ degW R P (cubDiv R P C₀ C₁ C₂ 1 0 1 2) = 0) ∧
    (degW R C₀.val (cubDiv R P C₀ C₁ C₂ 1 1 1 3) = 1 ∧ degW R C₁.val (cubDiv R P C₀ C₁ C₂ 1 1 1 3) = 1 ∧
      degW R C₂.val (cubDiv R P C₀ C₁ C₂ 1 1 1 3) = 1 ∧ degW R P (cubDiv R P C₀ C₁ C₂ 1 1 1 3) = 0) := by
  have i00 := inter_self R C₀
  have i11 := inter_self R C₁
  have i22 := inter_self R C₂
  have i01 := inter_of_not_adj R h01 hn01
  have i10 := inter_of_not_adj R h01.symm (fun h => hn01 h.symm)
  have i02 := inter_of_not_adj R h02 hn02
  have i20 := inter_of_not_adj R h02.symm (fun h => hn02 h.symm)
  have i12 := inter_of_not_adj R h12 hn12
  have i21 := inter_of_not_adj R h12.symm (fun h => hn12 h.symm)
  have iP0 := inter_contact R P C₀ hc0
  have iP1 := inter_contact R P C₁ hc1
  have iP2 := inter_contact R P C₂ hc2
  have i0P := inter_contact' R P C₀ hc0
  have i1P := inter_contact' R P C₁ hc1
  have i2P := inter_contact' R P C₂ hc2
  have iPP := inter_self_minusOne R P hP.1
  simp only [degW_cubDiv, i00, i11, i22, i01, i10, i02, i20, i12, i21, iP0, iP1, iP2, i0P, i1P, i2P,
    iPP, hw0, hw1, hw2]
  norm_num

include hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2 in
/-- `F₁, F₂, A` are nef. -/
theorem cubic_nef :
    (∀ Q : R.S.PrimeCurve, 0 ≤ degW R Q (cubDiv R P C₀ C₁ C₂ 1 1 0 2)) ∧
    (∀ Q : R.S.PrimeCurve, 0 ≤ degW R Q (cubDiv R P C₀ C₁ C₂ 1 0 1 2)) ∧
    (∀ Q : R.S.PrimeCurve, 0 ≤ degW R Q (cubDiv R P C₀ C₁ C₂ 1 1 1 3)) := by
  obtain ⟨⟨a0, a1, a2, aP⟩, ⟨b0, b1, b2, bP⟩, ⟨c0, c1, c2, cP⟩⟩ :=
    cubic_degrees R P C₀ C₁ C₂ hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2
  refine ⟨cubDiv_nef R P C₀ C₁ C₂ 1 1 0 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [a0]) (by rw [a1]) (by rw [a2]; norm_num) (by rw [aP]),
    cubDiv_nef R P C₀ C₁ C₂ 1 0 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [b0]) (by rw [b1]; norm_num) (by rw [b2]) (by rw [bP]),
    cubDiv_nef R P C₀ C₁ C₂ 1 1 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [c0]; norm_num) (by rw [c1]; norm_num) (by rw [c2]; norm_num) (by rw [cP])⟩

include hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2 in
/-- The numerical data: `F_i² = 0`, `K_S · F_i = -2`, `F₁ · F₂ = 2`, `A² = 3`, `K_S · A = -3`. -/
theorem cubic_numbers :
    R.S.numericalIntersectionBilinForm R.hreg (numW R (cubDiv R P C₀ C₁ C₂ 1 1 0 2))
      (numW R (cubDiv R P C₀ C₁ C₂ 1 1 0 2)) = 0 ∧
    R.S.numericalIntersectionBilinForm R.hreg (numW R (cubDiv R P C₀ C₁ C₂ 1 0 1 2))
      (numW R (cubDiv R P C₀ C₁ C₂ 1 0 1 2)) = 0 ∧
    R.S.numericalIntersectionBilinForm R.hreg (numW R (cubDiv R P C₀ C₁ C₂ 1 1 0 2))
      (numW R (cubDiv R P C₀ C₁ C₂ 1 0 1 2)) = 2 ∧
    R.S.numericalIntersectionBilinForm R.hreg (numW R (cubDiv R P C₀ C₁ C₂ 1 1 1 3))
      (numW R (cubDiv R P C₀ C₁ C₂ 1 1 1 3)) = 3 ∧
    R.S.numericalIntersectionBilinForm R.hreg R.Knum (numW R (cubDiv R P C₀ C₁ C₂ 1 1 0 2)) = -2 ∧
    R.S.numericalIntersectionBilinForm R.hreg R.Knum (numW R (cubDiv R P C₀ C₁ C₂ 1 0 1 2)) = -2 ∧
    R.S.numericalIntersectionBilinForm R.hreg R.Knum (numW R (cubDiv R P C₀ C₁ C₂ 1 1 1 3)) = -3 := by
  obtain ⟨⟨a0, a1, a2, aP⟩, ⟨b0, b1, b2, bP⟩, ⟨c0, c1, c2, cP⟩⟩ :=
    cubic_degrees R P C₀ C₁ C₂ hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pairing_cubDiv, a0, a1, a2, aP]; norm_num
  · rw [pairing_cubDiv, b0, b1, b2, bP]; norm_num
  · rw [pairing_cubDiv, b0, b1, b2, bP]; norm_num
  · rw [pairing_cubDiv, c0, c1, c2, cP]; norm_num
  · rw [Knum_pairing_cubDiv R P C₀ C₁ C₂ hP, hw0, hw1, hw2]; norm_num
  · rw [Knum_pairing_cubDiv R P C₀ C₁ C₂ hP, hw0, hw1, hw2]; norm_num
  · rw [Knum_pairing_cubDiv R P C₀ C₁ C₂ hP, hw0, hw1, hw2]; norm_num

/-! ### The rational rulings `F₁`, `F₂` (Lemma 3.1) -/

include hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2 in
/-- The Cartier divisors of `F₁` and `F₂` are nef with square zero and `K_S · F_i = -2`, hence are
fibre classes of rational rulings (`KltDP.Manuscript.S03.primitiveSquareZero_ruling`). -/
theorem cubic_rulings (p : ℕ) [CharP k p] (hp : 0 < p) :
    ∀ F : R.S.WeilDivisor, (F = cubDiv R P C₀ C₁ C₂ 1 1 0 2 ∨ F = cubDiv R P C₀ C₁ C₂ 1 0 1 2) →
      Positivity.IsNef R.S.structureMorphism (cartierDivisorInvertibleSheaf R.S.toScheme
        ((R.S.regularCartierWeilEquiv R.hreg).symm F)) ∧
      R.S.intersectionPairing R.hreg ((R.S.regularCartierWeilEquiv R.hreg).symm F)
        ((R.S.regularCartierWeilEquiv R.hreg).symm F) = 0 ∧
      R.S.intersectionPairing R.hreg R.KS ((R.S.regularCartierWeilEquiv R.hreg).symm F) = -2 ∧
      ∃ g : R.S.toScheme ⟶ projectiveSpace k 1,
        g ≫ projectiveSpaceToSpec k 1 = R.S.structureMorphism ∧ IsProper g ∧ Surjective g := by
  obtain ⟨nef₁, nef₂, -⟩ := cubic_nef R P C₀ C₁ C₂ hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2
  obtain ⟨sq₁, sq₂, -, -, K₁, K₂, -⟩ :=
    cubic_numbers R P C₀ C₁ C₂ hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2
  intro F hF
  have hnef : ∀ Q : R.S.PrimeCurve, 0 ≤ degW R Q F := by
    rcases hF with rfl | rfl
    · exact nef₁
    · exact nef₂
  have hsq : R.S.numericalIntersectionBilinForm R.hreg (numW R F) (numW R F) = 0 := by
    rcases hF with rfl | rfl
    · exact sq₁
    · exact sq₂
  have hK : R.S.numericalIntersectionBilinForm R.hreg R.Knum (numW R F) = -2 := by
    rcases hF with rfl | rfl
    · exact K₁
    · exact K₂
  have hFF : R.S.intersectionPairing R.hreg ((R.S.regularCartierWeilEquiv R.hreg).symm F)
      ((R.S.regularCartierWeilEquiv R.hreg).symm F) = 0 := by
    have h := intersectionPairing_symm_symm R F F
    rw [hsq] at h
    exact_mod_cast h
  have hKF : R.S.intersectionPairing R.hreg R.KS ((R.S.regularCartierWeilEquiv R.hreg).symm F) =
      -2 := by
    have h := intersectionPairing_symm_symm R (R.S.cartierToWeilHom R.KS) F
    rw [symm_KS, numW_KS, hK] at h
    exact_mod_cast h
  have hnefC := isNef_symm R F hnef
  refine ⟨hnefC, hFF, hKF, ?_⟩
  obtain ⟨g, hg, hproper, hsurj, -⟩ :=
    KltDP.Manuscript.S03.primitiveSquareZero_ruling R p hp _ hnefC hFF hKF
  exact ⟨g, hg, hproper, hsurj⟩

/-! ### The effective adjoint `E` (manuscript lines 1848–1856) -/

/-- The conclusions of Proposition 6.5 about the effective adjoint
`E ∼ K_S + C₀ + C₁ + C₂ + 2P`. -/
structure CubicRemainder (E : R.S.WeilDivisor) : Prop where
  effective : EffectiveDivisor E
  adjoint : R.S.LinearlyEquivalent (R.S.cartierToWeilHom R.KS + cubDiv R P C₀ C₁ C₂ 1 1 1 3)
    (Finsupp.single P 1 + E)
  class_eq : R.S.LinearlyEquivalent E (R.S.cartierToWeilHom R.KS + cubDiv R P C₀ C₁ C₂ 1 1 1 2)
  coeff_C₀ : E C₀.val = 0
  coeff_C₁ : E C₁.val = 0
  coeff_C₂ : E C₂.val = 0
  coeff_P : E P = 0
  null_A : ∀ Q : R.S.PrimeCurve, E Q ≠ 0 → degW R Q (cubDiv R P C₀ C₁ C₂ 1 1 1 3) = 0
  null_F₁ : ∀ Q : R.S.PrimeCurve, E Q ≠ 0 → degW R Q (cubDiv R P C₀ C₁ C₂ 1 1 0 2) = 0
  null_F₂ : ∀ Q : R.S.PrimeCurve, E Q ≠ 0 → degW R Q (cubDiv R P C₀ C₁ C₂ 1 0 1 2) = 0
  inter_zero : ∀ Q : R.S.PrimeCurve, E Q ≠ 0 →
    (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C₀.val) : ℚ) = 0 ∧
    (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C₁.val) : ℚ) = 0 ∧
    (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C₂.val) : ℚ) = 0 ∧
    (Q.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) = 0
  disjoint : ∀ Q : R.S.PrimeCurve, E Q ≠ 0 →
    Disjoint (Q : Set R.S.toScheme) (C₀.val : Set R.S.toScheme) ∧
    Disjoint (Q : Set R.S.toScheme) (C₁.val : Set R.S.toScheme) ∧
    Disjoint (Q : Set R.S.toScheme) (C₂.val : Set R.S.toScheme) ∧
    Disjoint (Q : Set R.S.toScheme) (P : Set R.S.toScheme)
  Ldeg_eq : LdegW R E = 2 * R.Ldeg P - R.Lsq
  exterior_minusOne : ∀ Q : R.S.PrimeCurve, E Q ≠ 0 → ¬ IsExceptionalCurve R.π Q →
    IsMinusOneCurve R.hreg Q ∧ R.Kdeg Q = -1
  exterior_mem : ∀ Q : R.S.PrimeCurve, ¬ IsExceptionalCurve R.π Q → Q ≠ P →
    degW R Q (cubDiv R P C₀ C₁ C₂ 1 1 0 2) = 0 → degW R Q (cubDiv R P C₀ C₁ C₂ 1 0 1 2) = 0 →
    IsMinusOneCurve R.hreg Q ∧ 0 < E Q
  unique : ∀ E' : R.S.WeilDivisor, EffectiveDivisor E' → R.S.LinearlyEquivalent E' E → E' = E

include hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2 in
/-- **Proposition 6.5, existence and properties of `E`** (manuscript lines 1846–1873). -/
theorem cubicAdjoint (p : ℕ) [CharP k p] (hp : 0 < p) :
    ∃ E : R.S.WeilDivisor, CubicRemainder R P C₀ C₁ C₂ E := by
  classical
  obtain ⟨⟨a0, a1, a2, aP⟩, ⟨b0, b1, b2, bP⟩, ⟨c0, c1, c2, cP⟩⟩ :=
    cubic_degrees R P C₀ C₁ C₂ hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2
  obtain ⟨-, -, hnefA⟩ :=
    cubic_nef R P C₀ C₁ C₂ hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2
  obtain ⟨-, -, -, sqA, -, -, KA⟩ :=
    cubic_numbers R P C₀ C₁ C₂ hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2
  set A := cubDiv R P C₀ C₁ C₂ 1 1 1 3 with hAdef
  have hsq : 0 < R.S.numericalIntersectionBilinForm R.hreg (numW R A) (numW R A) := by
    rw [sqA]; norm_num
  have hrr : 0 < R.S.numericalIntersectionBilinForm R.hreg (R.Knum + numW R A) (numW R A) / 2 + 1 := by
    rw [LinearMap.BilinForm.add_left, KA, sqA]; norm_num
  obtain ⟨Z, hZ, hlin⟩ := exists_effective_adjoint R p hp A hnefA hsq hrr
  have hnumZ : numW R Z = R.Knum + numW R A := by
    rw [numW_eq_of_linearlyEquivalent R hlin, map_add, numW_KS]
  have hAZ : R.S.numericalIntersectionBilinForm R.hreg (numW R A) (numW R Z) = 0 := by
    rw [hnumZ, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.IsSymm.eq (R.S.numericalIntersectionBilinForm_isSymm R.hreg) _ R.Knum,
      KA, sqA]
    norm_num
  have hZnull : ∀ Q : R.S.PrimeCurve, Z Q ≠ 0 → degW R Q A = 0 :=
    degW_eq_zero_of_component R A Z hnefA hZ hAZ
  -- distinctness
  have hP0 := exterior_ne_vertex R P hP.2 C₀
  have hP1 := exterior_ne_vertex R P hP.2 C₁
  have hP2 := exterior_ne_vertex R P hP.2 C₂
  -- `C_i` are not components of `Z` (they are not `A`-null)
  have hZ0 : Z C₀.val = 0 := by
    by_contra h
    have := hZnull _ h
    rw [c0] at this
    exact one_ne_zero this
  have hZ1 : Z C₁.val = 0 := by
    by_contra h
    have := hZnull _ h
    rw [c1] at this
    exact one_ne_zero this
  have hZ2 : Z C₂.val = 0 := by
    by_contra h
    have := hZnull _ h
    rw [c2] at this
    exact one_ne_zero this
  -- the remainder `E = Z - (Z P) P`
  set E : R.S.WeilDivisor := Z - Finsupp.single P (Z P) with hEdef
  have hEapply : ∀ Q, E Q = Z Q - if P = Q then Z P else 0 := by
    intro Q
    simp only [hEdef, Finsupp.sub_apply, Finsupp.single_apply]
  have hEP : E P = 0 := by rw [hEapply]; simp
  have hEother : ∀ Q, Q ≠ P → E Q = Z Q := by
    intro Q hQ
    rw [hEapply]
    simp [Ne.symm hQ]
  have hE0 : E C₀.val = 0 := by rw [hEother _ (Ne.symm hP0), hZ0]
  have hE1 : E C₁.val = 0 := by rw [hEother _ (Ne.symm hP1), hZ1]
  have hE2 : E C₂.val = 0 := by rw [hEother _ (Ne.symm hP2), hZ2]
  have hEeff : EffectiveDivisor E := by
    intro Q
    by_cases hQ : Q = P
    · rw [hQ, hEP]
    · rw [hEother Q hQ]; exact hZ Q
  have hEne : ∀ Q, E Q ≠ 0 → Q ≠ C₀.val ∧ Q ≠ C₁.val ∧ Q ≠ C₂.val ∧ Q ≠ P ∧ Z Q ≠ 0 := by
    intro Q hQ
    have hQ0 : Q ≠ C₀.val := fun h => hQ (h ▸ hE0)
    have hQ1 : Q ≠ C₁.val := fun h => hQ (h ▸ hE1)
    have hQ2 : Q ≠ C₂.val := fun h => hQ (h ▸ hE2)
    have hQP : Q ≠ P := fun h => hQ (h ▸ hEP)
    refine ⟨hQ0, hQ1, hQ2, hQP, ?_⟩
    rwa [hEother Q hQP] at hQ
  have hEnullA : ∀ Q : R.S.PrimeCurve, E Q ≠ 0 → degW R Q A = 0 :=
    fun Q hQ => hZnull Q (hEne Q hQ).2.2.2.2
  have hEinter : ∀ Q : R.S.PrimeCurve, E Q ≠ 0 →
      (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C₀.val) : ℚ) = 0 ∧
      (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C₁.val) : ℚ) = 0 ∧
      (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C₂.val) : ℚ) = 0 ∧
      (Q.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) = 0 := by
    intro Q hQ
    obtain ⟨hQ0, hQ1, hQ2, hQP, -⟩ := hEne Q hQ
    exact null_A_inter_eq_zero R P C₀ C₁ C₂ Q hQ0 hQ1 hQ2 hQP (hEnullA Q hQ)
  -- the coefficient of `P` in `Z` is one: `Z · P = (K_S + A) · P = -1`
  have hdegP : degW R P Z = -1 := by
    unfold degW
    rw [hnumZ, map_add, KltDP.Manuscript.S03.numericalRestrictionDegree_Knum,
      Kdeg_eq_neg_one_of_isMinusOne R P hP.1]
    have : R.S.numericalRestrictionDegree P (numW R A) = degW R P A := rfl
    rw [this, cP]
    push_cast
    ring
  have hdegPE : degW R P E = 0 := by
    rw [degW_eq_sum]
    refine Finset.sum_eq_zero (fun Q hQ => ?_)
    obtain ⟨-, -, -, h4⟩ := hEinter Q (Finsupp.mem_support_iff.mp hQ)
    rw [inter_comm R P Q, h4, mul_zero]
  have hZP : Z P = 1 := by
    have hZdecomp : Z = E + Finsupp.single P (Z P) := by rw [hEdef]; abel
    have h := hdegP
    nth_rewrite 1 [hZdecomp] at h
    rw [degW_add, degW_single, hdegPE, inter_self_minusOne R P hP.1] at h
    have h' : (Z P : ℚ) = 1 := by linarith
    exact_mod_cast h'
  have hZdecomp : Z = Finsupp.single P 1 + E := by
    rw [hEdef, hZP]; abel
  -- the class of `E`
  have hclass : R.S.LinearlyEquivalent E (R.S.cartierToWeilHom R.KS + cubDiv R P C₀ C₁ C₂ 1 1 1 2) := by
    have h := linearlyEquivalent_of_sub R (Z := Z) (N := E) (X := Finsupp.single P 1)
      (by rw [hZdecomp, add_comm]) hlin
    have hsub : R.S.cartierToWeilHom R.KS + A - Finsupp.single P 1 =
        R.S.cartierToWeilHom R.KS + cubDiv R P C₀ C₁ C₂ 1 1 1 2 := by
      have e : Finsupp.single P (3 : ℤ) = Finsupp.single P 2 + Finsupp.single P 1 := by
        rw [← Finsupp.single_add]; norm_num
      simp only [hAdef, cubDiv]
      rw [e]
      abel
    rwa [hsub] at h
  have hnumE : numW R E = R.Knum + curveClass R.S R.hreg C₀.val + curveClass R.S R.hreg C₁.val +
      curveClass R.S R.hreg C₂.val + (2 : ℚ) • curveClass R.S R.hreg P := by
    rw [numW_eq_of_linearlyEquivalent R hclass, map_add, numW_KS, numW_cubDiv]
    simp only [Int.cast_one, one_smul, add_assoc]
    push_cast
    rfl
  -- nullity for the rulings
  have hEnullF : ∀ Q : R.S.PrimeCurve, E Q ≠ 0 → degW R Q (cubDiv R P C₀ C₁ C₂ 1 1 0 2) = 0 ∧
      degW R Q (cubDiv R P C₀ C₁ C₂ 1 0 1 2) = 0 := by
    intro Q hQ
    obtain ⟨e0, e1, e2, eP⟩ := hEinter Q hQ
    rw [degW_cubDiv, degW_cubDiv, e0, e1, e2, eP]
    norm_num
  -- `E · A = 0`
  have hAE : R.S.numericalIntersectionBilinForm R.hreg (numW R A) (numW R E) = 0 := by
    rw [pairing_numW_eq_sum]
    exact Finset.sum_eq_zero (fun Q hQ => by
      rw [hEnullA Q (Finsupp.mem_support_iff.mp hQ), mul_zero])
  refine ⟨E, hEeff, ?_, hclass, hE0, hE1, hE2, hEP, hEnullA, fun Q hQ => (hEnullF Q hQ).1,
    fun Q hQ => (hEnullF Q hQ).2, hEinter, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hZdecomp]
    exact R.S.linearlyEquivalent_symm hlin
  · intro Q hQ
    obtain ⟨e0, e1, e2, eP⟩ := hEinter Q hQ
    obtain ⟨hQ0, hQ1, hQ2, hQP, -⟩ := hEne Q hQ
    exact ⟨disjoint_of_inter_eq_zero R Q C₀.val hQ0 e0, disjoint_of_inter_eq_zero R Q C₁.val hQ1 e1,
      disjoint_of_inter_eq_zero R Q C₂.val hQ2 e2, disjoint_of_inter_eq_zero R Q P hQP eP⟩
  · rw [LdegW_eq_pairing, hnumE]
    simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right,
      Lnum_pairing_curveClass, R.Ldeg_exceptional]
    have hsymm : R.S.numericalIntersectionBilinForm R.hreg R.Lnum R.Knum =
        R.S.numericalIntersectionBilinForm R.hreg R.Knum R.Lnum :=
      LinearMap.BilinForm.IsSymm.eq (R.S.numericalIntersectionBilinForm_isSymm R.hreg) _ _
    rw [hsymm, R.Knum_pairing_Lnum]
    ring
  · intro Q hQ hQext
    exact exteriorNullCurve_isMinusOne R (numW R A) hnefA hsq Q hQext (hEnullA Q hQ)
  · intro Q hQext hQP hF₁ hF₂
    have hQ0 := exterior_ne_vertex R Q hQext C₀
    have hQ1 := exterior_ne_vertex R Q hQext C₁
    have hQ2 := exterior_ne_vertex R Q hQext C₂
    obtain ⟨e0, e1, e2, eP⟩ := null_rulings_inter_eq_zero R P C₀ C₁ C₂ Q hQ0 hQ1 hQ2 hQP hF₁ hF₂
    have hQA : degW R Q A = 0 := by
      rw [hAdef, degW_cubDiv, e0, e1, e2, eP]; norm_num
    have hminus := exteriorNullCurve_isMinusOne R (numW R A) hnefA hsq Q hQext hQA
    refine ⟨hminus.1, ?_⟩
    have hdeg : degW R Q E = -1 := by
      rw [degW, hnumE, map_add, map_add, map_add, map_add, map_smul,
        KltDP.Manuscript.S03.numericalRestrictionDegree_Knum, hminus.2,
        numericalRestrictionDegree_curveClass, numericalRestrictionDegree_curveClass,
        numericalRestrictionDegree_curveClass, numericalRestrictionDegree_curveClass, e0, e1, e2, eP]
      simp only [smul_eq_mul]
      push_cast
      ring
    by_contra hle
    push_neg at hle
    have hQ0' : E Q = 0 := le_antisymm hle (hEeff Q)
    have := degW_nonneg_of_coeff_eq_zero R Q E hEeff hQ0'
    linarith
  · intro E' hE' hlin'
    have heq : numW R E' = numW R E := numW_eq_of_linearlyEquivalent R hlin'
    have hAE' : R.S.numericalIntersectionBilinForm R.hreg (numW R A) (numW R E') = 0 := by
      rw [heq, hAE]
    have hnull' := degW_eq_zero_of_component R A E' hnefA hE' hAE'
    exact eq_of_effective_of_null R (numW R A) hsq E' E hE' hEeff (fun Q hQ => hnull' Q hQ) heq

/-! ### The singular-point bound when `E = 0` (manuscript lines 1873–1878) -/

include hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2 in
/-- If `-K_S ∼ C₀ + C₁ + C₂ + 2P` then `K_S² = 2`, `#Irr(D) = 7` and `#Sing(X) ≤ 7`. -/
theorem singularPoints_le_seven_of_cubic_zero (p : ℕ) [CharP k p] (hp : 0 < p)
    (hclass : R.S.LinearlyEquivalent 0 (R.S.cartierToWeilHom R.KS + cubDiv R P C₀ C₁ C₂ 1 1 1 2)) :
    R.X.singularPoints.card ≤ 7 := by
  classical
  have hK : R.Knum = -(curveClass R.S R.hreg C₀.val + curveClass R.S R.hreg C₁.val +
      curveClass R.S R.hreg C₂.val + (2 : ℚ) • curveClass R.S R.hreg P) := by
    have h := numW_eq_of_linearlyEquivalent R hclass
    rw [map_zero, map_add, numW_KS, numW_cubDiv] at h
    simp only [Int.cast_one, one_smul] at h
    push_cast at h
    have h' : R.Knum + (curveClass R.S R.hreg C₀.val + curveClass R.S R.hreg C₁.val +
        curveClass R.S R.hreg C₂.val + (2 : ℚ) • curveClass R.S R.hreg P) = 0 := by
      rw [← add_assoc, ← add_assoc, ← add_assoc]
      exact h.symm
    exact eq_neg_of_add_eq_zero_left h'
  have hcc : ∀ X Y : R.S.PrimeCurve, R.S.numericalIntersectionBilinForm R.hreg
      (curveClass R.S R.hreg X) (curveClass R.S R.hreg Y) =
      (X.intersectionNumber (R.S.primeCurveCartier R.hreg Y) : ℚ) :=
    fun X Y => curveClass_pairing_eq_intersectionNumber R X Y
  have i00 := inter_self R C₀
  have i11 := inter_self R C₁
  have i22 := inter_self R C₂
  have i01 := inter_of_not_adj R h01 hn01
  have i10 := inter_of_not_adj R h01.symm (fun h => hn01 h.symm)
  have i02 := inter_of_not_adj R h02 hn02
  have i20 := inter_of_not_adj R h02.symm (fun h => hn02 h.symm)
  have i12 := inter_of_not_adj R h12 hn12
  have i21 := inter_of_not_adj R h12.symm (fun h => hn12 h.symm)
  have iP0 := inter_contact R P C₀ hc0
  have iP1 := inter_contact R P C₁ hc1
  have iP2 := inter_contact R P C₂ hc2
  have i0P := inter_contact' R P C₀ hc0
  have i1P := inter_contact' R P C₁ hc1
  have i2P := inter_contact' R P C₂ hc2
  have iPP := inter_self_minusOne R P hP.1
  have hKsq : R.Ksq = 2 := by
    unfold ResolutionDatum.Ksq
    rw [hK]
    simp only [LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right,
      LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right, hcc, i00, i11, i22, i01, i10, i02, i20, i12, i21, iP0, iP1,
      iP2, i0P, i1P, i2P, iPP, hw0, hw1, hw2]
    norm_num
  have hN := R.hmin.noetherRelation_of_kltDelPezzo R.hDP R.hrank p hp R.KS R.eKS
  change R.S.intersectionPairing R.hreg R.KS R.KS + (R.S.picardRank : ℤ) = 10 at hN
  have hKsq' := R.Ksq_eq_intersectionPairing
  rw [hKsq] at hKsq'
  have hKint : R.S.intersectionPairing R.hreg R.KS R.KS = 2 := by exact_mod_cast hKsq'.symm
  have hρ := R.hmin.picardRank_eq_of_klt R.hklt p hp
  rw [R.hrank, Nat.card_eq_fintype_card] at hρ
  have hρ' : (R.S.picardRank : ℤ) = 1 + (Fintype.card R.Vertices : ℤ) := by exact_mod_cast hρ
  have hcardZ : (Fintype.card R.Vertices : ℤ) = 7 := by
    rw [hKint] at hN
    linarith
  have hcard : Fintype.card R.Vertices = 7 := by exact_mod_cast hcardZ
  obtain ⟨hfin, hcount, -, -⟩ := R.hmin.exceptional_forest_and_singular_count_from_klt R.hklt
  letI := hfin
  letI : Fintype (ActualExceptionalIncidence.graph R.π).ConnectedComponent := Fintype.ofFinite _
  rw [hcount, Nat.card_eq_fintype_card]
  have hsurj : Function.Surjective
      (fun v : R.Vertices => (ActualExceptionalIncidence.graph R.π).connectedComponentMk v) :=
    fun c => SimpleGraph.ConnectedComponent.ind (fun v => ⟨v, rfl⟩) c
  have hle := Fintype.card_le_of_surjective _ hsurj
  omega

/-- If `E` has no exterior component, it is supported on the exceptional locus, every component
`B` satisfies `E · B = K_S · B ≥ 0`, and negative definiteness forces `E = 0` (manuscript lines
1871–1873). -/
theorem cubicRemainder_eq_zero_of_no_exterior {E : R.S.WeilDivisor}
    (hE : CubicRemainder R P C₀ C₁ C₂ E)
    (hno : ∀ Q : R.S.PrimeCurve, E Q ≠ 0 → IsExceptionalCurve R.π Q) : E = 0 := by
  classical
  have hnumE : numW R E = R.Knum + curveClass R.S R.hreg C₀.val + curveClass R.S R.hreg C₁.val +
      curveClass R.S R.hreg C₂.val + (2 : ℚ) • curveClass R.S R.hreg P := by
    rw [numW_eq_of_linearlyEquivalent R hE.class_eq, map_add, numW_KS, numW_cubDiv]
    simp only [Int.cast_one, one_smul, add_assoc]
    push_cast
    rfl
  -- every component `B` of `E` has `E · B = K_S · B = b_B - 2 ≥ 0`
  have hdeg : ∀ Q : R.S.PrimeCurve, E Q ≠ 0 → 0 ≤ degW R Q E := by
    intro Q hQ
    obtain ⟨e0, e1, e2, eP⟩ := hE.inter_zero Q hQ
    have hex := hno Q hQ
    have hK : (R.Kdeg Q : ℚ) = R.w ⟨Q, hex⟩ - 2 := R.Kdeg_exceptional ⟨Q, hex⟩
    have h2 := R.two_le_w ⟨Q, hex⟩
    rw [degW, hnumE, map_add, map_add, map_add, map_add, map_smul,
      KltDP.Manuscript.S03.numericalRestrictionDegree_Knum,
      numericalRestrictionDegree_curveClass, numericalRestrictionDegree_curveClass,
      numericalRestrictionDegree_curveClass, numericalRestrictionDegree_curveClass, e0, e1, e2, eP,
      hK]
    simp only [smul_eq_mul, mul_zero, add_zero]
    linarith
  have hsq : 0 ≤ R.S.numericalIntersectionBilinForm R.hreg (numW R E) (numW R E) := by
    rw [pairing_numW_eq_sum]
    exact Finset.sum_nonneg (fun Q hQ => mul_nonneg (by exact_mod_cast hE.effective Q)
      (hdeg Q (Finsupp.mem_support_iff.mp hQ)))
  exact eq_zero_of_exceptional_of_square_nonneg R E hno hsq

include hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2 in
/-- **Proposition 6.5, last clause**: if `E = 0`, or if `E` has no exterior component (equivalently,
there is no exterior `Q ≠ P` null for both rulings), then `#Sing(X) ≤ 7`. -/
theorem singularPoints_le_seven_of_cubicRemainder (p : ℕ) [CharP k p] (hp : 0 < p)
    {E : R.S.WeilDivisor} (hE : CubicRemainder R P C₀ C₁ C₂ E)
    (h : E = 0 ∨ ∀ Q : R.S.PrimeCurve, E Q ≠ 0 → IsExceptionalCurve R.π Q) :
    R.X.singularPoints.card ≤ 7 := by
  have hE0 : E = 0 := by
    rcases h with h | h
    · exact h
    · exact cubicRemainder_eq_zero_of_no_exterior R P C₀ C₁ C₂ hE h
  have hclass := hE.class_eq
  rw [hE0] at hclass
  exact singularPoints_le_seven_of_cubic_zero R P C₀ C₁ C₂ hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2
    hc0 hc1 hc2 p hp hclass

/-- The numerical class of `E`. -/
theorem CubicRemainder.numW_eq {E : R.S.WeilDivisor} (hE : CubicRemainder R P C₀ C₁ C₂ E) :
    numW R E = R.Knum + curveClass R.S R.hreg C₀.val + curveClass R.S R.hreg C₁.val +
      curveClass R.S R.hreg C₂.val + (2 : ℚ) • curveClass R.S R.hreg P := by
  rw [numW_eq_of_linearlyEquivalent R hE.class_eq, map_add, numW_KS, numW_cubDiv]
  simp only [Int.cast_one, one_smul, add_assoc]
  push_cast
  rfl

/-- The degree of `E` on an arbitrary prime curve:
`E · Q = K_S · Q + Q·C₀ + Q·C₁ + Q·C₂ + 2 Q·P`. -/
theorem CubicRemainder.degW_eq {E : R.S.WeilDivisor} (hE : CubicRemainder R P C₀ C₁ C₂ E)
    (Q : R.S.PrimeCurve) :
    degW R Q E = (R.Kdeg Q : ℚ) +
      (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C₀.val) : ℚ) +
      (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C₁.val) : ℚ) +
      (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C₂.val) : ℚ) +
      2 * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) := by
  rw [degW, hE.numW_eq, map_add, map_add, map_add, map_add, map_smul,
    KltDP.Manuscript.S03.numericalRestrictionDegree_Knum, numericalRestrictionDegree_curveClass,
    numericalRestrictionDegree_curveClass, numericalRestrictionDegree_curveClass,
    numericalRestrictionDegree_curveClass, smul_eq_mul]

/-- `E · B = K_S · B` for every component `B` of `E`. -/
theorem CubicRemainder.degW_component {E : R.S.WeilDivisor} (hE : CubicRemainder R P C₀ C₁ C₂ E)
    (Q : R.S.PrimeCurve) (hQ : E Q ≠ 0) : degW R Q E = (R.Kdeg Q : ℚ) := by
  obtain ⟨e0, e1, e2, eP⟩ := hE.inter_zero Q hQ
  rw [hE.degW_eq, e0, e1, e2, eP]
  ring

/-- The Picard-group form of `E ∼ K_S + C₀ + C₁ + C₂ + 2P`. -/
theorem CubicRemainder.pic_eq {E : R.S.WeilDivisor} (hE : CubicRemainder R P C₀ C₁ C₂ E) :
    R.S.regularWeilPicardClass R.hreg E =
      cartierPicardClass R.S.toScheme R.KS * R.curvePic C₀.val * R.curvePic C₁.val *
        R.curvePic C₂.val * R.curvePic P ^ 2 := by
  rw [picW_eq_of_linearlyEquivalent R hE.class_eq]
  have e : Finsupp.single P (2 : ℤ) = Finsupp.single P 1 + Finsupp.single P 1 := by
    rw [← Finsupp.single_add]; norm_num
  simp only [cubDiv, e, R.S.regularWeilPicardClass_add, picW_KS, picW_single, mul_assoc, sq]

end Cubic

end KltDP.Manuscript.S06Adj

namespace KltDP.Manuscript.S06

/-! Re-exports of the headline results of `KltDP.Manuscript.S06Adj` into the manuscript's §6
namespace (the module lives in the sibling namespace `S06Adj` to avoid clashes with the
square-one modules of the same section). -/

alias cubicAdjoint := KltDP.Manuscript.S06Adj.cubicAdjoint
alias cubic_rulings := KltDP.Manuscript.S06Adj.cubic_rulings
alias singularPoints_le_seven_of_cubicRemainder := KltDP.Manuscript.S06Adj.singularPoints_le_seven_of_cubicRemainder
alias cubicRemainder_eq_zero_of_no_exterior := KltDP.Manuscript.S06Adj.cubicRemainder_eq_zero_of_no_exterior

end KltDP.Manuscript.S06

#print axioms KltDP.Manuscript.S06Adj.cubicAdjoint
#print axioms KltDP.Manuscript.S06Adj.cubic_rulings
#print axioms KltDP.Manuscript.S06Adj.singularPoints_le_seven_of_cubicRemainder
#print axioms KltDP.Manuscript.S06Adj.cubicRemainder_eq_zero_of_no_exterior

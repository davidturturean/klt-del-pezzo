import KltDP.Manuscript.S07.ForestCount
import KltDP.Manuscript.S03.NefThreshold
import KltDP.Manuscript.S02.ExteriorNullCurves

/-!
# Manuscript Lemma 7.3: fibres of least possible anticanonical degree

Source: `source/manuscript.tex`, lines 2138–2196, `lem:fiber-degree-equality`.

Setting: the resolution datum `R`, a shortest exterior `(-1)`-curve `P` with `ℓ = L · P`
(`hP : R.IsShortestExteriorMinusOne P`, `hrho : 2 < ρ(S)`), a nef Cartier divisor `F` with
`F² = 0`, `K_S · F = -2`, the ruling `g` of Lemma 3.1 and its fibre divisors `E_t`
(`IsFiberDivisor F g t E`, multiplicities `μ_C = (cartierToWeilHom E) C`), and the hypothesis
`L · F = 2ℓ` (`hL`, as a numerical pairing).

For every reducible fibre:

* `exterior_component_isMinusOne`: every exterior component is a `(-1)`-curve with `K_S · R = -1`
  (fibre intersection equation and adjunction);
* `fiber_degree_equalities`: `Σ_{R ⊄ D} μ_R = 2`, `L · R = ℓ` for every exterior component, and
  `K_S · C = 0`, `w_C = 2`, `C² = -2` for every retained (exceptional) vertical component;
* `exterior_pattern`: the exterior multiplicity pattern is `(2)` (one exterior component of
  multiplicity two) or `(1, 1)` (two exterior components of multiplicity one);
* `numExterior_eq_one_or_two`: the number `o_t` of exterior components is `1` or `2`.

The count (`card_twoExteriorFibres_le`): with `s` horizontal exceptional curves, the number of
reducible fibres with pattern `(1, 1)` is at most `s - 1`. This uses only the lower bound
`2 + Σ_t (n_t - 1) ≤ ρ(S)` of Lemma 3.2 (`rulingFibers_picardRank_lower_bound`) and
`ρ(S) - 1 = #Irr(D) = s + Σ_t (n_t - o_t)`; the manuscript's equality `ρ(S) = 2 + Σ_t (n_t - 1)`
is not needed (it would give equality in the count).

The chain structure of pattern `(1, 1)` and the two-piece bound of pattern `(2)` are in the
second half of this file (`pattern_two_numPieces_le_two`, `pattern_one_one_chain`).
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Finset
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Manuscript KltDP.Manuscript.S03

universe u

namespace KltDP.Manuscript.S07

variable {k : Type u} [Field k] [IsAlgClosed k] {R : ResolutionDatum k}
  (p : ℕ) [CharP k p] (hp : 0 < p)
  (F : CartierDivisor R.S.toScheme)
  (hFF : R.S.intersectionPairing R.hreg F F = 0)
  (hKF : R.S.intersectionPairing R.hreg R.KS F = -2)
  (g : R.S.toScheme ⟶ projectiveSpace k 1)
  (hg : g ≫ projectiveSpaceToSpec k 1 = R.S.structureMorphism)
  (e : (pullbackInvertibleSheaf g (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
    cartierDivisorModule R.S.toScheme F)

/-! ### Exceptional curves: self-intersection and weight -/

/-- `D_i² = -w_i` for an exceptional curve. -/
theorem selfIntersection_eq_neg_w (i : R.Vertices) :
    ((i.val.selfIntersectionNumber R.hreg : ℤ) : ℚ) = -R.w i := by
  change _ = -(-(R.S.intersectionPairing R.hreg
    (R.S.primeCurveCartier R.hreg i.val) (R.S.primeCurveCartier R.hreg i.val) : ℚ))
  rw [R.S.intersectionPairing_primeCurve R.hreg, neg_neg]
  rfl

/-- `K_S · D_i = w_i - 2 ≥ 0` for an exceptional curve. -/
theorem Kdeg_exceptional_nonneg (i : R.Vertices) : 0 ≤ R.Kdeg i.val := by
  have h := R.Kdeg_exceptional i
  have h2 := R.two_le_w i
  have h' : (0 : ℚ) ≤ (R.Kdeg i.val : ℚ) := by
    rw [h]
    show (0 : ℚ) ≤ R.w i - 2
    linarith
  exact_mod_cast h'

/-- An exceptional curve with `K_S · D_i = 0` has `w_i = 2` and `D_i² = -2`. -/
theorem w_eq_two_of_Kdeg_eq_zero (i : R.Vertices) (h : R.Kdeg i.val = 0) :
    R.w i = 2 ∧ i.val.selfIntersectionNumber R.hreg = -2 := by
  have h1 := R.Kdeg_exceptional i
  rw [h, Int.cast_zero] at h1
  have hw : R.w i = 2 := by
    have : (0 : ℚ) = R.w i - 2 := h1
    linarith
  refine ⟨hw, ?_⟩
  have h2 := selfIntersection_eq_neg_w i
  rw [hw] at h2
  exact_mod_cast h2

/-! ### The `L`-degree of a fibre divisor -/

/-- `L · F = Σ_C μ_C (L · C)` for a fibre divisor `E` of class `F` (via the ample numerator
`π^*A = n L`). -/
theorem Lnum_pairing_fiberDivisor {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme}
    (hE : IsFiberDivisor F g t E) :
    R.S.numericalIntersectionBilinForm R.hreg R.Lnum (NefNullCurveNegativeSquare.cartierClass R.S F)
      = (R.S.cartierToWeilHom E).sum fun C a => (a : ℚ) * R.Ldeg C := by
  obtain ⟨n, hn, A, -, hLw⟩ := R.exists_ample_numerator
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hclass := cartierClass_pullback_eq R n A hLw hn
  have hdeg := Ldeg_mul_eq_intersectionNumber R n A hLw hn
  have hpair : (n : ℚ) * R.S.numericalIntersectionBilinForm R.hreg R.Lnum
      (NefNullCurveNegativeSquare.cartierClass R.S F)
      = (((R.S.cartierToWeilHom E).sum fun C a =>
          a * C.intersectionNumber (DominantCartierPullback.pullbackHom R.π A) : ℤ) : ℚ) := by
    rw [← LinearMap.BilinForm.smul_left, ← hclass,
      NefNullCurveNegativeSquare.cartierClass_pairing,
      R.S.intersectionPairing_eq_of_class_eq_right R.hreg _ F E hE.class_eq.symm,
      R.S.intersectionPairing_symm R.hreg, R.S.intersectionPairing_eq_weil_sum_right R.hreg]
  have hsum : (n : ℚ) * ((R.S.cartierToWeilHom E).sum fun C a => (a : ℚ) * R.Ldeg C)
      = (((R.S.cartierToWeilHom E).sum fun C a =>
          a * C.intersectionNumber (DominantCartierPullback.pullbackHom R.π A) : ℤ) : ℚ) := by
    unfold Finsupp.sum
    rw [Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [← hdeg C]
    ring
  exact mul_left_cancel₀ hn'.ne' (hpair.trans hsum.symm)

/-! ### Reducible fibres: exterior components are `(-1)`-curves -/

include hp hFF hKF hg e in
/-- Manuscript Lemma 7.3, first sentence of the proof (lines 2163–2165): every exterior component
of a reducible fibre is a smooth rational `(-1)`-curve with `K_S · R = -1`. -/
theorem exterior_component_isMinusOne [IsProper g] [Surjective g]
    {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E)
    (hred : ∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C')
    (C : R.S.PrimeCurve) (hC : InFiber g t C) (hCex : ¬ IsExceptionalCurve R.π C) :
    IsMinusOneCurve R.hreg C ∧ R.Kdeg C = -1 := by
  obtain ⟨C₁, C₂, h₁, h₂, hne⟩ := hred
  have hconn := fiber_isConnected R p hp F hFF hKF g hg e t
  have hneg : C.intersectionNumber R.KS < 0 := KltDP.Manuscript.S02.Kdeg_neg_of_not_exceptional R C hCex
  by_cases h : C₁ = C
  · subst h
    exact isMinusOneCurve_of_reducible_of_negative_canonical R F hFF hKF g hg e hE hconn C₁ hC
      C₂ h₂ (Ne.symm hne) hneg
  · exact isMinusOneCurve_of_reducible_of_negative_canonical R F hFF hKF g hg e hE hconn C hC
      C₁ h₁ h hneg

/-! ### The multiplicity and degree equalities -/

section Equalities

variable (hrho : 2 < R.S.picardRank) (P : R.S.PrimeCurve) (hP : R.IsShortestExteriorMinusOne P)
  (hL : R.S.numericalIntersectionBilinForm R.hreg R.Lnum
    (NefNullCurveNegativeSquare.cartierClass R.S F) = 2 * R.Ldeg P)

open Classical in
/-- The exterior components of the fibre divisor `E`, as a finset. -/
def exteriorSupport (E : CartierDivisor R.S.toScheme) : Finset R.S.PrimeCurve :=
  (R.S.cartierToWeilHom E).support.filter fun C => ¬ IsExceptionalCurve R.π C

theorem mem_exteriorSupport {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme}
    (hE : IsFiberDivisor F g t E) (C : R.S.PrimeCurve) :
    C ∈ exteriorSupport E ↔ InFiber g t C ∧ ¬ IsExceptionalCurve R.π C := by
  classical
  unfold exteriorSupport
  rw [Finset.mem_filter, ← inFiber_iff_mem_support R F g hE C]

include hp hFF hKF hg e hrho hP hL in
/-- **Manuscript Lemma 7.3, the equalities** (lines 2145–2151 and 2166–2175). In every reducible
fibre: `Σ_{R ⊄ D} μ_R = 2`; every exterior component `R` has `L · R = ℓ`; every retained vertical
component `C` has `K_S · C = 0`. -/
theorem fiber_degree_equalities [IsProper g] [Surjective g]
    {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E)
    (hred : ∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C') :
    (∑ C ∈ exteriorSupport E, R.S.cartierToWeilHom E C) = 2 ∧
      (∀ C : R.S.PrimeCurve, InFiber g t C → ¬ IsExceptionalCurve R.π C → R.Ldeg C = R.Ldeg P) ∧
      (∀ C : R.S.PrimeCurve, InFiber g t C → IsExceptionalCurve R.π C → R.Kdeg C = 0) := by
  classical
  set μ := R.S.cartierToWeilHom E with hμ
  have hℓ : 0 < R.Ldeg P := KltDP.Manuscript.S02.Ldeg_pos R P hP.1.2
  -- positivity of multiplicities
  have hμpos : ∀ C ∈ μ.support, (0 : ℚ) < μ C := fun C hC => by
    exact_mod_cast coeff_pos_of_inFiber R F g hE C ((inFiber_iff_mem_support R F g hE C).mpr hC)
  -- the canonical sum, split into exterior and exceptional components
  have hK : (∑ C ∈ μ.support, (μ C : ℚ) * (R.Kdeg C : ℚ)) = -2 := by
    have h := fiber_canonical_sum R F hKF g hE
    unfold Finsupp.sum at h
    have h' := congrArg (Int.cast (R := ℚ)) h
    push_cast at h'
    exact h'
  have hLs : (∑ C ∈ μ.support, (μ C : ℚ) * R.Ldeg C) = 2 * R.Ldeg P := by
    rw [← hL, Lnum_pairing_fiberDivisor F g hE]
    rfl
  have hsplitK := Finset.sum_filter_add_sum_filter_not μ.support
    (fun C => ¬ IsExceptionalCurve R.π C) (fun C => (μ C : ℚ) * (R.Kdeg C : ℚ))
  have hsplitL := Finset.sum_filter_add_sum_filter_not μ.support
    (fun C => ¬ IsExceptionalCurve R.π C) (fun C => (μ C : ℚ) * R.Ldeg C)
  simp only [not_not] at hsplitK hsplitL
  -- exterior components: `K_S · R = -1`, `L · R ≥ ℓ`
  have hKext : ∀ C ∈ exteriorSupport E, (R.Kdeg C : ℚ) = -1 := by
    intro C hC
    rw [mem_exteriorSupport F g hE] at hC
    have := (exterior_component_isMinusOne p hp F hFF hKF g hg e hE hred C hC.1 hC.2).2
    exact_mod_cast this
  have hLext : ∀ C ∈ exteriorSupport E, R.Ldeg P ≤ R.Ldeg C := by
    intro C hC
    rw [mem_exteriorSupport F g hE] at hC
    exact Ldeg_ge_of_not_exceptional R hrho P hP C hC.2
  -- exceptional components: `L · C = 0`, `K_S · C ≥ 0`
  have hLexc : ∀ C ∈ μ.support.filter (fun C => IsExceptionalCurve R.π C), R.Ldeg C = 0 := by
    intro C hC
    rw [Finset.mem_filter] at hC
    exact R.Ldeg_exceptional ⟨C, hC.2⟩
  have hKexc : ∀ C ∈ μ.support.filter (fun C => IsExceptionalCurve R.π C),
      (0 : ℚ) ≤ (R.Kdeg C : ℚ) := by
    intro C hC
    rw [Finset.mem_filter] at hC
    exact_mod_cast Kdeg_exceptional_nonneg ⟨C, hC.2⟩
  -- the sums
  have hSK : (∑ C ∈ exteriorSupport E, (μ C : ℚ) * (R.Kdeg C : ℚ))
      = -∑ C ∈ exteriorSupport E, (μ C : ℚ) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun C hC => by rw [hKext C hC]; ring
  have hSKexc : 0 ≤ ∑ C ∈ μ.support.filter (fun C => IsExceptionalCurve R.π C),
      (μ C : ℚ) * (R.Kdeg C : ℚ) :=
    Finset.sum_nonneg fun C hC =>
      mul_nonneg (hμpos C (Finset.mem_filter.mp hC).1).le (hKexc C hC)
  have hSLexc : (∑ C ∈ μ.support.filter (fun C => IsExceptionalCurve R.π C),
      (μ C : ℚ) * R.Ldeg C) = 0 :=
    Finset.sum_eq_zero fun C hC => by rw [hLexc C hC, mul_zero]
  have hSLext : (∑ C ∈ exteriorSupport E, (μ C : ℚ) * R.Ldeg P)
      ≤ ∑ C ∈ exteriorSupport E, (μ C : ℚ) * R.Ldeg C :=
    Finset.sum_le_sum fun C hC =>
      mul_le_mul_of_nonneg_left (hLext C hC) (hμpos C (Finset.mem_filter.mp hC).1).le
  rw [← Finset.sum_mul] at hSLext
  -- `Σ μ_R ≥ 2` and `Σ μ_R ≤ 2`
  have hext_eq : exteriorSupport E = μ.support.filter (fun C => ¬ IsExceptionalCurve R.π C) := rfl
  rw [← hext_eq] at hsplitK hsplitL
  have hge : 2 ≤ ∑ C ∈ exteriorSupport E, (μ C : ℚ) := by linarith
  have hle : ∑ C ∈ exteriorSupport E, (μ C : ℚ) ≤ 2 := by
    have : (∑ C ∈ exteriorSupport E, (μ C : ℚ)) * R.Ldeg P ≤ 2 * R.Ldeg P := by linarith
    exact le_of_mul_le_mul_right this hℓ
  have hsum2 : ∑ C ∈ exteriorSupport E, (μ C : ℚ) = 2 := le_antisymm hle hge
  refine ⟨by exact_mod_cast hsum2, ?_, ?_⟩
  · -- `L · R = ℓ` for exterior components: the slack `Σ μ_R (L·R − ℓ)` vanishes
    intro C hC hCex
    have hmem : C ∈ exteriorSupport E := (mem_exteriorSupport F g hE C).mpr ⟨hC, hCex⟩
    have hslack : ∑ C ∈ exteriorSupport E, (μ C : ℚ) * (R.Ldeg C - R.Ldeg P) = 0 := by
      have h1 : ∑ C ∈ exteriorSupport E, (μ C : ℚ) * (R.Ldeg C - R.Ldeg P)
          = ∑ C ∈ exteriorSupport E, (μ C : ℚ) * R.Ldeg C
            - (∑ C ∈ exteriorSupport E, (μ C : ℚ)) * R.Ldeg P := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun C _ => by ring
      rw [h1, hsum2]
      linarith
    have hnn : ∀ C ∈ exteriorSupport E, 0 ≤ (μ C : ℚ) * (R.Ldeg C - R.Ldeg P) := fun C hC =>
      mul_nonneg (hμpos C (Finset.mem_filter.mp hC).1).le (sub_nonneg.mpr (hLext C hC))
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hslack C hmem
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (hμpos C (Finset.mem_filter.mp hmem).1).ne'
    · linarith
  · -- `K_S · C = 0` for retained components: the nonnegative sum `Σ μ_C (K_S·C)` vanishes
    intro C hC hCex
    have hmem : C ∈ μ.support.filter (fun C => IsExceptionalCurve R.π C) :=
      Finset.mem_filter.mpr ⟨(inFiber_iff_mem_support R F g hE C).mp hC, hCex⟩
    have hzero : ∑ C ∈ μ.support.filter (fun C => IsExceptionalCurve R.π C),
        (μ C : ℚ) * (R.Kdeg C : ℚ) = 0 := by linarith
    have hnn : ∀ C ∈ μ.support.filter (fun C => IsExceptionalCurve R.π C),
        0 ≤ (μ C : ℚ) * (R.Kdeg C : ℚ) := fun C hC =>
      mul_nonneg (hμpos C (Finset.mem_filter.mp hC).1).le (hKexc C hC)
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero C hmem
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (hμpos C (Finset.mem_filter.mp hmem).1).ne'
    · exact_mod_cast h

include hp hFF hKF hg e hrho hP hL in
/-- Manuscript Lemma 7.3: every retained vertical component `C ⊂ D` of a reducible fibre has
weight two, `C² = -2`. -/
theorem vertical_exceptional_w_eq_two [IsProper g] [Surjective g]
    {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E)
    (hred : ∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C')
    (i : R.Vertices) (hi : InFiber g t i.val) :
    R.w i = 2 ∧ i.val.selfIntersectionNumber R.hreg = -2 :=
  w_eq_two_of_Kdeg_eq_zero i
    ((fiber_degree_equalities p hp F hFF hKF g hg e hrho P hP hL hE hred).2.2 i.val hi i.property)

include hp hFF hKF hg e hrho hP hL in
/-- **Manuscript Lemma 7.3, the pattern** (line 2152): the exterior multiplicity pattern of a
reducible fibre is `(2)` (a unique exterior component, of multiplicity two) or `(1, 1)` (exactly
two exterior components, both of multiplicity one). -/
theorem exterior_pattern [IsProper g] [Surjective g]
    {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E)
    (hred : ∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C') :
    (∃ R₀ : R.S.PrimeCurve, InFiber g t R₀ ∧ ¬ IsExceptionalCurve R.π R₀ ∧
        R.S.cartierToWeilHom E R₀ = 2 ∧
        ∀ C, InFiber g t C → ¬ IsExceptionalCurve R.π C → C = R₀) ∨
      (∃ R₁ R₂ : R.S.PrimeCurve, R₁ ≠ R₂ ∧ InFiber g t R₁ ∧ InFiber g t R₂ ∧
        ¬ IsExceptionalCurve R.π R₁ ∧ ¬ IsExceptionalCurve R.π R₂ ∧
        R.S.cartierToWeilHom E R₁ = 1 ∧ R.S.cartierToWeilHom E R₂ = 1 ∧
        ∀ C, InFiber g t C → ¬ IsExceptionalCurve R.π C → C = R₁ ∨ C = R₂) := by
  classical
  have hsum := (fiber_degree_equalities p hp F hFF hKF g hg e hrho P hP hL hE hred).1
  have hone : ∀ C ∈ exteriorSupport E, 1 ≤ R.S.cartierToWeilHom E C := fun C hC =>
    coeff_pos_of_inFiber R F g hE C ((mem_exteriorSupport F g hE C).mp hC).1
  have hcard : (exteriorSupport E).card ≤ 2 := by
    have h : ((exteriorSupport E).card : ℤ) ≤ ∑ C ∈ exteriorSupport E, R.S.cartierToWeilHom E C := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      exact Finset.sum_le_sum fun C hC => by exact_mod_cast hone C hC
    rw [hsum] at h
    exact_mod_cast h
  have hne : (exteriorSupport E).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at hsum
    exact absurd hsum (by norm_num)
  have hcard1 : 1 ≤ (exteriorSupport E).card := Finset.card_pos.mpr hne
  rcases (by omega : (exteriorSupport E).card = 1 ∨ (exteriorSupport E).card = 2) with h1 | h2
  · left
    obtain ⟨R₀, hR₀⟩ := Finset.card_eq_one.mp h1
    have hmem : R₀ ∈ exteriorSupport E := by rw [hR₀]; exact Finset.mem_singleton_self R₀
    rw [hR₀, Finset.sum_singleton] at hsum
    obtain ⟨hin, hex⟩ := (mem_exteriorSupport F g hE R₀).mp hmem
    refine ⟨R₀, hin, hex, hsum, fun C hC hCex => ?_⟩
    have : C ∈ exteriorSupport E := (mem_exteriorSupport F g hE C).mpr ⟨hC, hCex⟩
    rw [hR₀, Finset.mem_singleton] at this
    exact this
  · right
    obtain ⟨R₁, R₂, hne12, hR⟩ := Finset.card_eq_two.mp h2
    have hmem1 : R₁ ∈ exteriorSupport E := by rw [hR]; exact Finset.mem_insert_self _ _
    have hmem2 : R₂ ∈ exteriorSupport E := by
      rw [hR]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rw [hR, Finset.sum_pair hne12] at hsum
    have h1 := hone R₁ hmem1
    have h2 := hone R₂ hmem2
    obtain ⟨hin1, hex1⟩ := (mem_exteriorSupport F g hE R₁).mp hmem1
    obtain ⟨hin2, hex2⟩ := (mem_exteriorSupport F g hE R₂).mp hmem2
    refine ⟨R₁, R₂, hne12, hin1, hin2, hex1, hex2, by omega, by omega, fun C hC hCex => ?_⟩
    have : C ∈ exteriorSupport E := (mem_exteriorSupport F g hE C).mpr ⟨hC, hCex⟩
    rw [hR, Finset.mem_insert, Finset.mem_singleton] at this
    exact this

/-! ### The count of fibres with pattern `(1, 1)` -/

/-- `o_t`: the number of exterior components of the fibre over `t`. -/
def numExterior (t : projectiveSpace k 1) : ℕ :=
  Nat.card {C : R.S.PrimeCurve // InFiber g t C ∧ ¬ IsExceptionalCurve R.π C}

/-- `n_t`: the number of components of the fibre over `t`. -/
def numComponents (t : projectiveSpace k 1) : ℕ := Nat.card {C : R.S.PrimeCurve // InFiber g t C}

/-- `n_t - o_t`: the number of retained (exceptional) components of the fibre over `t`. -/
def numVertical (t : projectiveSpace k 1) : ℕ := Nat.card {i : R.Vertices // InFiber g t i.val}

theorem numExterior_eq_card {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme}
    (hE : IsFiberDivisor F g t E) : numExterior g t = (exteriorSupport E).card := by
  rw [numExterior, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun C => (mem_exteriorSupport F g hE C).symm)

/-- The fibre components are finite (they are the support of the fibre divisor). -/
theorem finite_inFiber_of_isFiberDivisor {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme}
    (hE : IsFiberDivisor F g t E) : Finite {C : R.S.PrimeCurve // InFiber g t C} :=
  Finite.of_injective
    (fun C : {C : R.S.PrimeCurve // InFiber g t C} =>
      (⟨C.1, (inFiber_iff_mem_support R F g hE C.1).mp C.2⟩ :
        {C : R.S.PrimeCurve // C ∈ (R.S.cartierToWeilHom E).support}))
    fun _ _ h => Subtype.ext (Subtype.mk.inj h)

/-- `n_t = o_t + (n_t - o_t)`: the components split into exterior and exceptional ones. -/
theorem numComponents_eq {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme}
    (hE : IsFiberDivisor F g t E) : numComponents g t = numExterior g t + numVertical g t := by
  classical
  haveI := finite_inFiber_of_isFiberDivisor F g hE
  unfold numComponents numExterior numVertical
  have e1 : {C : R.S.PrimeCurve // InFiber g t C} ≃
      {x : {C : R.S.PrimeCurve // InFiber g t C} // ¬ IsExceptionalCurve R.π x.1} ⊕
      {x : {C : R.S.PrimeCurve // InFiber g t C} // ¬ ¬ IsExceptionalCurve R.π x.1} :=
    (Equiv.sumCompl fun x : {C : R.S.PrimeCurve // InFiber g t C} =>
      ¬ IsExceptionalCurve R.π x.1).symm
  have e2 : {x : {C : R.S.PrimeCurve // InFiber g t C} // ¬ IsExceptionalCurve R.π x.1} ≃
      {C : R.S.PrimeCurve // InFiber g t C ∧ ¬ IsExceptionalCurve R.π C} :=
    Equiv.subtypeSubtypeEquivSubtypeInter (fun C : R.S.PrimeCurve => InFiber g t C)
      (fun C => ¬ IsExceptionalCurve R.π C)
  have e3 : {x : {C : R.S.PrimeCurve // InFiber g t C} // ¬ ¬ IsExceptionalCurve R.π x.1} ≃
      {i : R.Vertices // InFiber g t i.val} :=
    (Equiv.subtypeEquivRight fun x => not_not).trans
      ((Equiv.subtypeSubtypeEquivSubtypeInter (fun C : R.S.PrimeCurve => InFiber g t C)
        (fun C => IsExceptionalCurve R.π C)).trans
      ((Equiv.subtypeEquivRight fun C => and_comm).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter (fun C : R.S.PrimeCurve => IsExceptionalCurve R.π C)
          (fun C => InFiber g t C)).symm))
  rw [Nat.card_congr e1, Nat.card_sum, Nat.card_congr e2, Nat.card_congr e3]

include hp hFF hKF hg e hrho hP hL in
/-- `o_t ∈ {1, 2}` for a reducible fibre. -/
theorem numExterior_eq_one_or_two [IsProper g] [Surjective g]
    {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E)
    (hred : ∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C') :
    numExterior g t = 1 ∨ numExterior g t = 2 := by
  classical
  rw [numExterior_eq_card F g hE]
  rcases exterior_pattern p hp F hFF hKF g hg e hrho P hP hL hE hred with
    ⟨R₀, hin, hex, -, huniq⟩ | ⟨R₁, R₂, hne, hin1, hin2, hex1, hex2, -, -, huniq⟩
  · left
    rw [Finset.card_eq_one]
    refine ⟨R₀, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun C hC => ?_⟩⟩
    · exact (mem_exteriorSupport F g hE R₀).mpr ⟨hin, hex⟩
    · obtain ⟨hC1, hC2⟩ := (mem_exteriorSupport F g hE C).mp hC
      exact huniq C hC1 hC2
  · right
    rw [Finset.card_eq_two]
    refine ⟨R₁, R₂, hne, ?_⟩
    ext C
    rw [mem_exteriorSupport F g hE, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hC1, hC2⟩
      exact huniq C hC1 hC2
    · rintro (rfl | rfl)
      · exact ⟨hin1, hex1⟩
      · exact ⟨hin2, hex2⟩

/-- `#Irr(D) = s + Σ_{t ∈ T} (n_t - o_t)` for `T` containing every fibre with a vertical
exceptional curve. -/
theorem card_vertices_eq (T : Finset (projectiveSpace k 1))
    (hT : ∀ (i : R.Vertices) (t : projectiveSpace k 1), InFiber g t i.val → t ∈ T) :
    Nat.card R.Vertices = numHorizontal g + ∑ t ∈ T, numVertical g t := by
  classical
  rw [Nat.card_eq_fintype_card, card_eq_hor_add_vert (fiberIndex g T)]
  congr 1
  · unfold numHorizontal
    congr 1
    ext i
    simp only [horFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fiberIndex_eq_none_iff g T hT i
  · rw [← Finset.sum_coe_sort T]
    refine Finset.sum_congr rfl fun t _ => ?_
    unfold numVertical
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext i
    simp only [vertFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fiberIndex_eq_some_iff g T i t

include hp hFF hKF hg e hrho hP hL in
/-- **Manuscript Lemma 7.3, the count** (lines 2153–2155 and 2189–2196): for a finite set `T` of
closed points with reducible fibres containing every fibre with a vertical exceptional curve, the
number of `t ∈ T` with two exterior components is at most `s - 1`, `s` the number of horizontal
exceptional curves. (The manuscript states equality, using `ρ(S) = 2 + Σ_t (n_t - 1)`; the lower
bound `2 + Σ_t (n_t - 1) ≤ ρ(S)` gives the inequality, which is what Theorem 7.5 uses.) -/
theorem card_twoExteriorFibres_le [IsProper g] [Surjective g]
    (T : Finset (projectiveSpace k 1))
    (hTcl : ∀ t ∈ T, IsClosed ({t} : Set (projectiveSpace k 1)))
    (hTred : ∀ t ∈ T, ∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C')
    (hTall : ∀ (i : R.Vertices) (t : projectiveSpace k 1), InFiber g t i.val → t ∈ T) :
    (T.filter fun t => numExterior g t = 2).card + 1 ≤ numHorizontal g := by
  classical
  -- the lower bound of Lemma 3.2
  have hlow := rulingFibers_picardRank_lower_bound R p hp F hFF hKF g hg e T hTcl
  -- `ρ(S) = #Irr(D) + 1`
  have hrank : R.S.picardRank = Nat.card R.Vertices + 1 := by
    have h := R.hmin.picardRank_eq_of_klt R.hklt p hp
    rw [R.hrank] at h
    change R.S.picardRank = 1 + Nat.card R.Vertices at h
    omega
  have hvert := card_vertices_eq g T hTall
  -- fibrewise: `n_t = o_t + e_t` with `o_t ∈ {1, 2}`
  have hfib : ∀ t ∈ T, numComponents g t = numExterior g t + numVertical g t ∧
      (numExterior g t = 1 ∨ numExterior g t = 2) := by
    intro t ht
    obtain ⟨E, hE⟩ := exists_isFiberDivisor R F g e t (hTcl t ht)
    exact ⟨numComponents_eq F g hE,
      numExterior_eq_one_or_two p hp F hFF hKF g hg e hrho P hP hL hE (hTred t ht)⟩
  have hsum : ∑ t ∈ T, (Nat.card {C : R.S.PrimeCurve // InFiber g t C} - 1)
      = ∑ t ∈ T, (if numExterior g t = 2 then 1 else 0) + ∑ t ∈ T, numVertical g t := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t ht => ?_
    obtain ⟨h1, h2⟩ := hfib t ht
    change numComponents g t - 1 = _
    rw [h1]
    rcases h2 with h | h <;> rw [h] <;> split_ifs <;> omega
  rw [hsum, ← Finset.card_filter] at hlow
  omega

end Equalities

/-! ### Intersection numbers of fibre components -/

section Inter

/-- `C · C'` is symmetric. -/
theorem inter_symm (C C' : R.S.PrimeCurve) :
    C.intersectionNumber (R.S.primeCurveCartier R.hreg C') =
      C'.intersectionNumber (R.S.primeCurveCartier R.hreg C) := by
  rw [← PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber R.S R.hreg,
    ← PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber R.S R.hreg,
    R.S.intersectionPairing_symm R.hreg]

/-- Distinct prime curves have nonnegative intersection number. -/
theorem inter_nonneg {C C' : R.S.PrimeCurve} (hne : C ≠ C') :
    0 ≤ C.intersectionNumber (R.S.primeCurveCartier R.hreg C') := by
  rw [← PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber R.S R.hreg]
  exact PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg R.S R.hreg C C' hne

/-- Distinct prime curves have positive intersection number iff they meet. -/
theorem inter_pos_iff {C C' : R.S.PrimeCurve} (hne : C ≠ C') :
    0 < C.intersectionNumber (R.S.primeCurveCartier R.hreg C') ↔
      ((C : Set R.S.toScheme) ∩ (C' : Set R.S.toScheme)).Nonempty := by
  have h0 := inter_nonneg hne
  rw [← PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber R.S R.hreg]
    at h0 ⊢
  rw [← Set.not_disjoint_iff_nonempty_inter,
    ← PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint R.S R.hreg
      C C' hne]
  constructor <;> intro h <;> omega

theorem int_mul_eq_one {a b : ℤ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a * b = 1) : a = 1 ∧ b = 1 := by
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

open Classical in
include hg e in
/-- **The weighted valency equation**: for a component `C` of the fibre over `t`,
`Σ_{C' ≠ C} μ_{C'} (C · C') = -μ_C C²` (the fibre intersection equation `F · C = 0`). -/
theorem valency_eq {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme}
    (hE : IsFiberDivisor F g t E) (C : R.S.PrimeCurve) (hC : InFiber g t C) :
    ∑ C' ∈ (R.S.cartierToWeilHom E).support.erase C,
        R.S.cartierToWeilHom E C' * C.intersectionNumber (R.S.primeCurveCartier R.hreg C')
      = -(R.S.cartierToWeilHom E C * C.selfIntersectionNumber R.hreg) := by
  classical
  have h0 : C.intersectionNumber F = 0 := intersectionNumber_eq_zero_of_vertical R F g hg e C t hC
  have h := fiber_intersection_eq R F g hE C
  rw [h0] at h
  unfold Finsupp.sum at h
  have hmem : C ∈ (R.S.cartierToWeilHom E).support := (inFiber_iff_mem_support R F g hE C).mp hC
  rw [← Finset.add_sum_erase _ _ hmem] at h
  change 0 = R.S.cartierToWeilHom E C * C.selfIntersectionNumber R.hreg + _ at h
  linarith

/-- The incidence graph of the components of the fibre over `t` (the graph of Lemma 3.2). -/
abbrev fiberGraph (t : projectiveSpace k 1) : SimpleGraph {C : R.S.PrimeCurve // InFiber g t C} :=
  curveIncidenceGraph (fun C : {C : R.S.PrimeCurve // InFiber g t C} => C.1)

theorem fiberGraph_adj_iff (t : projectiveSpace k 1) (a b : {C : R.S.PrimeCurve // InFiber g t C}) :
    (fiberGraph g t).Adj a b ↔
      a ≠ b ∧ ((a.1 : Set R.S.toScheme) ∩ (b.1 : Set R.S.toScheme)).Nonempty := Iff.rfl

theorem graph_adj_iff (i j : R.Vertices) :
    R.graph.Adj i j ↔ i ≠ j ∧ ((i.val : Set R.S.toScheme) ∩ (j.val : Set R.S.toScheme)).Nonempty :=
  Iff.rfl

/-- Adjacent fibre components have positive intersection number. -/
theorem inter_pos_of_adj {t : projectiveSpace k 1} {a b : {C : R.S.PrimeCurve // InFiber g t C}}
    (h : (fiberGraph g t).Adj a b) :
    0 < a.1.intersectionNumber (R.S.primeCurveCartier R.hreg b.1) := by
  have hne : a.1 ≠ b.1 := fun heq => h.1 (Subtype.ext heq)
  exact (inter_pos_iff hne).mpr h.2

end Inter

/-! ### A connected graph minus a vertex has at most `degree` components -/

section GraphAux

variable {W : Type*} (Gf : SimpleGraph W) (w₀ : W)

/-- A walk avoiding `w₀` lifts to the graph induced on the complement of `w₀`. -/
theorem reachable_induce_of_not_mem_support :
    ∀ {a b : W} (q : Gf.Walk a b), w₀ ∉ q.support → ∀ (ha : a ≠ w₀) (hb : b ≠ w₀),
      (Gf.induce {w | w ≠ w₀}).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  intro a b q
  induction q with
  | nil =>
    intro _ ha hb
    exact SimpleGraph.Reachable.refl _
  | @cons a c b h q' ih =>
    intro hmem ha hb
    rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hmem
    have hc : c ≠ w₀ := fun hc => hmem.2 (hc ▸ q'.start_mem_support)
    exact (SimpleGraph.Adj.reachable
      (show (Gf.induce {w | w ≠ w₀}).Adj ⟨a, ha⟩ ⟨c, hc⟩ from h)).trans (ih hmem.2 hc hb)

/-- In a finite connected graph, deleting a vertex `w₀` leaves at most `deg w₀` connected
components (each component contains a neighbour of `w₀`). -/
theorem natCard_components_induce_ne_le [Finite W] (hconn : Gf.Connected) :
    Nat.card (Gf.induce {w | w ≠ w₀}).ConnectedComponent ≤ Nat.card {w : W // Gf.Adj w₀ w} := by
  classical
  have hex : ∀ c : (Gf.induce {w | w ≠ w₀}).ConnectedComponent,
      ∃ u : W, Gf.Adj w₀ u ∧ ∃ hu : u ≠ w₀,
        (Gf.induce {w | w ≠ w₀}).connectedComponentMk ⟨u, hu⟩ = c := by
    intro c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h w =>
      obtain ⟨v, hv⟩ := w
      have hv' : v ≠ w₀ := hv
      obtain ⟨p⟩ := hconn.preconnected w₀ v
      have hq := p.bypass_isPath
      generalize p.bypass = q at hq
      cases q with
      | nil => exact absurd rfl hv'
      | @cons _ u _ h q' =>
        rw [SimpleGraph.Walk.cons_isPath_iff] at hq
        have hu : u ≠ w₀ := fun huw => hq.2 (huw ▸ q'.start_mem_support)
        exact ⟨u, h, hu, SimpleGraph.ConnectedComponent.sound
          (reachable_induce_of_not_mem_support Gf w₀ q' hq.2 hu hv')⟩
  choose f hf using hex
  refine Nat.card_le_card_of_injective (fun c => ⟨f c, (hf c).1⟩) ?_
  intro c c' hcc'
  obtain ⟨hu, hc⟩ := (hf c).2
  obtain ⟨hu', hc'⟩ := (hf c').2
  have hff : f c = f c' := congrArg Subtype.val hcc'
  rw [← hc, ← hc']
  congr 1
  exact Subtype.ext hff

end GraphAux

/-! ### Pattern `(2)`: valency and pieces -/

section PatternTwo

variable {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme}

open Classical in
include p hp hFF hKF hg e in
/-- Manuscript Lemma 7.3, pattern `(2)` (lines 2177–2178 and 2186–2187): the unique exterior
component `R₀` (multiplicity two) satisfies `Σ_{C ≠ R₀} μ_C (R₀ · C) = 2`, so at most two fibre
components meet `R₀` (`R₀` has valency at most two in the fibre). -/
theorem pattern_two_valency [IsProper g] [Surjective g] (hE : IsFiberDivisor F g t E)
    (hred : ∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C')
    (R₀ : R.S.PrimeCurve) (hR₀ : InFiber g t R₀) (hex : ¬ IsExceptionalCurve R.π R₀)
    (hμ : R.S.cartierToWeilHom E R₀ = 2) :
    (∑ C' ∈ (R.S.cartierToWeilHom E).support.erase R₀,
        R.S.cartierToWeilHom E C' * R₀.intersectionNumber (R.S.primeCurveCartier R.hreg C')) = 2 ∧
    Nat.card {C' : R.S.PrimeCurve // C' ∈ (R.S.cartierToWeilHom E).support ∧ C' ≠ R₀ ∧
        0 < R₀.intersectionNumber (R.S.primeCurveCartier R.hreg C')} ≤ 2 := by
  classical
  have hsq := (exterior_component_isMinusOne p hp F hFF hKF g hg e hE hred R₀ hR₀ hex).1.selfIntersection
  have hval := valency_eq F g hg e hE R₀ hR₀
  rw [hμ, hsq] at hval
  have hval2 : (∑ C' ∈ (R.S.cartierToWeilHom E).support.erase R₀,
      R.S.cartierToWeilHom E C' * R₀.intersectionNumber (R.S.primeCurveCartier R.hreg C')) = 2 := by
    rw [hval]; norm_num
  refine ⟨hval2, ?_⟩
  set T := ((R.S.cartierToWeilHom E).support.erase R₀).filter fun C' =>
    0 < R₀.intersectionNumber (R.S.primeCurveCartier R.hreg C') with hT
  have hμpos : ∀ C' ∈ (R.S.cartierToWeilHom E).support, 1 ≤ R.S.cartierToWeilHom E C' :=
    fun C' hC' => coeff_pos_of_inFiber R F g hE C' ((inFiber_iff_mem_support R F g hE C').mpr hC')
  have hterm : ∀ C' ∈ T,
      (1 : ℤ) ≤ R.S.cartierToWeilHom E C' * R₀.intersectionNumber (R.S.primeCurveCartier R.hreg C') := by
    intro C' hC'
    rw [hT, Finset.mem_filter, Finset.mem_erase] at hC'
    have h1 := hμpos C' hC'.1.2
    have h2 : 1 ≤ R₀.intersectionNumber (R.S.primeCurveCartier R.hreg C') := by
      have := hC'.2; omega
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]
  have hcard : (T.card : ℤ) ≤ ∑ C' ∈ T,
      R.S.cartierToWeilHom E C' * R₀.intersectionNumber (R.S.primeCurveCartier R.hreg C') := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    exact Finset.sum_le_sum fun C' hC' => by simpa using hterm C' hC'
  have hsub : (∑ C' ∈ T,
        R.S.cartierToWeilHom E C' * R₀.intersectionNumber (R.S.primeCurveCartier R.hreg C'))
      ≤ ∑ C' ∈ (R.S.cartierToWeilHom E).support.erase R₀,
        R.S.cartierToWeilHom E C' * R₀.intersectionNumber (R.S.primeCurveCartier R.hreg C') := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro C' hC' _
    rw [Finset.mem_erase] at hC'
    exact mul_nonneg (by linarith [hμpos C' hC'.2]) (inter_nonneg (Ne.symm hC'.1))
  have hT2 : T.card ≤ 2 := by
    have : (T.card : ℤ) ≤ 2 := by linarith
    exact_mod_cast this
  rw [← Nat.card_eq_finsetCard] at hT2
  refine le_trans (le_of_eq (Nat.card_congr (Equiv.subtypeEquivRight fun C' => ?_))) hT2
  rw [hT, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h2, h1⟩, h3⟩
  · rintro ⟨⟨h2, h1⟩, h3⟩
    exact ⟨h1, h2, h3⟩

/-- Pattern `(2)`: the exceptional fibre vertices over `t` are the fibre components other than the
unique exterior component `R₀`. -/
def patternTwoEquiv (R₀ : R.S.PrimeCurve) (hR₀ : InFiber g t R₀) (hex : ¬ IsExceptionalCurve R.π R₀)
    (huniq : ∀ C, InFiber g t C → ¬ IsExceptionalCurve R.π C → C = R₀) :
    {i : R.Vertices // InFiber g t i.val} ≃
      {w : {C : R.S.PrimeCurve // InFiber g t C} // w ≠ ⟨R₀, hR₀⟩} where
  toFun i := ⟨⟨i.1.1, i.2⟩, fun h => hex (by
    have h' : i.1.1 = R₀ := congrArg Subtype.val h
    rw [← h']
    exact i.1.2)⟩
  invFun w := ⟨⟨w.1.1, Classical.byContradiction fun hexc =>
    w.2 (Subtype.ext (huniq w.1.1 w.1.2 hexc))⟩, w.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Pattern `(2)`: the graph induced by `R.graph` on the vertical vertices over `t` is the fibre
incidence graph with the exterior component `R₀` deleted. -/
def patternTwoIso (R₀ : R.S.PrimeCurve) (hR₀ : InFiber g t R₀) (hex : ¬ IsExceptionalCurve R.π R₀)
    (huniq : ∀ C, InFiber g t C → ¬ IsExceptionalCurve R.π C → C = R₀) :
    R.graph.induce {i : R.Vertices | InFiber g t i.val} ≃g
      (fiberGraph g t).induce {w | w ≠ ⟨R₀, hR₀⟩} where
  toEquiv := patternTwoEquiv g R₀ hR₀ hex huniq
  map_rel_iff' := by
    intro a b
    change (fiberGraph g t).Adj (patternTwoEquiv g R₀ hR₀ hex huniq a).1
      (patternTwoEquiv g R₀ hR₀ hex huniq b).1 ↔ R.graph.Adj a.1 b.1
    rw [fiberGraph_adj_iff, graph_adj_iff]
    constructor
    · rintro ⟨hne, hint⟩
      refine ⟨fun h => hne ?_, hint⟩
      have h' : a.1.1 = b.1.1 := congrArg Subtype.val h
      exact Subtype.ext h'
    · rintro ⟨hne, hint⟩
      refine ⟨fun h => hne ?_, hint⟩
      have h' := congrArg Subtype.val h
      exact Subtype.ext h'

include p hp hFF hKF hg e in
/-- Manuscript Lemma 7.3, pattern `(2)` (lines 2147–2148): the exceptional vertical part of the
fibre has at most two connected pieces (`r_t ≤ 2`): every piece contains a neighbour of the
unique exterior component `R₀`, which has at most two. -/
theorem pattern_two_numPieces_le_two [IsProper g] [Surjective g] (hE : IsFiberDivisor F g t E)
    (hred : ∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C')
    (R₀ : R.S.PrimeCurve) (hR₀ : InFiber g t R₀) (hex : ¬ IsExceptionalCurve R.π R₀)
    (hμ : R.S.cartierToWeilHom E R₀ = 2)
    (huniq : ∀ C, InFiber g t C → ¬ IsExceptionalCurve R.π C → C = R₀) :
    numPieces g t ≤ 2 := by
  classical
  haveI : Finite {C : R.S.PrimeCurve // InFiber g t C} := finite_inFiber_of_isFiberDivisor F g hE
  have hconn := fiber_isConnected R p hp F hFF hKF g hg e t
  have hGconn : (fiberGraph g t).Connected := fiberGraph_connected R F g hE hconn
  have h1 : numPieces g t =
      Nat.card ((fiberGraph g t).induce {w | w ≠ ⟨R₀, hR₀⟩}).ConnectedComponent :=
    Nat.card_congr (patternTwoIso g R₀ hR₀ hex huniq).connectedComponentEquiv
  have h2 := natCard_components_induce_ne_le (fiberGraph g t) ⟨R₀, hR₀⟩ hGconn
  have h3 : Nat.card {w : {C : R.S.PrimeCurve // InFiber g t C} //
      (fiberGraph g t).Adj ⟨R₀, hR₀⟩ w} ≤ 2 := by
    have hval := (pattern_two_valency p hp F hFF hKF g hg e hE hred R₀ hR₀ hex hμ).2
    refine le_trans ?_ hval
    haveI : Finite {C' : R.S.PrimeCurve // C' ∈ (R.S.cartierToWeilHom E).support ∧ C' ≠ R₀ ∧
        0 < R₀.intersectionNumber (R.S.primeCurveCartier R.hreg C')} :=
      Finite.of_injective
        (fun x => (⟨x.1, x.2.1⟩ : {C' : R.S.PrimeCurve // C' ∈ (R.S.cartierToWeilHom E).support}))
        fun _ _ h => Subtype.ext (Subtype.mk.inj h)
    have hmem : ∀ w : {w : {C : R.S.PrimeCurve // InFiber g t C} //
        (fiberGraph g t).Adj ⟨R₀, hR₀⟩ w},
        w.1.1 ∈ (R.S.cartierToWeilHom E).support ∧ w.1.1 ≠ R₀ ∧
          0 < R₀.intersectionNumber (R.S.primeCurveCartier R.hreg w.1.1) := by
      intro w
      have hadj' := (fiberGraph_adj_iff g t ⟨R₀, hR₀⟩ w.1).mp w.2
      refine ⟨(inFiber_iff_mem_support R F g hE _).mp w.1.2, fun h => hadj'.1 (Subtype.ext h).symm, ?_⟩
      have hpos := inter_pos_of_adj (t := t) g w.2
      exact hpos
    refine Nat.card_le_card_of_injective (fun w => ⟨w.1.1, hmem w⟩) ?_
    intro w w' h
    exact Subtype.ext (Subtype.ext (Subtype.mk.inj h))
  omega

end PatternTwo

/-! ### Pattern `(1, 1)`: the chain -/

section PatternOneOne

variable (hrho : 2 < R.S.picardRank) (P : R.S.PrimeCurve) (hP : R.IsShortestExteriorMinusOne P)
  (hL : R.S.numericalIntersectionBilinForm R.hreg R.Lnum
    (NefNullCurveNegativeSquare.cartierClass R.S F) = 2 * R.Ldeg P)
  {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme}

include p hp hFF hKF hg e hrho hP hL in
/-- **Manuscript Lemma 7.3, pattern `(1, 1)`** (lines 2148–2151 and 2179–2186): if the fibre has
exactly two exterior components `R₁ ≠ R₂`, both of multiplicity one, then the reduced fibre is a
chain `R₁ − C₁ − ⋯ − C_l − R₂` (`l ≥ 0`): there is an injective enumeration `c : Fin (l+2) → S`
of the fibre components with `c 0 = R₁`, `c (l+1) = R₂`, all multiplicities one, the interior
members exceptional, consecutive members meeting with intersection number one and non-consecutive
distinct members disjoint. The proof traces the neighbours along a path from `R₁` to `R₂` in the
fibre incidence graph using the weighted valency equations `Σ_{C' ≠ C} μ_{C'} (C · C') = -μ_C C²`
(`= 1` at the exterior components, `= 2 μ_C` at the retained `(-2)`-curves) and concludes by
connectedness that the path exhausts the fibre. -/
theorem pattern_one_one_chain [IsProper g] [Surjective g] (hE : IsFiberDivisor F g t E)
    (hred : ∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C')
    (R₁ R₂ : R.S.PrimeCurve) (hne : R₁ ≠ R₂) (h₁ : InFiber g t R₁) (h₂ : InFiber g t R₂)
    (hex₁ : ¬ IsExceptionalCurve R.π R₁) (hex₂ : ¬ IsExceptionalCurve R.π R₂)
    (hμ₁ : R.S.cartierToWeilHom E R₁ = 1) (hμ₂ : R.S.cartierToWeilHom E R₂ = 1)
    (huniq : ∀ C, InFiber g t C → ¬ IsExceptionalCurve R.π C → C = R₁ ∨ C = R₂) :
    ∃ (l : ℕ) (c : Fin (l + 2) → R.S.PrimeCurve),
      c 0 = R₁ ∧ c (Fin.last (l + 1)) = R₂ ∧ Function.Injective c ∧
      (∀ C, InFiber g t C ↔ ∃ i, c i = C) ∧
      (∀ i, R.S.cartierToWeilHom E (c i) = 1) ∧
      (∀ i : Fin (l + 2), i ≠ 0 → i ≠ Fin.last (l + 1) → IsExceptionalCurve R.π (c i)) ∧
      (∀ i j : Fin (l + 2), (i : ℕ) + 1 = j →
        (c i).intersectionNumber (R.S.primeCurveCartier R.hreg (c j)) = 1) ∧
      (∀ i j : Fin (l + 2), i ≠ j → (i : ℕ) + 1 ≠ j → (j : ℕ) + 1 ≠ i →
        (c i).intersectionNumber (R.S.primeCurveCartier R.hreg (c j)) = 0) := by
  classical
  set μ := R.S.cartierToWeilHom E with hμdef
  set X := μ.support with hXdef
  have hsq : ∀ C, InFiber g t C → ¬ IsExceptionalCurve R.π C →
      C.selfIntersectionNumber R.hreg = -1 := fun C hC hCex =>
    (exterior_component_isMinusOne p hp F hFF hKF g hg e hE hred C hC hCex).1.selfIntersection
  have hsq2 : ∀ C, InFiber g t C → C ≠ R₁ → C ≠ R₂ →
      IsExceptionalCurve R.π C ∧ C.selfIntersectionNumber R.hreg = -2 := by
    intro C hC hC1 hC2
    have hexC : IsExceptionalCurve R.π C := by
      refine Classical.byContradiction fun h => ?_
      rcases huniq C hC h with h' | h'
      · exact hC1 h'
      · exact hC2 h'
    exact ⟨hexC, (vertical_exceptional_w_eq_two p hp F hFF hKF g hg e hrho P hP hL hE hred
      ⟨C, hexC⟩ hC).2⟩
  have hμpos : ∀ C ∈ X, 1 ≤ μ C := fun C hC =>
    coeff_pos_of_inFiber R F g hE C ((inFiber_iff_mem_support R F g hE C).mpr hC)
  have hmemX : ∀ C, InFiber g t C → C ∈ X := fun C hC => (inFiber_iff_mem_support R F g hE C).mp hC
  have hval : ∀ C, InFiber g t C →
      ∑ C' ∈ X.erase C, μ C' * C.intersectionNumber (R.S.primeCurveCartier R.hreg C')
        = -(μ C * C.selfIntersectionNumber R.hreg) :=
    fun C hC => valency_eq F g hg e hE C hC
  have hnn : ∀ (C : R.S.PrimeCurve) (s : Finset R.S.PrimeCurve), s ⊆ X.erase C →
      ∀ C' ∈ s, 0 ≤ μ C' * C.intersectionNumber (R.S.primeCurveCartier R.hreg C') := by
    intro C s hs C' hC'
    have h := Finset.mem_erase.mp (hs hC')
    exact mul_nonneg (by linarith [hμpos C' h.2]) (inter_nonneg (Ne.symm h.1))
  have hpos1 : ∀ (C C' : R.S.PrimeCurve), C' ∈ X →
      0 < C.intersectionNumber (R.S.primeCurveCartier R.hreg C') →
      1 ≤ μ C' * C.intersectionNumber (R.S.primeCurveCartier R.hreg C') := by
    intro C C' hC' h
    have h1 := hμpos C' hC'
    have h2 : 1 ≤ C.intersectionNumber (R.S.primeCurveCartier R.hreg C') := by omega
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]
  haveI : Finite {C : R.S.PrimeCurve // InFiber g t C} := finite_inFiber_of_isFiberDivisor F g hE
  have hconn := fiber_isConnected R p hp F hFF hKF g hg e t
  have hGconn : (fiberGraph g t).Connected := fiberGraph_connected R F g hE hconn
  let w₁ : {C : R.S.PrimeCurve // InFiber g t C} := ⟨R₁, h₁⟩
  let w₂ : {C : R.S.PrimeCurve // InFiber g t C} := ⟨R₂, h₂⟩
  obtain ⟨p₀⟩ := hGconn.preconnected w₁ w₂
  have hq : p₀.bypass.IsPath := p₀.bypass_isPath
  generalize p₀.bypass = q at hq
  -- the vertices of the path
  let v : ℕ → R.S.PrimeCurve := fun i => (q.getVert i).1
  have hv0 : v 0 = R₁ := congrArg Subtype.val q.getVert_zero
  have hvm : v q.length = R₂ := congrArg Subtype.val q.getVert_length
  have hin : ∀ i, InFiber g t (v i) := fun i => (q.getVert i).2
  have hinX : ∀ i, v i ∈ X := fun i => hmemX _ (hin i)
  have hinj : ∀ i j, i ≤ q.length → j ≤ q.length → v i = v j → i = j := fun i j hi hj h =>
    hq.getVert_injOn hi hj (Subtype.ext h)
  have hm1 : 0 < q.length := Nat.pos_of_ne_zero fun h0 =>
    hne (congrArg Subtype.val (SimpleGraph.Walk.eq_of_length_eq_zero h0))
  have hadj : ∀ i, i < q.length →
      0 < (v i).intersectionNumber (R.S.primeCurveCartier R.hreg (v (i + 1))) ∧ v i ≠ v (i + 1) := by
    intro i hi
    have h := q.adj_getVert_succ hi
    exact ⟨inter_pos_of_adj g h, fun heq => h.1 (Subtype.ext heq)⟩
  -- tracing the neighbours along the path
  have key : ∀ i, i < q.length → μ (v i) = 1 ∧ μ (v (i + 1)) = 1 ∧
      (v i).intersectionNumber (R.S.primeCurveCartier R.hreg (v (i + 1))) = 1 ∧
      ∀ C ∈ X, C ≠ v i → C ≠ v (i + 1) → (∀ j, j + 1 = i → C ≠ v j) →
        (v i).intersectionNumber (R.S.primeCurveCartier R.hreg C) = 0 := by
    intro i
    induction i with
    | zero =>
      intro h0
      have hval0 := hval (v 0) (hin 0)
      rw [hv0, hμ₁, hsq R₁ h₁ hex₁] at hval0
      have hmem1 : v 1 ∈ X.erase R₁ :=
        Finset.mem_erase.mpr ⟨by rw [← hv0]; exact (hadj 0 h0).2.symm, hinX 1⟩
      rw [← Finset.add_sum_erase _ _ hmem1] at hval0
      have hrest : 0 ≤ ∑ C' ∈ (X.erase R₁).erase (v 1),
          μ C' * R₁.intersectionNumber (R.S.primeCurveCartier R.hreg C') :=
        Finset.sum_nonneg (hnn R₁ ((X.erase R₁).erase (v 1)) (Finset.erase_subset _ _))
      have hfirst := hpos1 R₁ (v 1) (hinX 1) (by rw [← hv0]; exact (hadj 0 h0).1)
      have heq1 : μ (v 1) * R₁.intersectionNumber (R.S.primeCurveCartier R.hreg (v 1)) = 1 := by
        linarith
      have hrest0 : ∑ C' ∈ (X.erase R₁).erase (v 1),
          μ C' * R₁.intersectionNumber (R.S.primeCurveCartier R.hreg C') = 0 := by linarith
      obtain ⟨hμ1, hI1⟩ := int_mul_eq_one (hμpos _ (hinX 1))
        (by have := (hadj 0 h0).1; rw [hv0, zero_add] at this; omega) heq1
      refine ⟨by rw [hv0]; exact hμ₁, hμ1, by rw [hv0]; exact hI1, ?_⟩
      intro C hC hC0 hC1 _
      rw [hv0] at hC0
      have hmem : C ∈ (X.erase R₁).erase (v 1) :=
        Finset.mem_erase.mpr ⟨hC1, Finset.mem_erase.mpr ⟨hC0, hC⟩⟩
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (hnn R₁ ((X.erase R₁).erase (v 1)) (Finset.erase_subset _ _))).mp hrest0 C hmem
      rw [hv0]
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd h (by have := hμpos C hC; omega)
      · exact h
    | succ i ih =>
      intro hi
      obtain ⟨hμi, hμi1, hIi, -⟩ := ih (by omega)
      have hne1 : v (i + 1) ≠ R₁ := by
        rw [← hv0]
        intro h
        have := hinj _ _ (by omega) (by omega) h
        omega
      have hne2 : v (i + 1) ≠ R₂ := by
        rw [← hvm]
        intro h
        have := hinj _ _ (by omega) (by omega) h
        omega
      obtain ⟨-, hsqi⟩ := hsq2 (v (i + 1)) (hin (i + 1)) hne1 hne2
      have hvali := hval (v (i + 1)) (hin (i + 1))
      rw [hμi1, hsqi] at hvali
      have hmemi : v i ∈ X.erase (v (i + 1)) :=
        Finset.mem_erase.mpr ⟨(hadj i (by omega)).2, hinX i⟩
      have hne_i2 : v (i + 1 + 1) ≠ v i := fun h => by
        have := hinj _ _ (by omega) (by omega) h
        omega
      have hmemi2 : v (i + 1 + 1) ∈ (X.erase (v (i + 1))).erase (v i) :=
        Finset.mem_erase.mpr ⟨hne_i2, Finset.mem_erase.mpr ⟨(hadj (i + 1) hi).2.symm, hinX _⟩⟩
      rw [← Finset.add_sum_erase _ _ hmemi, ← Finset.add_sum_erase _ _ hmemi2] at hvali
      have htermi : μ (v i) * (v (i + 1)).intersectionNumber (R.S.primeCurveCartier R.hreg (v i)) = 1 := by
        rw [hμi, inter_symm, hIi]
        ring
      have hfirst := hpos1 (v (i + 1)) (v (i + 1 + 1)) (hinX _) (hadj (i + 1) hi).1
      have hsub : ((X.erase (v (i + 1))).erase (v i)).erase (v (i + 1 + 1)) ⊆ X.erase (v (i + 1)) :=
        (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have hrest : 0 ≤ ∑ C' ∈ ((X.erase (v (i + 1))).erase (v i)).erase (v (i + 1 + 1)),
          μ C' * (v (i + 1)).intersectionNumber (R.S.primeCurveCartier R.hreg C') :=
        Finset.sum_nonneg (hnn (v (i + 1)) _ hsub)
      have heq2 : μ (v (i + 1 + 1)) *
          (v (i + 1)).intersectionNumber (R.S.primeCurveCartier R.hreg (v (i + 1 + 1))) = 1 := by
        linarith
      have hrest0 : ∑ C' ∈ ((X.erase (v (i + 1))).erase (v i)).erase (v (i + 1 + 1)),
          μ C' * (v (i + 1)).intersectionNumber (R.S.primeCurveCartier R.hreg C') = 0 := by
        linarith
      obtain ⟨hμ2, hI2⟩ := int_mul_eq_one (hμpos _ (hinX _))
        (by have := (hadj (i + 1) hi).1; omega) heq2
      refine ⟨hμi1, hμ2, hI2, ?_⟩
      intro C hC hC1 hC2 hCj
      have hCi : C ≠ v i := hCj i rfl
      have hmem : C ∈ ((X.erase (v (i + 1))).erase (v i)).erase (v (i + 1 + 1)) :=
        Finset.mem_erase.mpr ⟨hC2, Finset.mem_erase.mpr ⟨hCi, Finset.mem_erase.mpr ⟨hC1, hC⟩⟩⟩
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (hnn (v (i + 1)) _ hsub)).mp hrest0 C hmem
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd h (by have := hμpos C hC; omega)
      · exact h
  -- all multiplicities are one
  have hμall : ∀ i ≤ q.length, μ (v i) = 1 := by
    intro i hi
    rcases Nat.lt_or_ge i q.length with h | h
    · exact (key i h).1
    · obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [hj]
      exact (key j (by omega)).2.1
  -- the neighbours of every path vertex are its path neighbours
  have hN : ∀ i ≤ q.length, ∀ C ∈ X, C ≠ v i →
      (v i).intersectionNumber (R.S.primeCurveCartier R.hreg C) ≠ 0 →
      (i < q.length ∧ C = v (i + 1)) ∨ (∃ j, j + 1 = i ∧ C = v j) := by
    intro i hi C hC hCi hI
    rcases Nat.lt_or_ge i q.length with h | h
    · refine Classical.byContradiction fun hcon => ?_
      push_neg at hcon
      exact hI ((key i h).2.2.2 C hC hCi (hcon.1 h) hcon.2)
    · have him : i = q.length := by omega
      obtain ⟨j, hj⟩ : ∃ j, q.length = j + 1 := ⟨q.length - 1, by omega⟩
      right
      refine ⟨j, by omega, ?_⟩
      have hvalm := hval (v q.length) (hin q.length)
      rw [hvm, hμ₂, hsq R₂ h₂ hex₂] at hvalm
      have hI' : (v j).intersectionNumber (R.S.primeCurveCartier R.hreg R₂) = 1 := by
        rw [← hvm, hj]
        exact (key j (by omega)).2.2.1
      have hmemj : v j ∈ X.erase R₂ := Finset.mem_erase.mpr ⟨by
        rw [← hvm, hj]; exact (hadj j (by omega)).2, hinX j⟩
      rw [← Finset.add_sum_erase _ _ hmemj] at hvalm
      have htermj : μ (v j) * R₂.intersectionNumber (R.S.primeCurveCartier R.hreg (v j)) = 1 := by
        rw [(key j (by omega)).1, inter_symm, hI']
        ring
      have hrest0 : ∑ C' ∈ (X.erase R₂).erase (v j),
          μ C' * R₂.intersectionNumber (R.S.primeCurveCartier R.hreg C') = 0 := by linarith
      refine Classical.byContradiction fun hCj => ?_
      rw [him, hvm] at hCi hI
      have hmem : C ∈ (X.erase R₂).erase (v j) :=
        Finset.mem_erase.mpr ⟨hCj, Finset.mem_erase.mpr ⟨hCi, hC⟩⟩
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (hnn R₂ ((X.erase R₂).erase (v j)) (Finset.erase_subset _ _))).mp hrest0 C hmem
      rcases mul_eq_zero.mp hz with h' | h'
      · exact absurd h' (by have := hμpos C hC; omega)
      · exact hI h'
  -- the path exhausts the fibre (connectedness)
  have hclosure : ∀ (a b : {C : R.S.PrimeCurve // InFiber g t C}) (r : (fiberGraph g t).Walk a b),
      (∃ i ≤ q.length, v i = a.1) → ∃ i ≤ q.length, v i = b.1 := by
    intro a b r
    induction r with
    | nil => exact id
    | @cons a c b h r' ih =>
      intro ha
      apply ih
      obtain ⟨i, hi, hvi⟩ := ha
      have hne' : c.1 ≠ v i := by
        rw [hvi]
        exact fun h' => h.1 (Subtype.ext h'.symm)
      have hI : (v i).intersectionNumber (R.S.primeCurveCartier R.hreg c.1) ≠ 0 := by
        rw [hvi]
        exact (inter_pos_of_adj g h).ne'
      rcases hN i hi c.1 (hmemX c.1 c.2) hne' hI with ⟨hlt, hc⟩ | ⟨j, hj, hc⟩
      · exact ⟨i + 1, by omega, hc.symm⟩
      · exact ⟨j, by omega, hc.symm⟩
  have hall : ∀ C, InFiber g t C → ∃ i ≤ q.length, v i = C := by
    intro C hC
    obtain ⟨r⟩ := hGconn.preconnected w₁ ⟨C, hC⟩
    exact hclosure w₁ ⟨C, hC⟩ r ⟨0, by omega, hv0⟩
  -- packaging
  obtain ⟨l, hl⟩ : ∃ l, q.length = l + 1 := ⟨q.length - 1, by omega⟩
  refine ⟨l, fun i => v i, hv0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show v (l + 1) = R₂
    rw [← hl]
    exact hvm
  · intro i j h
    exact Fin.ext (hinj i j (by have := i.isLt; omega) (by have := j.isLt; omega) h)
  · intro C
    constructor
    · intro hC
      obtain ⟨i, hi, hvi⟩ := hall C hC
      exact ⟨⟨i, by omega⟩, hvi⟩
    · rintro ⟨i, rfl⟩
      exact hin i
  · intro i
    exact hμall i (by have := i.isLt; omega)
  · intro i hi0 hil
    have hne1 : v i ≠ R₁ := by
      rw [← hv0]
      intro h
      exact hi0 (Fin.ext (hinj _ _ (by have := i.isLt; omega) (by omega) h))
    have hne2 : v i ≠ R₂ := by
      rw [← hvm]
      intro h
      have := hinj _ _ (by have := i.isLt; omega) le_rfl h
      exact hil (Fin.ext (by rw [Fin.val_last]; omega))
    exact (hsq2 (v i) (hin i) hne1 hne2).1
  · intro i j hij
    show (v i).intersectionNumber (R.S.primeCurveCartier R.hreg (v j)) = 1
    rw [← hij]
    exact (key i (by have := j.isLt; omega)).2.2.1
  · intro i j hij hij1 hji1
    show (v i).intersectionNumber (R.S.primeCurveCartier R.hreg (v j)) = 0
    refine Classical.byContradiction fun hI => ?_
    have hvne : v j ≠ v i := fun h =>
      hij (Fin.ext (hinj _ _ (by have := i.isLt; omega) (by have := j.isLt; omega) h)).symm
    rcases hN i (by have := i.isLt; omega) (v j) (hinX j) hvne hI with ⟨hlt, hc⟩ | ⟨j', hj', hc⟩
    · exact hij1 (hinj _ _ (by have := j.isLt; omega) (by omega) hc).symm
    · have := hinj _ _ (by have := j.isLt; omega) (by omega) hc
      exact hji1 (by omega)

end PatternOneOne

end KltDP.Manuscript.S07

#print axioms KltDP.Manuscript.S07.Lnum_pairing_fiberDivisor
#print axioms KltDP.Manuscript.S07.exterior_component_isMinusOne
#print axioms KltDP.Manuscript.S07.fiber_degree_equalities
#print axioms KltDP.Manuscript.S07.exterior_pattern
#print axioms KltDP.Manuscript.S07.card_twoExteriorFibres_le
#print axioms KltDP.Manuscript.S07.pattern_two_valency
#print axioms KltDP.Manuscript.S07.pattern_two_numPieces_le_two
#print axioms KltDP.Manuscript.S07.pattern_one_one_chain

import KltDP.Manuscript.S05.PicardIndex
import KltDP.Manuscript.S02.Projection
import KltDP.Manuscript.S04.DiscrepancyLemmas
import KltDP.Support.ZeroAdjointTable
import KltDP.Lattices.SmallADEForestDecomposition
import KltDP.Lattices.SmallADEForestLattice

/-!
# Section 5.5 of the manuscript: the zero-adjoint three-curve configuration

Manuscript `source/manuscript.tex`, Proposition 5.5 (`prop:zero-adjoint`, lines 1483–1541), for
the resolution datum `R = (S, D, L)` of a rank-one klt del Pezzo surface in characteristic
`p > 2`: if `C, B₁, B₂ ⊂ D` are pairwise disjoint exceptional curves with `C² = -2`,
`B₁² = -3`, `B₂² = -β` (`β ≥ 3`), `P ⊄ D` is a `(-1)`-curve with `P·C = P·B₁ = P·B₂ = 1`, and
`-K_S ≡ C + B₁ + B₂ + 2P` numerically, then `#Sing(X) ≤ 7`.

The proof follows the manuscript line by line (lines 1497–1541):

* every other exceptional vertex `A` has `0 ≤ K_S·A = -(C+B₁+B₂+2P)·A ≤ 0`, hence weight two and
  disjoint from `C, B₁, B₂, P` (`other_vertex`);
* `C, B₁, B₂` are isolated with discrepancies `0, 1/3, (β-2)/β`, so `L·P = (6-β)/(3β) > 0` forces
  `β ∈ {3, 4, 5}` (`Ldeg_eq`, `exists_beta`);
* `K_S² = 3 - β` (`Ksq_eq`), Noether gives `ρ(S) = β + 7`, so the forest
  `F = D ∖ {C, B₁, B₂}` has `β + 3` weight-two vertices (`card_vertices`) and at least five
  components (`five_le_components`, from `#Sing(X) ≥ 8`);
* the index `I = [Pic S : ⟨D, P⟩]` satisfies `I² = det A · (g - 1) = (6 - β) det A_F` with
  `det A = 6β det A_F` (block decomposition, `A_det_eq`) and `g = pᵀA⁻¹p = 1/2 + 1/3 + 1/β`
  (`green_eq`);
* the union's `smallADEForest_decomposition` identifies `det A_F` with the ADE root determinant of
  the forest, the union's `ZeroAdjointTable` leaves the six table rows with `t > v₂(I)`, while
  Lemma 5.2(ii) (`fullPicardIndexObstruction`) gives `t ≤ v₂(I)` for the `t` isolated `A₁`
  nodes: contradiction.

Everything is derived from the compiled union and the delivered modules; no manuscript theorem is
assumed.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.LinearAlgebra KltDP.Lattices.SmallADEGraphs KltDP.Lattices.SmallADEForestLattice
open KltDP.Lattices.SmallADEForestDecomposition KltDP.Lattices.SmallADEPartitions
open KltDP.Lattices.SmallADEMatrices
open KltDP.Support.ZeroAdjointTable
open KltDP.Manuscript KltDP.Manuscript.S02 KltDP.Manuscript.S04
open scoped BigOperators

universe u

namespace KltDP.Manuscript.S05

namespace ZeroAdjoint

/-! ### An elementary sum lemma -/

/-- A sum over a finite type of a function vanishing outside three distinct points. -/
theorem sum_eq_add_add_add {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (f : ι → M) (a b c : ι) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hf : ∀ x, x ≠ a → x ≠ b → x ≠ c → f x = 0) :
    ∑ x, f x = f a + f b + f c := by
  rw [← Finset.sum_subset (Finset.subset_univ ({a, b, c} : Finset ι)) (fun x _ hx => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact hf x hx.1 hx.2.1 hx.2.2)]
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simpa using hbc),
    Finset.sum_singleton, add_assoc]

end ZeroAdjoint

open ZeroAdjoint

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)

/-! ### Pairings of the exceptional classes -/

/-- Distinct non-adjacent exceptional curves have zero intersection number. -/
theorem M_eq_zero_of_not_adj {i j : R.Vertices} (hne : i ≠ j) (h : ¬ R.graph.Adj i j) :
    R.M i j = 0 := by
  have hne' : i.val ≠ j.val := fun h' => hne (Subtype.ext h')
  have hd := (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
    R.S R.hreg i.val j.val hne').mpr (disjoint_of_not_adj R hne h)
  change (R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.val)
    (R.S.primeCurveCartier R.hreg j.val) : ℚ) = 0
  rw [hd, Int.cast_zero]

/-- Distinct exceptional curves with zero intersection number are not adjacent. -/
theorem not_adj_of_M_eq_zero {i j : R.Vertices} (hne : i ≠ j) (h : R.M i j = 0) :
    ¬ R.graph.Adj i j := by
  intro hadj
  have hne' : i.val ≠ j.val := fun h' => hne (Subtype.ext h')
  have h' : ((R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.val)
    (R.S.primeCurveCartier R.hreg j.val) : ℤ) : ℚ) = 0 := h
  have hd := (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
    R.S R.hreg i.val j.val hne').mp (by exact_mod_cast h')
  obtain ⟨_, hn⟩ := hadj
  exact Set.not_disjoint_iff_nonempty_inter.mpr hn hd

/-- `D_i · D_i = -b_i`. -/
theorem M_diag (i : R.Vertices) : R.M i i = -R.w i := by
  simp [ResolutionDatum.w]

/-- The contact vector of the delivered module `S05.PicardIndex`, entrywise. -/
theorem contact_apply (P : R.S.PrimeCurve) (i : R.Vertices) :
    contact R P i = (R.contact P i : ℚ) := rfl

/-- The contact vector of the delivered module `S02.Projection`, entrywise. -/
theorem contactVector_apply (P : R.S.PrimeCurve) (i : R.Vertices) :
    contactVector R P i = (R.contact P i : ℚ) := rfl

/-- The contact of an exterior curve with an exceptional curve is nonnegative. -/
theorem contactVector_nonneg (P : R.S.PrimeCurve) (hPext : ¬ IsExceptionalCurve R.π P)
    (i : R.Vertices) : 0 ≤ contactVector R P i := by
  have hne : P ≠ i.val := fun h => hPext (h ▸ i.property)
  have h := PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg R.S R.hreg P i.val hne
  rw [PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber] at h
  rw [contactVector_apply]
  exact_mod_cast h

/-! ### The configuration -/

section Configuration

variable (C B₁ B₂ : R.Vertices) (P : R.S.PrimeCurve)

/-- The forest complement `F = D ∖ {C, B₁, B₂}` as a set of vertices. -/
def forestSet : Set R.Vertices := {v | v ≠ C ∧ v ≠ B₁ ∧ v ≠ B₂}

/-- The three displayed vertices, indexed by `Fin 3`. -/
def core : Fin 3 → R.Vertices := ![C, B₁, B₂]

variable (hP : R.IsExteriorMinusOne P)
  (hCB₁ : ¬ R.graph.Adj C B₁) (hCB₂ : ¬ R.graph.Adj C B₂) (hB₁B₂ : ¬ R.graph.Adj B₁ B₂)
  (hne₁ : C ≠ B₁) (hne₂ : C ≠ B₂) (hne₃ : B₁ ≠ B₂)
  (hwC : R.w C = 2) (hwB₁ : R.w B₁ = 3) (hwB₂ : 3 ≤ R.w B₂)
  (hPC : R.contact P C = 1) (hPB₁ : R.contact P B₁ = 1) (hPB₂ : R.contact P B₂ = 1)
  (hK : R.Knum = -(DisjointNegativeCurvesRank.curveClass R.S R.hreg C.val +
    DisjointNegativeCurvesRank.curveClass R.S R.hreg B₁.val +
    DisjointNegativeCurvesRank.curveClass R.S R.hreg B₂.val +
    (2 : ℚ) • DisjointNegativeCurvesRank.curveClass R.S R.hreg P))

include hP hK in
/-- Manuscript lines 1499–1504: every other exceptional component `A` has
`0 ≤ K_S·A = -(C+B₁+B₂+2P)·A ≤ 0`, hence `A² = -2` and `A` is disjoint from `C, B₁, B₂, P`. -/
theorem other_vertex (A : R.Vertices) (hAC : A ≠ C) (hAB₁ : A ≠ B₁) (hAB₂ : A ≠ B₂) :
    R.w A = 2 ∧ ¬ R.graph.Adj C A ∧ ¬ R.graph.Adj B₁ A ∧ ¬ R.graph.Adj B₂ A ∧
      R.contact P A = 0 := by
  have hq := R.Knum_pairing_curveClass A
  rw [hK, LinearMap.BilinForm.neg_left, LinearMap.BilinForm.add_left,
    LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
    curveClass_pairing_vertices R C A, curveClass_pairing_vertices R B₁ A,
    curveClass_pairing_vertices R B₂ A, curveClass_pairing_contact R P A] at hq
  have h1 := R.M_offDiag_nonneg C A hAC.symm
  have h2 := R.M_offDiag_nonneg B₁ A hAB₁.symm
  have h3 := R.M_offDiag_nonneg B₂ A hAB₂.symm
  have h4 := contactVector_nonneg R P hP.2 A
  have h5 := R.two_le_w A
  have hqA : R.q A = R.w A - 2 := rfl
  rw [hqA] at hq
  have hw : R.w A = 2 := by linarith
  have hM1 : R.M C A = 0 := by linarith
  have hM2 : R.M B₁ A = 0 := by linarith
  have hM3 : R.M B₂ A = 0 := by linarith
  have hp : contactVector R P A = 0 := by linarith
  rw [contactVector_apply] at hp
  refine ⟨hw, not_adj_of_M_eq_zero R hAC.symm hM1, not_adj_of_M_eq_zero R hAB₁.symm hM2,
    not_adj_of_M_eq_zero R hAB₂.symm hM3, ?_⟩
  exact_mod_cast hp

include hP hCB₁ hCB₂ hK in
/-- `C` is isolated in the exceptional graph. -/
theorem isolated_C : ∀ y, ¬ R.graph.Adj C y := by
  intro y hy
  by_cases hyC : y = C
  · subst hyC; exact R.graph.loopless _ hy
  by_cases hyB₁ : y = B₁
  · subst hyB₁; exact hCB₁ hy
  by_cases hyB₂ : y = B₂
  · subst hyB₂; exact hCB₂ hy
  exact (other_vertex R C B₁ B₂ P hP hK y hyC hyB₁ hyB₂).2.1 hy

include hP hCB₁ hB₁B₂ hK in
/-- `B₁` is isolated in the exceptional graph. -/
theorem isolated_B₁ : ∀ y, ¬ R.graph.Adj B₁ y := by
  intro y hy
  by_cases hyC : y = C
  · subst hyC; exact hCB₁ hy.symm
  by_cases hyB₁ : y = B₁
  · subst hyB₁; exact R.graph.loopless _ hy
  by_cases hyB₂ : y = B₂
  · subst hyB₂; exact hB₁B₂ hy
  exact (other_vertex R C B₁ B₂ P hP hK y hyC hyB₁ hyB₂).2.2.1 hy

include hP hCB₂ hB₁B₂ hK in
/-- `B₂` is isolated in the exceptional graph. -/
theorem isolated_B₂ : ∀ y, ¬ R.graph.Adj B₂ y := by
  intro y hy
  by_cases hyC : y = C
  · subst hyC; exact hCB₂ hy.symm
  by_cases hyB₁ : y = B₁
  · subst hyB₁; exact hB₁B₂ hy.symm
  by_cases hyB₂ : y = B₂
  · subst hyB₂; exact R.graph.loopless _ hy
  exact (other_vertex R C B₁ B₂ P hP hK y hyC hyB₁ hyB₂).2.2.2.1 hy

include hP hCB₁ hCB₂ hB₁B₂ hK in
/-- Every vertex of the core is isolated. -/
theorem isolated_core (i : Fin 3) : ∀ y, ¬ R.graph.Adj (core R C B₁ B₂ i) y := by
  fin_cases i
  · exact isolated_C R C B₁ B₂ P hP hCB₁ hCB₂ hK
  · exact isolated_B₁ R C B₁ B₂ P hP hCB₁ hB₁B₂ hK
  · exact isolated_B₂ R C B₁ B₂ P hP hCB₂ hB₁B₂ hK

include hP hCB₁ hCB₂ hB₁B₂ hK in
/-- Every vertex outside the forest is isolated. -/
theorem isolated_of_not_mem_forestSet (v : R.Vertices) (hv : v ∉ forestSet R C B₁ B₂) :
    ∀ y, ¬ R.graph.Adj v y := by
  simp only [forestSet, Set.mem_setOf_eq, not_and, not_not] at hv
  by_cases h1 : v = C
  · subst h1; exact isolated_C R v B₁ B₂ P hP hCB₁ hCB₂ hK
  by_cases h2 : v = B₁
  · subst h2; exact isolated_B₁ R C v B₂ P hP hCB₁ hB₁B₂ hK
  have h3 : v = B₂ := hv h1 h2
  subst h3; exact isolated_B₂ R C B₁ v P hP hCB₂ hB₁B₂ hK

include hne₁ hne₂ hne₃ in
/-- The core vertices are pairwise distinct. -/
theorem core_injective : Function.Injective (core R C B₁ B₂) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [core] at h ⊢ <;>
    first
    | exact hne₁ h | exact hne₂ h | exact hne₃ h
    | exact hne₁ h.symm | exact hne₂ h.symm | exact hne₃ h.symm

/-- The core vertices are not in the forest. -/
theorem core_not_mem_forestSet (i : Fin 3) : core R C B₁ B₂ i ∉ forestSet R C B₁ B₂ := by
  fin_cases i <;> simp [core, forestSet]

/-- A core vertex differs from every forest vertex. -/
theorem core_ne_forest (i : Fin 3) (y : forestSet R C B₁ B₂) : core R C B₁ B₂ i ≠ y.val := by
  intro h
  apply core_not_mem_forestSet R C B₁ B₂ i
  rw [h]
  exact y.property

/-- The discrepancy of an isolated vertex: `b_v λ_v = b_v - 2`. -/
theorem w_mul_lam_of_isolated (v : R.Vertices) (hiso : ∀ y, ¬ R.graph.Adj v y) :
    R.w v * R.lam v = R.w v - 2 := by
  classical
  have h := row_equation R v
  rwa [Finset.sum_eq_zero (fun u hu => absurd ((R.graph.mem_neighborFinset v u).1 hu) (hiso u)),
    sub_zero] at h

include hP hCB₁ hCB₂ hB₁B₂ hne₁ hne₂ hne₃ hwC hwB₁ hwB₂ hPC hPB₁ hPB₂ hK in
/-- `L·P = (6 - β)/(3β)` (manuscript line 1506). -/
theorem Ldeg_eq : R.Ldeg P = (6 - R.w B₂) / (3 * R.w B₂) := by
  classical
  have hch := rankOneProjection_charge R P hP
  have hlC : R.lam C = 0 := by
    have := w_mul_lam_of_isolated R C (isolated_C R C B₁ B₂ P hP hCB₁ hCB₂ hK)
    rw [hwC] at this; linarith
  have hlB₁ : R.lam B₁ = 1 / 3 := by
    have := w_mul_lam_of_isolated R B₁ (isolated_B₁ R C B₁ B₂ P hP hCB₁ hB₁B₂ hK)
    rw [hwB₁] at this; linarith
  have hlB₂ : R.lam B₂ = (R.w B₂ - 2) / R.w B₂ := by
    have := w_mul_lam_of_isolated R B₂ (isolated_B₂ R C B₁ B₂ P hP hCB₂ hB₁B₂ hK)
    rw [eq_div_iff (by linarith)]; linarith
  have hsum : dotProduct (contactVector R P) R.lam =
      contactVector R P C * R.lam C + contactVector R P B₁ * R.lam B₁ +
        contactVector R P B₂ * R.lam B₂ := by
    unfold dotProduct
    refine sum_eq_add_add_add _ C B₁ B₂ hne₁ hne₂ hne₃ (fun x hx1 hx2 hx3 => ?_)
    have h0 := (other_vertex R C B₁ B₂ P hP hK x hx1 hx2 hx3).2.2.2.2
    rw [contactVector_apply, h0, Int.cast_zero, zero_mul]
  have hcC : contactVector R P C = 1 := by rw [contactVector_apply, hPC, Int.cast_one]
  have hcB₁ : contactVector R P B₁ = 1 := by rw [contactVector_apply, hPB₁, Int.cast_one]
  have hcB₂ : contactVector R P B₂ = 1 := by rw [contactVector_apply, hPB₂, Int.cast_one]
  rw [hsum, hcC, hcB₁, hcB₂, hlC, hlB₁, hlB₂] at hch
  have hβ : R.w B₂ ≠ 0 := by linarith
  have hL : R.Ldeg P = 1 - 1 / 3 - (R.w B₂ - 2) / R.w B₂ := by linarith
  rw [hL]
  field_simp
  ring

include hP hCB₁ hCB₂ hB₁B₂ hne₁ hne₂ hne₃ hwC hwB₁ hwB₂ hPC hPB₁ hPB₂ hK in
/-- `β ∈ {3, 4, 5}` (manuscript line 1507): `β` is an integer with `3 ≤ β < 6`. -/
theorem exists_beta : ∃ β : ℕ, R.w B₂ = β ∧ 3 ≤ β ∧ β ≤ 5 := by
  have hl := Ldeg_pos R P hP.2
  rw [Ldeg_eq R C B₁ B₂ P hP hCB₁ hCB₂ hB₁B₂ hne₁ hne₂ hne₃ hwC hwB₁ hwB₂ hPC hPB₁ hPB₂ hK] at hl
  have hlt : R.w B₂ < 6 := by
    by_contra h
    push_neg at h
    have : (6 - R.w B₂) / (3 * R.w B₂) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith
  have hint : R.w B₂ = ((-(B₂.val.selfIntersectionNumber R.hreg) : ℤ) : ℚ) := by
    rw [w_eq_neg_selfIntersection, Int.cast_neg]
  have hb3 : (3 : ℤ) ≤ -(B₂.val.selfIntersectionNumber R.hreg) := by
    have := hwB₂
    rw [hint] at this
    exact_mod_cast this
  have hb6 : -(B₂.val.selfIntersectionNumber R.hreg) < (6 : ℤ) := by
    rw [hint] at hlt
    exact_mod_cast hlt
  rcases (by omega : -(B₂.val.selfIntersectionNumber R.hreg) = 3 ∨
      -(B₂.val.selfIntersectionNumber R.hreg) = 4 ∨
      -(B₂.val.selfIntersectionNumber R.hreg) = 5) with h | h | h
  · exact ⟨3, by rw [hint, h]; norm_num, by norm_num, by norm_num⟩
  · exact ⟨4, by rw [hint, h]; norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, by rw [hint, h]; norm_num, by norm_num, by norm_num⟩

include hP hCB₁ hCB₂ hB₁B₂ hne₁ hne₂ hne₃ hwC hwB₁ hPC hPB₁ hPB₂ hK in
/-- `K_S² = 3 - β` (manuscript line 1508). -/
theorem Ksq_eq : R.Ksq = 3 - R.w B₂ := by
  have hsymm := R.S.numericalIntersectionBilinForm_isSymm R.hreg
  have hCC : R.S.numericalIntersectionBilinForm R.hreg
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg C.val)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg C.val) = -2 := by
    rw [curveClass_pairing_vertices, M_diag, hwC]
  have hB₁B₁ : R.S.numericalIntersectionBilinForm R.hreg
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg B₁.val)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg B₁.val) = -3 := by
    rw [curveClass_pairing_vertices, M_diag, hwB₁]
  have hB₂B₂ : R.S.numericalIntersectionBilinForm R.hreg
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg B₂.val)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg B₂.val) = -R.w B₂ := by
    rw [curveClass_pairing_vertices, M_diag]
  have hPP : R.S.numericalIntersectionBilinForm R.hreg
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg P)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg P) = -1 := by
    rw [curveClass_self_pairing, hP.1.selfIntersection]; norm_num
  have hCB₁' : R.S.numericalIntersectionBilinForm R.hreg
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg C.val)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg B₁.val) = 0 := by
    rw [curveClass_pairing_vertices, M_eq_zero_of_not_adj R hne₁ hCB₁]
  have hB₁C' : R.S.numericalIntersectionBilinForm R.hreg
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg B₁.val)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg C.val) = 0 := by
    rw [hsymm.eq, hCB₁']
  have hCB₂' : R.S.numericalIntersectionBilinForm R.hreg
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg C.val)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg B₂.val) = 0 := by
    rw [curveClass_pairing_vertices, M_eq_zero_of_not_adj R hne₂ hCB₂]
  have hB₂C' : R.S.numericalIntersectionBilinForm R.hreg
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg B₂.val)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg C.val) = 0 := by
    rw [hsymm.eq, hCB₂']
  have hB₁B₂' : R.S.numericalIntersectionBilinForm R.hreg
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg B₁.val)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg B₂.val) = 0 := by
    rw [curveClass_pairing_vertices, M_eq_zero_of_not_adj R hne₃ hB₁B₂]
  have hB₂B₁' : R.S.numericalIntersectionBilinForm R.hreg
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg B₂.val)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg B₁.val) = 0 := by
    rw [hsymm.eq, hB₁B₂']
  have hPC' : R.S.numericalIntersectionBilinForm R.hreg
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg P)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg C.val) = 1 := by
    rw [curveClass_pairing_contact, contactVector_apply, hPC, Int.cast_one]
  have hCP' : R.S.numericalIntersectionBilinForm R.hreg
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg C.val)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg P) = 1 := by
    rw [hsymm.eq, hPC']
  have hPB₁' : R.S.numericalIntersectionBilinForm R.hreg
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg P)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg B₁.val) = 1 := by
    rw [curveClass_pairing_contact, contactVector_apply, hPB₁, Int.cast_one]
  have hB₁P' : R.S.numericalIntersectionBilinForm R.hreg
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg B₁.val)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg P) = 1 := by
    rw [hsymm.eq, hPB₁']
  have hPB₂' : R.S.numericalIntersectionBilinForm R.hreg
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg P)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg B₂.val) = 1 := by
    rw [curveClass_pairing_contact, contactVector_apply, hPB₂, Int.cast_one]
  have hB₂P' : R.S.numericalIntersectionBilinForm R.hreg
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg B₂.val)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg P) = 1 := by
    rw [hsymm.eq, hPB₂']
  unfold ResolutionDatum.Ksq
  rw [hK]
  simp only [LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right,
    LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right, hCC, hB₁B₁, hB₂B₂, hPP, hCB₁', hB₁C', hCB₂', hB₂C', hB₁B₂',
    hB₂B₁', hPC', hCP', hPB₁', hB₁P', hPB₂', hB₂P']
  ring

include hP hCB₁ hCB₂ hB₁B₂ hne₁ hne₂ hne₃ hwC hwB₁ hPC hPB₁ hPB₂ hK in
/-- Noether's formula and the Picard rank: `ρ(S) = 10 - K_S² = β + 7`, so the number of
exceptional curves is `β + 6` (manuscript line 1508). -/
theorem card_vertices (p : ℕ) [CharP k p] (hp : 0 < p) :
    (Fintype.card R.Vertices : ℚ) = R.w B₂ + 6 := by
  have hN := R.hmin.noetherRelation_of_kltDelPezzo R.hDP R.hrank p hp R.KS R.eKS
  change R.S.intersectionPairing R.hreg R.KS R.KS + (R.S.picardRank : ℤ) = 10 at hN
  have hKsq := R.Ksq_eq_intersectionPairing
  rw [Ksq_eq R C B₁ B₂ P hP hCB₁ hCB₂ hB₁B₂ hne₁ hne₂ hne₃ hwC hwB₁ hPC hPB₁ hPB₂ hK] at hKsq
  have hρ := R.hmin.picardRank_eq_of_klt R.hklt p hp
  rw [R.hrank] at hρ
  have h6 : Nat.card (ActualExceptionalIncidence.Vertices R.π) = Fintype.card R.Vertices :=
    Nat.card_eq_fintype_card
  rw [h6] at hρ
  have hN' : (R.S.intersectionPairing R.hreg R.KS R.KS : ℚ) + (R.S.picardRank : ℚ) = 10 := by
    exact_mod_cast hN
  have hρ' : (R.S.picardRank : ℚ) = 1 + (Fintype.card R.Vertices : ℚ) := by
    exact_mod_cast hρ
  linarith

/-! ### The block decomposition of `A` along `{C, B₁, B₂} ⊔ F` -/

/-- The splitting map `Fin 3 ⊕ F → D`. -/
def splitFun : Fin 3 ⊕ forestSet R C B₁ B₂ → R.Vertices :=
  Sum.elim (core R C B₁ B₂) Subtype.val

include hne₁ hne₂ hne₃ in
theorem splitFun_bijective : Function.Bijective (splitFun R C B₁ B₂) := by
  constructor
  · rintro (i | x) (j | y) h
    · simp only [splitFun, Sum.elim_inl] at h
      rw [core_injective R C B₁ B₂ hne₁ hne₂ hne₃ h]
    · simp only [splitFun, Sum.elim_inl, Sum.elim_inr] at h
      exact absurd h (core_ne_forest R C B₁ B₂ i y)
    · simp only [splitFun, Sum.elim_inl, Sum.elim_inr] at h
      exact absurd h.symm (core_ne_forest R C B₁ B₂ j x)
    · simp only [splitFun, Sum.elim_inr] at h
      rw [Subtype.ext h]
  · intro v
    by_cases h1 : v = C
    · exact ⟨Sum.inl 0, by simp [splitFun, core, h1]⟩
    by_cases h2 : v = B₁
    · exact ⟨Sum.inl 1, by simp [splitFun, core, h2]⟩
    by_cases h3 : v = B₂
    · exact ⟨Sum.inl 2, by simp [splitFun, core, h3]⟩
    exact ⟨Sum.inr ⟨v, h1, h2, h3⟩, rfl⟩

/-- The splitting equivalence `Fin 3 ⊕ F ≃ D`. -/
def splitEquiv (hne₁ : C ≠ B₁) (hne₂ : C ≠ B₂) (hne₃ : B₁ ≠ B₂) :
    Fin 3 ⊕ forestSet R C B₁ B₂ ≃ R.Vertices :=
  Equiv.ofBijective _ (splitFun_bijective R C B₁ B₂ hne₁ hne₂ hne₃)

/-- The principal submatrix of `A` on the forest. -/
def forestMatrix : Matrix (forestSet R C B₁ B₂) (forestSet R C B₁ B₂) ℚ :=
  R.A.submatrix Subtype.val Subtype.val

include hP hCB₁ hCB₂ hB₁B₂ hwC hwB₁ hK in
/-- `A` is block diagonal along `{C, B₁, B₂} ⊔ F`, with core block `diag(2, 3, β)`. -/
theorem A_submatrix_splitEquiv :
    R.A.submatrix (splitEquiv R C B₁ B₂ hne₁ hne₂ hne₃) (splitEquiv R C B₁ B₂ hne₁ hne₂ hne₃) =
      Matrix.fromBlocks (Matrix.diagonal ![2, 3, R.w B₂]) 0 0 (forestMatrix R C B₁ B₂) := by
  have hiso := isolated_core R C B₁ B₂ P hP hCB₁ hCB₂ hB₁B₂ hK
  have hA : ∀ i j : R.Vertices, R.A i j = -R.M i j := fun i j => rfl
  ext (i | x) (j | y)
  · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, splitEquiv,
      Equiv.ofBijective_apply, splitFun, Sum.elim_inl, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, R.A_diag]
      fin_cases i <;> simp [core, hwC, hwB₁]
    · rw [if_neg hij, hA, M_eq_zero_of_not_adj R
        (fun h => hij (core_injective R C B₁ B₂ hne₁ hne₂ hne₃ h)) (hiso i _), neg_zero]
  · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, splitEquiv,
      Equiv.ofBijective_apply, splitFun, Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply]
    rw [hA, M_eq_zero_of_not_adj R (core_ne_forest R C B₁ B₂ i y) (hiso i _), neg_zero]
  · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, splitEquiv,
      Equiv.ofBijective_apply, splitFun, Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply]
    rw [hA, M_symm, M_eq_zero_of_not_adj R (core_ne_forest R C B₁ B₂ j x) (hiso j _), neg_zero]
  · rfl

include hP hCB₁ hCB₂ hB₁B₂ hne₁ hne₂ hne₃ hwC hwB₁ hK in
/-- `det A = 6β · det A_F` (manuscript line 1514, core determinant `2·3·β`). -/
theorem A_det_eq [DecidableEq R.Vertices] [DecidableEq (forestSet R C B₁ B₂)]
    [Fintype (forestSet R C B₁ B₂)] :
    R.A.det = 6 * R.w B₂ * (forestMatrix R C B₁ B₂).det := by
  rw [← Matrix.det_submatrix_equiv_self (splitEquiv R C B₁ B₂ hne₁ hne₂ hne₃) R.A,
    A_submatrix_splitEquiv R C B₁ B₂ P hP hCB₁ hCB₂ hB₁B₂ hne₁ hne₂ hne₃ hwC hwB₁ hK,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

include hP hK in
/-- The forest block of `A` is the (rational) graph Cartan matrix of the induced forest. -/
theorem forestMatrix_eq_graphCartanMatrix [DecidableEq R.Vertices] [DecidableRel R.graph.Adj]
    [DecidableEq (forestSet R C B₁ B₂)]
    [DecidableRel (R.graph.induce (forestSet R C B₁ B₂)).Adj] :
    forestMatrix R C B₁ B₂ =
      (graphCartanMatrix (R.graph.induce (forestSet R C B₁ B₂))).map (Int.cast : ℤ → ℚ) := by
  ext x y
  have hA := congr_fun (congr_fun R.A_eq_graphWeightMatrix x.val) y.val
  rw [graphWeightMatrix_apply] at hA
  have hx : R.w x.val = 2 :=
    (other_vertex R C B₁ B₂ P hP hK x.val x.property.1 x.property.2.1 x.property.2.2).1
  simp only [forestMatrix, Matrix.submatrix_apply, Matrix.map_apply, graphCartanMatrix]
  rw [hA]
  have hadj : (R.graph.induce (forestSet R C B₁ B₂)).Adj x y ↔ R.graph.Adj x.val y.val := Iff.rfl
  by_cases hxy : x = y
  · subst hxy
    simp [hx]
  · have hxy' : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
    by_cases had : R.graph.Adj x.val y.val
    · simp [hxy, hxy', had, hadj]
    · simp [hxy, hxy', had, hadj]

/-! ### The vector `A⁻¹ p` and the Green quantity `g = pᵀ A⁻¹ p` -/

section Inverse

variable [DecidableEq R.Vertices]

/-- The explicit solution `u` of `A u = p`: `1/2, 1/3, 1/β` at `C, B₁, B₂`, zero elsewhere. -/
def uvec : R.Vertices → ℚ := fun v =>
  if v = C then 1 / 2 else if v = B₁ then 1 / 3 else if v = B₂ then 1 / R.w B₂ else 0

include hP hCB₁ hCB₂ hB₁B₂ hne₁ hne₂ hne₃ hwC hwB₁ hwB₂ hPC hPB₁ hPB₂ hK in
theorem A_mulVec_uvec : R.A *ᵥ uvec R C B₁ B₂ = contact R P := by
  classical
  have hisoC := isolated_C R C B₁ B₂ P hP hCB₁ hCB₂ hK
  have hisoB₁ := isolated_B₁ R C B₁ B₂ P hP hCB₁ hB₁B₂ hK
  have hisoB₂ := isolated_B₂ R C B₁ B₂ P hP hCB₂ hB₁B₂ hK
  have hβ : R.w B₂ ≠ 0 := by linarith
  funext v
  rw [A_mulVec_apply, contact_apply]
  by_cases hvC : v = C
  · rw [Finset.sum_eq_zero (fun u hu => absurd ((R.graph.mem_neighborFinset v u).1 hu)
      (hvC ▸ hisoC u)), sub_zero, hvC, hPC, hwC]
    simp [uvec]
  by_cases hvB₁ : v = B₁
  · rw [Finset.sum_eq_zero (fun u hu => absurd ((R.graph.mem_neighborFinset v u).1 hu)
      (hvB₁ ▸ hisoB₁ u)), sub_zero, hvB₁, hPB₁, hwB₁]
    simp [uvec, hne₁.symm]
  by_cases hvB₂ : v = B₂
  · rw [Finset.sum_eq_zero (fun u hu => absurd ((R.graph.mem_neighborFinset v u).1 hu)
      (hvB₂ ▸ hisoB₂ u)), sub_zero, hvB₂, hPB₂]
    simp only [uvec, if_neg hne₂.symm, if_neg hne₃.symm, if_pos rfl, Int.cast_one]
    field_simp
  · have h0 := (other_vertex R C B₁ B₂ P hP hK v hvC hvB₁ hvB₂).2.2.2.2
    have hu : uvec R C B₁ B₂ v = 0 := by simp [uvec, hvC, hvB₁, hvB₂]
    have hsum : ∑ u ∈ R.graph.neighborFinset v, uvec R C B₁ B₂ u = 0 := by
      refine Finset.sum_eq_zero (fun u hu => ?_)
      have hadj := (R.graph.mem_neighborFinset v u).1 hu
      have huC : u ≠ C := fun h => hisoC v (h ▸ hadj.symm)
      have huB₁ : u ≠ B₁ := fun h => hisoB₁ v (h ▸ hadj.symm)
      have huB₂ : u ≠ B₂ := fun h => hisoB₂ v (h ▸ hadj.symm)
      simp [uvec, huC, huB₁, huB₂]
    rw [hsum, hu, h0]
    simp

include hP hCB₁ hCB₂ hB₁B₂ hne₁ hne₂ hne₃ hwC hwB₁ hwB₂ hPC hPB₁ hPB₂ hK in
/-- `g = pᵀ A⁻¹ p = 1/2 + 1/3 + 1/β` (the manuscript's `pᵀA⁻¹p` for three isolated contacts). -/
theorem green_eq :
    dotProduct (contact R P) (R.A⁻¹ *ᵥ contact R P) = 1 / 2 + 1 / 3 + 1 / R.w B₂ := by
  classical
  have hu : R.A⁻¹ *ᵥ contact R P = uvec R C B₁ B₂ := by
    rw [← A_mulVec_uvec R C B₁ B₂ P hP hCB₁ hCB₂ hB₁B₂ hne₁ hne₂ hne₃ hwC hwB₁ hwB₂ hPC hPB₁
      hPB₂ hK, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul R.A (A_det_isUnit R),
      Matrix.one_mulVec]
  rw [hu]
  unfold dotProduct
  rw [sum_eq_add_add_add _ C B₁ B₂ hne₁ hne₂ hne₃ (fun x hx1 hx2 hx3 => by
    have h0 := (other_vertex R C B₁ B₂ P hP hK x hx1 hx2 hx3).2.2.2.2
    rw [contact_apply, h0, Int.cast_zero, zero_mul])]
  rw [contact_apply, contact_apply, contact_apply, hPC, hPB₁, hPB₂]
  simp [uvec, hne₁, hne₂, hne₃, hne₁.symm, hne₂.symm, hne₃.symm]

end Inverse

/-! ### Components of the forest -/

/-- The exceptional dual graph is a forest (union). -/
theorem graph_isAcyclic' : R.graph.IsAcyclic :=
  (R.hmin.exceptional_forest_and_singular_count_from_klt R.hklt).2.2.1

/-- Every induced subgraph of the exceptional forest is a forest. -/
theorem induce_isAcyclic' (s : Set R.Vertices) : (R.graph.induce s).IsAcyclic :=
  KltDP.Lattices.SmallForestComponents.isAcyclic_induce R.graph (graph_isAcyclic' R) s

/-- With at least eight singular points, the forest `F` has at least five connected components:
every component of `D` contains a core vertex or a vertex of `F`, so the components of `D` are
covered by the three core classes and the components of `F` (manuscript lines 1509–1510). -/
theorem five_le_components (h8 : 8 ≤ R.X.singularPoints.card) :
    5 ≤ Nat.card (R.graph.induce (forestSet R C B₁ B₂)).ConnectedComponent := by
  classical
  obtain ⟨_, hcount, _, _⟩ := R.hmin.exceptional_forest_and_singular_count_from_klt R.hklt
  let s := forestSet R C B₁ B₂
  let G := R.graph.induce s
  let ι : G →g R.graph := ⟨Subtype.val, fun h => h⟩
  let φ : G.ConnectedComponent ⊕ Fin 3 → R.graph.ConnectedComponent :=
    Sum.elim (fun c => c.map ι) (fun i => R.graph.connectedComponentMk (core R C B₁ B₂ i))
  have hφ : Function.Surjective φ := by
    intro c
    refine SimpleGraph.ConnectedComponent.ind (fun v => ?_) c
    by_cases hv : v ∈ s
    · exact ⟨Sum.inl (G.connectedComponentMk ⟨v, hv⟩), rfl⟩
    · simp only [s, forestSet, Set.mem_setOf_eq, not_and, not_not] at hv
      by_cases h1 : v = C
      · refine ⟨Sum.inr 0, ?_⟩
        show R.graph.connectedComponentMk (core R C B₁ B₂ 0) = R.graph.connectedComponentMk v
        rw [h1]; rfl
      by_cases h2 : v = B₁
      · refine ⟨Sum.inr 1, ?_⟩
        show R.graph.connectedComponentMk (core R C B₁ B₂ 1) = R.graph.connectedComponentMk v
        rw [h2]; rfl
      · refine ⟨Sum.inr 2, ?_⟩
        show R.graph.connectedComponentMk (core R C B₁ B₂ 2) = R.graph.connectedComponentMk v
        rw [hv h1 h2]; rfl
  have hcard := Fintype.card_le_of_surjective φ hφ
  rw [Fintype.card_sum, Fintype.card_fin] at hcard
  have h1 : Fintype.card G.ConnectedComponent =
      Nat.card (R.graph.induce (forestSet R C B₁ B₂)).ConnectedComponent :=
    Fintype.card_eq_nat_card
  have h2 : Fintype.card R.graph.ConnectedComponent =
      Nat.card (ActualExceptionalIncidence.graph R.π).ConnectedComponent :=
    Fintype.card_eq_nat_card
  omega

end Configuration

/-! ### Proposition 5.5 -/

/-- **Proposition 5.5 (`prop:zero-adjoint`, manuscript lines 1483–1541).** Let `R` be the
resolution datum of a rank-one klt del Pezzo surface in characteristic `p > 2`. Suppose
`C, B₁, B₂ ⊂ D` are pairwise disjoint exceptional curves with `C² = -2`, `B₁² = -3`,
`B₂² = -β` (`β ≥ 3`), `P ⊄ D` is a `(-1)`-curve with `P·C = P·B₁ = P·B₂ = 1`, and
`-K_S ≡ C + B₁ + B₂ + 2P` numerically. Then `X` has at most seven singular points. -/
theorem zeroAdjointBound (p : ℕ) [CharP k p] (hp : 2 < p)
    (C B₁ B₂ : R.Vertices) (P : R.S.PrimeCurve) (hP : R.IsExteriorMinusOne P)
    (hCB₁ : ¬ R.graph.Adj C B₁) (hCB₂ : ¬ R.graph.Adj C B₂) (hB₁B₂ : ¬ R.graph.Adj B₁ B₂)
    (hne₁ : C ≠ B₁) (hne₂ : C ≠ B₂) (hne₃ : B₁ ≠ B₂)
    (hwC : R.w C = 2) (hwB₁ : R.w B₁ = 3) (hwB₂ : 3 ≤ R.w B₂)
    (hPC : R.contact P C = 1) (hPB₁ : R.contact P B₁ = 1) (hPB₂ : R.contact P B₂ = 1)
    (hK : R.Knum = -(DisjointNegativeCurvesRank.curveClass R.S R.hreg C.val +
      DisjointNegativeCurvesRank.curveClass R.S R.hreg B₁.val +
      DisjointNegativeCurvesRank.curveClass R.S R.hreg B₂.val +
      (2 : ℚ) • DisjointNegativeCurvesRank.curveClass R.S R.hreg P)) :
    R.X.singularPoints.card ≤ 7 := by
  classical
  by_contra h8
  push_neg at h8
  have hp0 : 0 < p := by omega
  -- `β ∈ {3, 4, 5}`
  obtain ⟨β, hβ, hβ3, hβ5⟩ :=
    exists_beta R C B₁ B₂ P hP hCB₁ hCB₂ hB₁B₂ hne₁ hne₂ hne₃ hwC hwB₁ hwB₂ hPC hPB₁ hPB₂ hK
  have hβQ : (3 : ℚ) ≤ β := by exact_mod_cast hβ3
  have hβ0 : (β : ℚ) ≠ 0 := by positivity
  -- the forest `F = forestSet R C B₁ B₂` and its induced graph `R.graph.induce F`
  letI : Fintype (forestSet R C B₁ B₂) := Fintype.ofFinite _
  letI : Fintype (R.graph.induce (forestSet R C B₁ B₂)).ConnectedComponent := Fintype.ofFinite _
  letI : ∀ c : (R.graph.induce (forestSet R C B₁ B₂)).ConnectedComponent, Fintype c.supp :=
    fun c => Fintype.ofFinite _
  -- `#F = β + 3`
  have hcardV : (Fintype.card R.Vertices : ℚ) = R.w B₂ + 6 :=
    card_vertices R C B₁ B₂ P hP hCB₁ hCB₂ hB₁B₂ hne₁ hne₂ hne₃ hwC hwB₁ hPC hPB₁ hPB₂ hK p hp0
  have hcardV' : Fintype.card R.Vertices = β + 6 := by
    rw [hβ] at hcardV
    exact_mod_cast hcardV
  have hcardF : Fintype.card (forestSet R C B₁ B₂) = β + 3 := by
    have h := Fintype.card_congr (splitEquiv R C B₁ B₂ hne₁ hne₂ hne₃)
    rw [Fintype.card_sum, Fintype.card_fin] at h
    omega
  -- at least five components
  have hcomp : 5 ≤ Fintype.card (R.graph.induce (forestSet R C B₁ B₂)).ConnectedComponent := by
    rw [Fintype.card_eq_nat_card]
    exact five_le_components R C B₁ B₂ (by omega)
  -- the ADE decomposition of the forest
  obtain ⟨counts, e, hrank, hcomps, hGram, hdet⟩ :=
    smallADEForest_decomposition (R.graph.induce (forestSet R C B₁ B₂))
      (induce_isAcyclic' R (forestSet R C B₁ B₂)) (by omega) hcomp
  -- the index equation `I² = det A · (g - 1) = (6 - β) det A_F`
  obtain ⟨hI, hnodes, -⟩ := fullPicardIndexObstruction R p hp P hP.1 hP.2
  set I : ℕ := (R.S.exceptionalExteriorPicardSpan R.π R.hreg P).toAddSubgroup.index with hIdef
  have hdetA := A_det_eq R C B₁ B₂ P hP hCB₁ hCB₂ hB₁B₂ hne₁ hne₂ hne₃ hwC hwB₁ hK
  have hg := green_eq R C B₁ B₂ P hP hCB₁ hCB₂ hB₁B₂ hne₁ hne₂ hne₃ hwC hwB₁ hwB₂ hPC hPB₁ hPB₂ hK
  have hFM := forestMatrix_eq_graphCartanMatrix R C B₁ B₂ P hP hK
  have hdetF : (forestMatrix R C B₁ B₂).det = (counts.rootDet : ℚ) := by
    rw [hFM]
    rw [show ((graphCartanMatrix (R.graph.induce (forestSet R C B₁ B₂))).map
        (Int.cast : ℤ → ℚ)).det =
      (((graphCartanMatrix (R.graph.induce (forestSet R C B₁ B₂))).det : ℤ) : ℚ) from
        (Int.cast_det _).symm, hdet]
    norm_cast
  have hsqQ : ((I : ℕ) : ℚ) ^ 2 = ((6 - β : ℕ) : ℚ) * (counts.rootDet : ℚ) := by
    rw [hI, hdetA, hg, hdetF, Nat.cast_sub (by omega), hβ]
    push_cast
    field_simp
    ring
  have hsq : gammaDet β counts = I ^ 2 := by
    rw [gammaDet_eq]
    exact_mod_cast hsqQ.symm
  have hlt := gammaDet_square_factorization_lt_nodes β I counts hβ3 hβ5 (hrank.trans hcardF)
    (by rw [hcomps]; exact hcomp) hsq
  -- the `t = counts.a1` isolated nodes of `F`
  have hinj : Function.Injective (fun i : Fin counts.a1 => (transportedNode counts e i).val) :=
    fun i j h => transportedNode_injective counts e (Subtype.ext h)
  obtain ⟨N, hN⟩ : ∃ N : Finset R.Vertices,
      N = Finset.univ.image (fun i : Fin counts.a1 => (transportedNode counts e i).val) :=
    ⟨_, rfl⟩
  have hNcard : N.card = counts.a1 := by
    rw [hN, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hmemN : ∀ W ∈ N, W ∈ forestSet R C B₁ B₂ := by
    rw [hN]
    intro W hW
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hW
    exact (transportedNode counts e i).property
  have hw : ∀ W ∈ N, R.w W = 2 := fun W hW =>
    (other_vertex R C B₁ B₂ P hP hK W (hmemN W hW).1 (hmemN W hW).2.1 (hmemN W hW).2.2).1
  have hPN : ∀ W ∈ N, P.intersectionNumber (R.S.primeCurveCartier R.hreg W.val) = 0 :=
    fun W hW =>
      (other_vertex R C B₁ B₂ P hP hK W (hmemN W hW).1 (hmemN W hW).2.1 (hmemN W hW).2.2).2.2.2.2
  have hiso : ∀ W ∈ N, ∀ y, ¬ R.graph.Adj W y := by
    rw [hN]
    intro W hW y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hW
    have hnot := transportedNode_not_mem_support (R.graph.induce (forestSet R C B₁ B₂)) counts e
      hGram i
    by_cases hys : y ∈ forestSet R C B₁ B₂
    · exact hnot ((SimpleGraph.mem_support (R.graph.induce (forestSet R C B₁ B₂))).mpr
        ⟨⟨y, hys⟩, hy⟩)
    · exact isolated_of_not_mem_forestSet R C B₁ B₂ P hP hCB₁ hCB₂ hB₁B₂ hK y hys _ hy.symm
  have hle := hnodes N hw hiso hPN
  rw [hNcard] at hle
  omega

/-- **Proposition 5.5, Picard-class form.** The same conclusion when the adjoint identity is
given in `Pic S`: `K_S + C + B₁ + B₂ + 2P ∼ 0`, i.e. `-K_S ∼ C + B₁ + B₂ + 2P` (the form in
which Theorem 7.1 produces the configuration when the extra curve `R'` is absent). The numerical
identity follows by applying `picardNumericalMap`. -/
theorem zeroAdjointBound_pic (p : ℕ) [CharP k p] (hp : 2 < p)
    (C B₁ B₂ : R.Vertices) (P : R.S.PrimeCurve) (hP : R.IsExteriorMinusOne P)
    (hCB₁ : ¬ R.graph.Adj C B₁) (hCB₂ : ¬ R.graph.Adj C B₂) (hB₁B₂ : ¬ R.graph.Adj B₁ B₂)
    (hne₁ : C ≠ B₁) (hne₂ : C ≠ B₂) (hne₃ : B₁ ≠ B₂)
    (hwC : R.w C = 2) (hwB₁ : R.w B₁ = 3) (hwB₂ : 3 ≤ R.w B₂)
    (hPC : R.contact P C = 1) (hPB₁ : R.contact P B₁ = 1) (hPB₂ : R.contact P B₂ = 1)
    (hK : cartierPicardClass R.S.toScheme R.KS * R.curvePic C.val * R.curvePic B₁.val *
      R.curvePic B₂.val * R.curvePic P ^ 2 = 1) :
    R.X.singularPoints.card ≤ 7 := by
  refine zeroAdjointBound R p hp C B₁ B₂ P hP hCB₁ hCB₂ hB₁B₂ hne₁ hne₂ hne₃ hwC hwB₁ hwB₂
    hPC hPB₁ hPB₂ ?_
  have h := congrArg (fun x => R.S.picardNumericalMap (Additive.ofMul x)) hK
  simp only [ofMul_mul, ofMul_pow, ofMul_one, map_add, map_nsmul, map_zero] at h
  have h2 : (2 : ℚ) • DisjointNegativeCurvesRank.curveClass R.S R.hreg P =
      2 • DisjointNegativeCurvesRank.curveClass R.S R.hreg P := by
    rw [two_smul, two_nsmul]
  rw [h2]
  apply eq_neg_of_add_eq_zero_left
  rw [← add_assoc, ← add_assoc, ← add_assoc]
  exact h

end KltDP.Manuscript.S05

#print axioms KltDP.Manuscript.S05.zeroAdjointBound
#print axioms KltDP.Manuscript.S05.zeroAdjointBound_pic

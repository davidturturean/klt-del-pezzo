import KltDP.Manuscript.S07.Interfaces
import KltDP.Manuscript.S03.NefThreshold
import KltDP.Manuscript.S04.ExcessContact
import KltDP.Manuscript.S04.OneComponentReplacement
import KltDP.Manuscript.S05.ZeroAdjoint
import KltDP.Manuscript.S06.MultipleContact
import KltDP.Manuscript.S06.AdjacentContactAdjoint
import KltDP.Manuscript.S06.ThreeContactDescent
import KltDP.Manuscript.S06.CubicAdjoint

/-!
# Manuscript Theorem 7.1: a single exterior adjoint curve for a minimal counterexample

Source: `source/manuscript.tex`, lines 2324–2445, label `thm:adjoint-reduction`.

For the resolution datum of a minimal counterexample (characteristic `p > 2`) and a shortest
exterior `(-1)`-curve `P`, the contacts of `P` with the exceptional divisor form the single
exterior adjoint configuration `AdjointConfiguration R P`: a weight-two contact `C`, two
higher-weight contacts `B₁, B₂` of weights `(3, β)`, `β ∈ {3, 4, 5}`, and an exterior `(-1)`-curve
`R' ∼ K_S + C + B₁ + B₂ + 2P` disjoint from `C ∪ B₁ ∪ B₂ ∪ P` with `L·R' = 2ℓ - v`.

The proof follows the manuscript sentence by sentence (see the section headers below); the two
inputs still being formalized, Theorem 7.5 (`TwoContactRulingHyp`) and Theorem 4.6
(`IsolatedExchangeHyp`), are explicit hypotheses of `singleExteriorAdjointReduction_of`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.DisjointNegativeCurvesRank
open KltDP.Manuscript KltDP.Manuscript.S02 KltDP.Manuscript.S04 KltDP.Manuscript.S06Adj
open KltDP.Manuscript.S04.Replacement

universe u

namespace KltDP.Manuscript.S07

/-! ### A graph-theoretic lemma: cycles through a distinguished vertex -/

section Graph

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (u : V)

/-- A graph is acyclic as soon as (1) it has no cycle avoiding the vertex `u` and (2) there is
no walk avoiding `u` between two distinct neighbours of `u`. -/
theorem isAcyclic_of_avoiding
    (h₁ : ∀ (v : V) (c : G.Walk v v), c.IsCycle → u ∉ c.support → False)
    (h₂ : ∀ (a b : V), G.Adj u a → G.Adj u b → a ≠ b → ∀ (q : G.Walk a b),
      u ∉ q.support → False) :
    G.IsAcyclic := by
  intro v c hc
  by_cases hu : u ∈ c.support
  · have hc' := hc.rotate hu
    generalize c.rotate hu = c' at hc'
    cases c' with
    | nil => exact SimpleGraph.Walk.IsCycle.not_of_nil hc'
    | @cons _ a _ h q =>
      obtain ⟨hq, hedge⟩ := (SimpleGraph.Walk.cons_isCycle_iff q h).1 hc'
      have hrev : q.reverse.IsPath := hq.reverse
      have hrevedges : q.reverse.edges = q.edges.reverse := q.edges_reverse
      generalize q.reverse = r at hrev hrevedges
      cases r with
      | nil => exact G.loopless _ h
      | @cons _ b _ h' q' =>
        obtain ⟨hq', hu'⟩ := (SimpleGraph.Walk.cons_isPath_iff h' q').1 hrev
        have hab : b ≠ a := by
          intro hba
          apply hedge
          have hmem : s(u, b) ∈ q.edges.reverse := by
            rw [← hrevedges, SimpleGraph.Walk.edges_cons]
            exact List.mem_cons_self
          rw [hba] at hmem
          exact List.mem_reverse.1 hmem
        exact h₂ b a h' h hab q' hu'
  · exact h₁ v c hc hu

end Graph

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)

local notation "𝒞" => DisjointNegativeCurvesRank.curveClass R.S R.hreg
local notation "𝔅" => R.S.numericalIntersectionBilinForm R.hreg

/-! ### The SNC-forest hypothesis of Theorem 4.5 for `P + (D - C)`

Manuscript lines 2400–2402: "deleting `C` leaves `P + (D - C)` an SNC forest: the remaining
contacts are simple and lie in distinct exceptional components." -/

section Forest

/-- The incidence graph of the family `P + (D - C)` is acyclic when the vertices `≠ C` met by
`P` lie in pairwise distinct components of the exceptional forest. -/
theorem famG_isAcyclic (C : R.Vertices) (P : R.S.PrimeCurve) (hP : ¬ IsExceptionalCurve R.π P)
    (hsep : ∀ i j : R.Vertices, i ≠ C → j ≠ C → R.contact P i ≠ 0 → R.contact P j ≠ 0 →
      i ≠ j → ¬ R.graph.Reachable i j) :
    (curveIncidenceGraph (famG R C P)).IsAcyclic := by
  classical
  set G := curveIncidenceGraph (famG R C P) with hG
  -- the graph with the edges at `P` removed
  let G₀ : SimpleGraph (D0 R C ⊕ Unit) :=
    { Adj := fun a b => G.Adj a b ∧ a ≠ Sum.inr () ∧ b ≠ Sum.inr ()
      symm := fun a b ⟨h, ha, hb⟩ => ⟨h.symm, hb, ha⟩
      loopless := fun a ⟨h, _, _⟩ => G.loopless a h }
  -- the injective map to the vertices of `D`, sending `P` to `C`
  let φ : D0 R C ⊕ Unit → R.Vertices := Sum.elim (fun i => i.1) (fun _ => C)
  have hφinj : Function.Injective φ := by
    rintro (i | u) (j | u') h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exact absurd h i.2
    · exact absurd h.symm j.2
    · cases u; cases u'; rfl
  let ψ : G₀ →g R.graph :=
    { toFun := φ
      map_rel' := by
        rintro (i | u) (j | u') ⟨hadj, ha, hb⟩
        · obtain ⟨hne, hmeet⟩ := hadj
          refine ⟨fun h => hne (congrArg Sum.inl (Subtype.ext h)), ?_⟩
          exact hmeet
        · exact absurd rfl (by cases u'; exact hb)
        · exact absurd rfl (by cases u; exact ha)
        · exact absurd rfl (by cases u; exact ha) }
  -- walks avoiding `P` transfer to `G₀`
  have htransfer : ∀ {a b : D0 R C ⊕ Unit} (q : G.Walk a b), Sum.inr () ∉ q.support →
      ∀ e ∈ q.edges, e ∈ G₀.edgeSet := by
    intro a b q hq e he
    revert he
    induction e using Sym2.ind with
    | h x y =>
      intro he
      rw [SimpleGraph.mem_edgeSet]
      refine ⟨q.adj_of_mem_edges he, ?_, ?_⟩
      · intro hx
        apply hq
        rw [← hx]
        exact q.fst_mem_support_of_mem_edges he
      · intro hy
        apply hq
        rw [← hy]
        exact q.snd_mem_support_of_mem_edges he
  have hreach : ∀ {a b : D0 R C ⊕ Unit} (q : G.Walk a b), Sum.inr () ∉ q.support →
      R.graph.Reachable (φ a) (φ b) :=
    fun q hq => ⟨(q.transfer G₀ (htransfer q hq)).map ψ⟩
  apply isAcyclic_of_avoiding G (Sum.inr ())
  · intro v c hc hu
    have hc₀ := hc.transfer (htransfer c hu)
    have hcyc := (SimpleGraph.Walk.map_isCycle_iff_of_injective (f := ψ)
      (p := c.transfer G₀ (htransfer c hu)) hφinj).2 hc₀
    exact KltDP.Manuscript.S05.graph_isAcyclic' R _ hcyc
  · intro a b ha hb hab q hq
    -- the neighbours of `P` are the vertices `≠ C` with nonzero contact
    have hnbr : ∀ x, G.Adj (Sum.inr ()) x → ∃ i : D0 R C, x = Sum.inl i ∧ R.contact P i.1 ≠ 0 := by
      intro x hx
      rcases x with i | u'
      · refine ⟨i, rfl, ?_⟩
        rw [hG, curveIncidenceGraph_adj_iff_pairing_pos R.S R.hreg (famG R C P)
          (famG_injective R C P hP)] at hx
        obtain ⟨-, hpos⟩ := hx
        intro h0
        have hzero : R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg P)
            (R.S.primeCurveCartier R.hreg i.1.1) = 0 := by
          rw [PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber]
          exact h0
        simp only [famG_inl, famG_inr] at hpos
        rw [hzero] at hpos
        exact lt_irrefl _ hpos
      · cases u'
        exact absurd hx (G.loopless _)
    obtain ⟨i, rfl, hi⟩ := hnbr a ha
    obtain ⟨j, rfl, hj⟩ := hnbr b hb
    have hij : i.1 ≠ j.1 := fun h => hab (congrArg Sum.inl (Subtype.ext h))
    exact hsep i.1 j.1 i.2 j.2 hi hj hij (hreach q hq)

end Forest

/-! ### Remainder helpers

The recurring argument of the manuscript (lines 2338–2340, 2372–2374, 2412–2414, 2424–2429):
an effective divisor `N ∼ K_S + A` whose exterior components would be too short is supported on
`D`; if moreover `N · A = 0` then `N² = K_S · N ≥ 0`, so `N = 0` by negative definiteness. -/

/-- Components of an effective divisor of `L`-degree `< ℓ` are exceptional (Lemma 3.3 (f)). -/
theorem exceptional_of_LdegW_lt (hrho : 2 < R.S.picardRank) {P : R.S.PrimeCurve}
    (hP : R.IsShortestExteriorMinusOne P) (N : R.S.WeilDivisor) (hN : EffectiveDivisor N)
    (hL : LdegW R N < R.Ldeg P) : ∀ Q, N Q ≠ 0 → IsExceptionalCurve R.π Q := by
  intro Q hQ
  refine Classical.byContradiction (fun hext => ?_)
  exact hQ (KltDP.Manuscript.S03.effective_small_degree_supported_on_exceptional R hrho P hP N hN
    hL Q hext)

/-- `K_S · Q ≥ 0` for an exceptional curve `Q`. -/
theorem Kdeg_nonneg_of_exceptional (Q : R.S.PrimeCurve) (hQ : IsExceptionalCurve R.π Q) :
    (0 : ℚ) ≤ R.Kdeg Q := by
  have h := R.Kdeg_exceptional ⟨Q, hQ⟩
  have h2 := R.two_le_w ⟨Q, hQ⟩
  rw [h]
  unfold ResolutionDatum.q
  linarith

/-- `N · K_S = Σ_Q N_Q (K_S · Q)`. -/
theorem pairing_numW_Knum_eq (N : R.S.WeilDivisor) :
    𝔅 (numW R N) R.Knum = ∑ Q ∈ N.support, (N Q : ℚ) * (R.Kdeg Q : ℚ) := by
  rw [numW_eq_sum, LinearMap.BilinForm.sum_left]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  simp only [LinearMap.BilinForm.smul_left, smul_eq_mul]
  rw [(R.S.numericalIntersectionBilinForm_isSymm R.hreg).eq, Knum_pairing_cc]

/-- An effective divisor supported on the exceptional curves with `N ≡ K_S + a` and `N · a = 0`
vanishes (`N² = K_S · N ≥ 0` and negative definiteness). -/
theorem eq_zero_of_exceptional_adjoint (N : R.S.WeilDivisor) (hN : EffectiveDivisor N)
    (hexc : ∀ Q, N Q ≠ 0 → IsExceptionalCurve R.π Q) (a : R.S.NumericalClassGroup)
    (hnum : numW R N = R.Knum + a) (hNa : 𝔅 (numW R N) a = 0) : N = 0 := by
  apply eq_zero_of_exceptional_of_square_nonneg R N hexc
  have hsq : 𝔅 (numW R N) (numW R N) = 𝔅 (numW R N) R.Knum + 𝔅 (numW R N) a := by
    rw [← LinearMap.BilinForm.add_right, ← hnum]
  rw [hsq, hNa, add_zero, pairing_numW_Knum_eq]
  exact Finset.sum_nonneg (fun Q hQ => mul_nonneg (by exact_mod_cast hN Q)
    (Kdeg_nonneg_of_exceptional R Q (hexc Q (Finsupp.mem_support_iff.mp hQ))))

/-- `Q · N = K_S · Q + Q · A` when `N ∼ K_S + A`. -/
theorem degW_of_linearlyEquivalent_KS_add (N A : R.S.WeilDivisor)
    (h : R.S.LinearlyEquivalent N (R.S.cartierToWeilHom R.KS + A)) (Q : R.S.PrimeCurve) :
    degW R Q N = (R.Kdeg Q : ℚ) + degW R Q A := by
  rw [degW_eq_pairing, numW_eq_of_linearlyEquivalent R h, map_add, numW_KS,
    LinearMap.BilinForm.add_right, (R.S.numericalIntersectionBilinForm_isSymm R.hreg).eq _ R.Knum,
    Knum_pairing_cc, ← degW_eq_pairing]

/-- If every component of `N` is disjoint from `E`, then `E · N = 0`. -/
theorem degW_eq_zero_of_components (E : R.S.PrimeCurve) (N : R.S.WeilDivisor)
    (h : ∀ Q, N Q ≠ 0 → (Q.intersectionNumber (R.S.primeCurveCartier R.hreg E) : ℚ) = 0) :
    degW R E N = 0 := by
  rw [degW_eq_sum]
  refine Finset.sum_eq_zero (fun Q hQ => ?_)
  rw [inter_comm, h Q (Finsupp.mem_support_iff.mp hQ), mul_zero]

/-- The components of an effective `Z` with `E · Z = 0` and `E ∉ Supp Z` are disjoint from
`E` (all terms of `E · Z = Σ Z_Q (E · Q)` are nonnegative). -/
theorem inter_eq_zero_of_degW_eq_zero (E : R.S.PrimeCurve) (Z : R.S.WeilDivisor)
    (hZ : EffectiveDivisor Z) (hZE : Z E = 0) (h0 : degW R E Z = 0) :
    ∀ Q, Z Q ≠ 0 → (E.intersectionNumber (R.S.primeCurveCartier R.hreg Q) : ℚ) = 0 := by
  intro Q hQ
  rw [degW_eq_sum] at h0
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun Q' hQ' => mul_nonneg
    (by exact_mod_cast hZ Q')
    (inter_nonneg R E Q' (fun h => (Finsupp.mem_support_iff.mp hQ') (h ▸ hZE))))).mp h0 Q
    (Finsupp.mem_support_iff.mpr hQ)
  exact (mul_eq_zero.mp hterm).resolve_left (by exact_mod_cast hQ)

/-- The remainder of Lemma 6.3 at a shortest curve `P` vanishes: an exterior component would
have `L`-degree `≤ ℓ - v < ℓ`, and a remainder supported on `D` is zero by negative
definiteness (manuscript lines 2338–2340). -/
theorem adjointRemainder_eq_zero (hrho : 2 < R.S.picardRank) {P : R.S.PrimeCurve}
    (hP : R.IsShortestExteriorMinusOne P) {C H : R.Vertices} {A Z N : R.S.WeilDivisor}
    (hN : AdjointRemainder R P C H A Z N) : N = 0 := by
  have hexc : ∀ Q, N Q ≠ 0 → IsExceptionalCurve R.π Q :=
    exceptional_of_LdegW_lt R hrho hP N hN.effective (by rw [hN.Ldeg_eq]; linarith [R.Lsq_pos])
  have hnum : numW R N = R.Knum + numW R (adjDiv R P C H 1 1 1) := by
    rw [numW_eq_of_linearlyEquivalent R hN.class_eq, map_add, numW_KS]
  refine eq_zero_of_exceptional_adjoint R N hN.effective hexc _ hnum ?_
  rw [(R.S.numericalIntersectionBilinForm_isSymm R.hreg).eq, pairing_numW_eq_sum]
  refine Finset.sum_eq_zero (fun Q hQ => ?_)
  have hQ' : N Q ≠ 0 := Finsupp.mem_support_iff.mp hQ
  obtain ⟨dC, dH, dP⟩ := hN.disjoint Q hQ'
  have hQC : Q ≠ C.val := fun h => hQ' (h ▸ hN.coeff_C)
  have hQH : Q ≠ H.val := fun h => hQ' (h ▸ hN.coeff_H)
  have hQP : Q ≠ P := fun h => hQ' (h ▸ hN.coeff_P)
  rw [degW_adjDiv, inter_eq_zero_of_disjoint R Q C.val hQC dC,
    inter_eq_zero_of_disjoint R Q H.val hQH dH, inter_eq_zero_of_disjoint R Q P hQP dP]
  simp

/-! ### The weight-three double contact (type (U3)) is excluded at a shortest curve

Manuscript lines 2333–2336 with Proposition 6.2 (iii). We derive `-K_S ≡ B + P` directly from
the Riemann–Roch remainder of `A = B + 2P` (Lemma 6.1 (U3) without the "no other contact"
hypothesis) and conclude with `squareOneStructure_U3`. -/

theorem singularPoints_le_seven_of_U3 (p : ℕ) [CharP k p] (hp : 2 < p)
    (hrho : 2 < R.S.picardRank) (P : R.S.PrimeCurve) (hP : R.IsShortestExteriorMinusOne P)
    (B : R.Vertices) (hwB : R.w B = 3) (hPB : R.contact P B = 2) :
    R.X.singularPoints.card ≤ 7 := by
  classical
  have hp0 : 0 < p := by omega
  -- the square-one divisor `A = B + 2P`
  set A : R.S.WeilDivisor := Finsupp.single B.val 1 + Finsupp.single P 2 with hAdef
  have hnumA : numW R A = 𝒞 B.val + (2 : ℚ) • 𝒞 P := by
    rw [hAdef, map_add, numW_single, numW_single]
    push_cast
    rw [one_smul]
  obtain ⟨hnefA, hA2, hKA⟩ := KltDP.Manuscript.S06.squareOneClass_U3 R P hP.1 B hwB hPB
  have hnef : ∀ Q, 0 ≤ degW R Q A := fun Q => by
    unfold degW
    rw [hnumA]
    exact hnefA Q
  have hsq : 0 < 𝔅 (numW R A) (numW R A) := by
    rw [hnumA, hA2]
    norm_num
  have hrr : 0 < 𝔅 (R.Knum + numW R A) (numW R A) / 2 + 1 := by
    rw [LinearMap.BilinForm.add_left, hnumA, hKA, hA2]
    norm_num
  obtain ⟨Z, hZeff, hZlin⟩ := exists_effective_adjoint R p hp0 A hnef hsq hrr
  have hnumZ : numW R Z = R.Knum + numW R A := by
    rw [numW_eq_of_linearlyEquivalent R hZlin, map_add, numW_KS]
  have hAZ : 𝔅 (numW R A) (numW R Z) = 0 := by
    rw [hnumZ, LinearMap.BilinForm.add_right,
      (R.S.numericalIntersectionBilinForm_isSymm R.hreg).eq _ R.Knum, hnumA, hKA, hA2]
    norm_num
  have hZnull : ∀ Q, Z Q ≠ 0 → degW R Q A = 0 := degW_eq_zero_of_component R A Z hnef hZeff hAZ
  -- the intersection table
  have hPB' : (P.intersectionNumber (R.S.primeCurveCartier R.hreg B.val) : ℚ) = 2 := by
    exact_mod_cast hPB
  have hBP' : ((B.val).intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) = 2 := by
    rw [inter_comm]
    exact hPB'
  have hdegA : ∀ Q, degW R Q A = (Q.intersectionNumber (R.S.primeCurveCartier R.hreg B.val) : ℚ) +
      2 * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) := by
    intro Q
    rw [hAdef, degW_add, degW_single, degW_single]
    push_cast
    ring
  have hdegB : degW R B.val A = 1 := by
    rw [hdegA, inter_self, hwB, hBP']
    norm_num
  have hdegP : degW R P A = 0 := by
    rw [hdegA, hPB', inter_self_minusOne R P hP.1.1]
    norm_num
  have hPneB : P ≠ B.val := exterior_ne_vertex R P hP.1.2 B
  -- `B` is not a component of `Z`
  have hZB : Z B.val = 0 := by
    refine Classical.byContradiction (fun h => ?_)
    have := hZnull _ h
    rw [hdegB] at this
    exact one_ne_zero this
  -- components `Q ≠ P` of `Z` are disjoint from `B` and `P`
  have hcomp : ∀ Q, Z Q ≠ 0 → Q ≠ P →
      (Q.intersectionNumber (R.S.primeCurveCartier R.hreg B.val) : ℚ) = 0 ∧
      (Q.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) = 0 := by
    intro Q hQ hQP
    have hQB : Q ≠ B.val := fun h => hQ (h ▸ hZB)
    have h0 := hZnull Q hQ
    rw [hdegA] at h0
    have h1 := inter_nonneg R Q B.val hQB
    have h2 := inter_nonneg R Q P hQP
    constructor <;> linarith
  -- `Z · P = -1` forces `Z_P = 1`
  have hZP_deg : degW R P Z = -1 := by
    rw [degW_of_linearlyEquivalent_KS_add R Z A hZlin, hdegP,
      Kdeg_eq_neg_one_of_isMinusOne R P hP.1.1]
    norm_num
  have hZP : Z P = 1 := by
    have h := degW_eq_sum R P Z
    rw [Finset.sum_eq_single P (fun Q hQ hQP => ?_) (fun hP' => ?_)] at h
    · rw [inter_self_minusOne R P hP.1.1, hZP_deg] at h
      have : (Z P : ℚ) = 1 := by linarith
      exact_mod_cast this
    · rw [inter_comm, (hcomp Q (Finsupp.mem_support_iff.mp hQ) hQP).2, mul_zero]
    · have : Z P = 0 := by
        refine Classical.byContradiction (fun h => ?_)
        exact hP' (Finsupp.mem_support_iff.mpr h)
      rw [this, Int.cast_zero, zero_mul]
  -- the remainder `N = Z - P ∼ K_S + B + P`
  set N : R.S.WeilDivisor := Z - Finsupp.single P 1 with hNdef
  have hNapply : ∀ Q, N Q = Z Q - if P = Q then 1 else 0 := by
    intro Q
    simp only [hNdef, Finsupp.sub_apply, Finsupp.single_apply]
  have hNP : N P = 0 := by
    rw [hNapply]
    simp [hZP]
  have hNother : ∀ Q, Q ≠ P → N Q = Z Q := by
    intro Q hQ
    rw [hNapply]
    simp [Ne.symm hQ]
  have hNeff : EffectiveDivisor N := by
    intro Q
    by_cases hQ : Q = P
    · rw [hQ, hNP]
    · rw [hNother Q hQ]
      exact hZeff Q
  have hZeq : Z = N + Finsupp.single P 1 := by
    rw [hNdef]
    abel
  have hA' : A = Finsupp.single B.val 1 + Finsupp.single P 1 + Finsupp.single P 1 := by
    rw [hAdef, add_assoc, ← Finsupp.single_add]
    norm_num
  have hNlin : R.S.LinearlyEquivalent N
      (R.S.cartierToWeilHom R.KS + (Finsupp.single B.val 1 + Finsupp.single P 1)) := by
    have h := linearlyEquivalent_of_sub R hZeq hZlin
    rwa [hA', show R.S.cartierToWeilHom R.KS +
      (Finsupp.single B.val 1 + Finsupp.single P 1 + Finsupp.single P 1) - Finsupp.single P 1 =
      R.S.cartierToWeilHom R.KS + (Finsupp.single B.val 1 + Finsupp.single P 1) by abel] at h
  have hnumN : numW R N = R.Knum + (𝒞 B.val + 𝒞 P) := by
    rw [numW_eq_of_linearlyEquivalent R hNlin, map_add, numW_KS, map_add, numW_single, numW_single]
    simp
  have hNcomp : ∀ Q, N Q ≠ 0 → Q ≠ P ∧ Z Q ≠ 0 := by
    intro Q hQ
    have hQP : Q ≠ P := fun h => hQ (h ▸ hNP)
    exact ⟨hQP, by rwa [hNother Q hQP] at hQ⟩
  -- `L · N = ℓ - v < ℓ`, so `N` is supported on `D`
  have hLN : LdegW R N = R.Ldeg P - R.Lsq := by
    rw [LdegW_eq_pairing, hnumN, LinearMap.BilinForm.add_right, LinearMap.BilinForm.add_right,
      (R.S.numericalIntersectionBilinForm_isSymm R.hreg).eq R.Lnum R.Knum, R.Knum_pairing_Lnum,
      Lnum_pairing_curveClass, Lnum_pairing_curveClass, R.Ldeg_exceptional B]
    ring
  have hexc : ∀ Q, N Q ≠ 0 → IsExceptionalCurve R.π Q :=
    exceptional_of_LdegW_lt R hrho hP N hNeff (by rw [hLN]; linarith [R.Lsq_pos])
  -- `N · (B + P) = 0`, hence `N = 0`
  have hNB : degW R B.val N = 0 :=
    degW_eq_zero_of_components R B.val N
      (fun Q hQ => (hcomp Q (hNcomp Q hQ).2 (hNcomp Q hQ).1).1)
  have hNP' : degW R P N = 0 :=
    degW_eq_zero_of_components R P N
      (fun Q hQ => (hcomp Q (hNcomp Q hQ).2 (hNcomp Q hQ).1).2)
  have hN0 : N = 0 := by
    refine eq_zero_of_exceptional_adjoint R N hNeff hexc _ hnumN ?_
    rw [LinearMap.BilinForm.add_right,
      (R.S.numericalIntersectionBilinForm_isSymm R.hreg).eq _ (𝒞 B.val),
      (R.S.numericalIntersectionBilinForm_isSymm R.hreg).eq _ (𝒞 P), ← degW_eq_pairing,
      ← degW_eq_pairing, hNB, hNP', add_zero]
  -- `-K_S ≡ B + P` and Proposition 6.2 (iii)
  have hK : R.Knum = -(𝒞 B.val + 𝒞 P) := by
    have h := hnumN
    rw [hN0, map_zero] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have := (KltDP.Manuscript.S06.squareOneStructure_U3 R p hp P hP.1 B hwB hPB hK).2.2.2.2.2.2.2.2.2.2
  omega


/-! ### Integrality of the weights -/

theorem w_eq_two_or_three_le (i : R.Vertices) : R.w i = 2 ∨ 3 ≤ R.w i := by
  obtain ⟨z, hz⟩ : ∃ z : ℤ, R.w i = z := ⟨_, w_eq_intCast R i⟩
  have h2 := R.two_le_w i
  rw [hz] at h2 ⊢
  have h2' : (2 : ℤ) ≤ z := by exact_mod_cast h2
  rcases (by omega : z = 2 ∨ 3 ≤ z) with h3 | h3
  · left
    rw [h3]
    norm_num
  · right
    exact_mod_cast h3

/-! ### The isolated weight-two contact: `pᵀA⁻¹p = 1/2` (manuscript lines 2404–2406) -/

/-- If `P` meets only an isolated weight-two vertex `C`, once, then `pᵀA⁻¹p = 1/2`,
contradicting Lemma 2.8. -/
theorem green_isolated_contradiction (p : ℕ) [CharP k p] (hp0 : 0 < p) (P : R.S.PrimeCurve)
    (hP : R.IsExteriorMinusOne P) (C : R.Vertices) (hwC : R.w C = 2) (hPC : R.contact P C = 1)
    (hiso : ∀ y, ¬ R.graph.Adj C y) (honly : ∀ i, i ≠ C → R.contact P i = 0) : False := by
  classical
  have hgreen := rankOneProjection_green_gt_one R p hp0 P hP
  have hpvec : contactVector R P = Pi.single C 1 := by
    funext i
    rw [contactVector_eq]
    by_cases hi : i = C
    · rw [hi, hPC]
      simp
    · rw [honly i hi]
      simp [hi]
  set x : R.Vertices → ℚ := Pi.single C (1 / 2) with hx
  have hAx : R.A *ᵥ x = contactVector R P := by
    funext v
    rw [A_mulVec_apply, hpvec]
    have hsum : ∑ u ∈ R.graph.neighborFinset v, x u = 0 := by
      refine Finset.sum_eq_zero (fun u hu => ?_)
      have hadj : R.graph.Adj v u := (R.graph.mem_neighborFinset v u).1 hu
      have huC : u ≠ C := fun h => hiso v (h ▸ hadj).symm
      rw [hx]
      simp [huC]
    rw [hsum, sub_zero]
    by_cases hv : v = C
    · rw [hv, hx, hwC]
      simp
    · rw [hx]
      simp [hv]
  have hinv : R.A⁻¹ *ᵥ contactVector R P = x := by
    rw [← hAx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul R.A (A_det_isUnit R),
      Matrix.one_mulVec]
  rw [hinv, hpvec] at hgreen
  have hdot : Pi.single C (1 : ℚ) ⬝ᵥ x = 1 / 2 := by
    rw [hx]
    simp [dotProduct, Pi.single_apply]
  linarith

/-! ### The weights `(3, β)` of the two higher-weight contacts (manuscript lines 2413–2416) -/

theorem weights_of_two_higher_contacts (P : R.S.PrimeCurve) (hP : R.IsExteriorMinusOne P)
    (B₁ B₂ : R.Vertices) (hne : B₁ ≠ B₂) (hw1 : 3 ≤ R.w B₁) (hw2 : 3 ≤ R.w B₂)
    (hPB₁ : R.contact P B₁ = 1) (hPB₂ : R.contact P B₂ = 1) :
    (R.w B₁ = 3 ∧ (R.w B₂ = 3 ∨ R.w B₂ = 4 ∨ R.w B₂ = 5)) ∨
      (R.w B₂ = 3 ∧ (R.w B₁ = 3 ∨ R.w B₁ = 4 ∨ R.w B₁ = 5)) := by
  have hbud := two_contacts_mul_lam_lt_one R P hP hne
  rw [contactVector_eq, contactVector_eq, hPB₁, hPB₂] at hbud
  push_cast at hbud
  have hl1 := elementaryDiscrepancyBound R B₁ hw1
  have hl2 := elementaryDiscrepancyBound R B₂ hw2
  obtain ⟨a, ha⟩ : ∃ a : ℤ, R.w B₁ = a := ⟨_, w_eq_intCast R B₁⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, R.w B₂ = b := ⟨_, w_eq_intCast R B₂⟩
  rw [ha] at hl1 hw1 ⊢
  rw [hb] at hl2 hw2 ⊢
  have ha3 : (3 : ℤ) ≤ a := by exact_mod_cast hw1
  have hb3 : (3 : ℤ) ≤ b := by exact_mod_cast hw2
  have hapos : (0 : ℚ) < a := by exact_mod_cast (by omega : (0 : ℤ) < a)
  have hbpos : (0 : ℚ) < b := by exact_mod_cast (by omega : (0 : ℤ) < b)
  have hsum : ((a : ℚ) - 2) / a + ((b : ℚ) - 2) / b < 1 := by linarith
  rw [div_add_div _ _ hapos.ne' hbpos.ne', div_lt_one (mul_pos hapos hbpos)] at hsum
  have hZ : (a - 2) * b + a * (b - 2) < a * b := by exact_mod_cast hsum
  have key : (a = 3 ∧ (b = 3 ∨ b = 4 ∨ b = 5)) ∨ (b = 3 ∧ (a = 3 ∨ a = 4 ∨ a = 5)) := by
    rcases (by omega : a = 3 ∨ 4 ≤ a) with ha' | ha'
    · left
      refine ⟨ha', ?_⟩
      subst ha'
      omega
    · rcases (by omega : b = 3 ∨ 4 ≤ b) with hb' | hb'
      · right
        refine ⟨hb', ?_⟩
        subst hb'
        omega
      · exfalso
        nlinarith
  rcases key with ⟨ha', hb'⟩ | ⟨hb', ha'⟩
  · left
    refine ⟨by rw [ha']; norm_num, ?_⟩
    rcases hb' with h | h | h <;> rw [h] <;> norm_num
  · right
    refine ⟨by rw [hb']; norm_num, ?_⟩
    rcases ha' with h | h | h <;> rw [h] <;> norm_num

/-! ### Steps (2)–(8) of the proof of Theorem 7.1 at a shortest curve of a counterexample -/

section Steps

variable (p : ℕ) [CharP k p] (hp : 2 < p) (hrho : 2 < R.S.picardRank)
  (P : R.S.PrimeCurve) (hP : R.IsShortestExteriorMinusOne P)
  (hcount : ¬ R.X.singularPoints.card ≤ 7)

include hp hrho hP hcount in
/-- Manuscript lines 2331–2336: every contact of `P` is simple (weight two by Corollary 6.4 and
Proposition 6.2 (ii); higher weight by Lemma 4.2 and Proposition 6.2 (iii)). -/
theorem contact_le_one (i : R.Vertices) : R.contact P i ≤ 1 := by
  refine Classical.byContradiction (fun h => ?_)
  push_neg at h
  have h2 : 2 ≤ R.contact P i := h
  rcases w_eq_two_or_three_le R i with hw | hw
  · exact hcount (KltDP.Manuscript.S06.multipleContact_bound R p hp hrho P hP i hw h2)
  · rcases isExcessContact_or_isBoundedContact R P i with hex | hbd
    · obtain ⟨hw3, hc2⟩ := higher_weight_excess_contact R P hP.1 i hw hex
      exact hcount (singularPoints_le_seven_of_U3 R p hp hrho P hP i hw3 hc2)
    · have := contact_le_one_of_bounded R P hP.1 i hbd
      omega

include hp hrho hP hcount in
theorem contact_eq_zero_or_one (i : R.Vertices) : R.contact P i = 0 ∨ R.contact P i = 1 := by
  have h0 := contact_nonneg_of_not_exceptional R P hP.1.2 i
  have h1 := contact_le_one R p hp hrho P hP hcount i
  omega

include hp hrho hP hcount in
/-- Manuscript lines 2341–2344 (Lemma 6.3 with `b = 2`): two weight-two contacts of `P` are not
adjacent. -/
theorem not_adj_of_weightTwo_contacts (U V : R.Vertices) (hUV : U ≠ V) (hwU : R.w U = 2)
    (hwV : R.w V = 2) (hPU : R.contact P U = 1) (hPV : R.contact P V = 1) :
    ¬ R.graph.Adj U V := by
  intro hadj
  have hp0 : 0 < p := by omega
  obtain ⟨-, hcases⟩ := adjacentContactAdjoint R P U V hP.1 hUV hwV hadj hPU hPV p hp0
  rcases hcases with ⟨-, -, N, hN⟩ | ⟨h3, -⟩ | ⟨h4, -⟩
  · have hN0 := adjointRemainder_eq_zero R hrho hP hN
    have hclass := hN.class_eq
    rw [hN0] at hclass
    exact hcount (singularPoints_le_seven_of_remainder_zero R P U V hP.1 hUV hwV hadj hPU hPV p
      hp0 hwU hclass)
  · rw [hwU] at h3
    norm_num at h3
  · rw [hwU] at h4
    norm_num at h4

include hp hrho hP hcount in
/-- Manuscript lines 2345–2346 (Theorem 6.7): three weight-two contacts are impossible. -/
theorem not_three_weightTwo_contacts (C₀ C₁ C₂ : R.Vertices) (h01 : C₀ ≠ C₁) (h02 : C₀ ≠ C₂)
    (h12 : C₁ ≠ C₂) (hw0 : R.w C₀ = 2) (hw1 : R.w C₁ = 2) (hw2 : R.w C₂ = 2)
    (hc0 : R.contact P C₀ = 1) (hc1 : R.contact P C₁ = 1) (hc2 : R.contact P C₂ = 1) : False := by
  have hn01 := not_adj_of_weightTwo_contacts R p hp hrho P hP hcount C₀ C₁ h01 hw0 hw1 hc0 hc1
  have hn02 := not_adj_of_weightTwo_contacts R p hp hrho P hP hcount C₀ C₂ h02 hw0 hw2 hc0 hc2
  have hn12 := not_adj_of_weightTwo_contacts R p hp hrho P hP hcount C₁ C₂ h12 hw1 hw2 hc1 hc2
  rcases threeContactDescent R P C₀ C₁ C₂ hP.1 h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2
    p hp with h | ⟨Q, hQ, -, -, -, -, -, hle⟩
  · exact hcount h
  · have := hP.2 Q hQ
    have := R.Lsq_pos
    linarith

include hrho hP in
/-- Manuscript lines 2353–2356 and 2410–2413 (Lemma 6.3 at `(B, H)`): a higher-weight contact
`B` of `P` is not adjacent to a weight-two contact `H` when `P` has a further contact `T`: the
remainder would be zero at the shortest curve, but `N · T = K_S · T + T·B + T·H + T·P > 0`. -/
theorem not_adj_higher_contact (hp0 : 0 < p) (B H T : R.Vertices) (hwB : 3 ≤ R.w B)
    (hwH : R.w H = 2) (hPB : R.contact P B = 1) (hPH : R.contact P H = 1)
    (hPT : R.contact P T = 1) (hTB : T ≠ B) (hTH : T ≠ H) : ¬ R.graph.Adj B H := by
  intro hadj
  have hBH : B ≠ H := fun h => by
    rw [h, hwH] at hwB
    norm_num at hwB
  obtain ⟨-, hcases⟩ := adjacentContactAdjoint R P B H hP.1 hBH hwH hadj hPB hPH p hp0
  have key : ∀ (A Z N : R.S.WeilDivisor), AdjointRemainder R P B H A Z N → False := by
    intro A Z N hN
    have hN0 := adjointRemainder_eq_zero R hrho hP hN
    have hdeg := degW_of_linearlyEquivalent_KS_add R N _ hN.class_eq T.val
    rw [hN0, degW_zero, degW_adjDiv] at hdeg
    have h1 := inter_nonneg R T.val B.val (vertex_ne_of_ne R hTB)
    have h2 := inter_nonneg R T.val H.val (vertex_ne_of_ne R hTH)
    have h3 : ((T.val).intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) = 1 :=
      inter_contact' R P T hPT
    have h4 := Kdeg_nonneg_of_exceptional R T.val T.property
    push_cast at hdeg
    linarith
  rcases hcases with ⟨-, -, N, hN⟩ | ⟨-, -, N, hN⟩ | ⟨-, -, N, hN⟩ <;> exact key _ _ _ hN

include hp hrho hP hcount in
/-- Manuscript lines 2347–2362: exactly two weight-two contacts `U, V` are impossible
(Theorem 7.5, `TwoContactRulingHyp`). -/
theorem not_two_weightTwo_contacts (hTwo : TwoContactRulingHyp R P) (U V : R.Vertices)
    (hUV : U ≠ V) (hwU : R.w U = 2) (hwV : R.w V = 2) (hPU : R.contact P U = 1)
    (hPV : R.contact P V = 1)
    (honly : ∀ i, R.w i = 2 → R.contact P i ≠ 0 → i = U ∨ i = V) : False := by
  have hp0 : 0 < p := by omega
  have hnadj := not_adj_of_weightTwo_contacts R p hp hrho P hP hcount U V hUV hwU hwV hPU hPV
  apply hcount
  apply hTwo U V hUV hwU hwV hnadj hPU hPV
  intro i
  have hexp : ((i.val).intersectionNumber (R.fibreDivisor U V P) : ℚ) =
      ((i.val).intersectionNumber (R.S.primeCurveCartier R.hreg U.val) : ℚ) +
        2 * ((i.val).intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) +
        ((i.val).intersectionNumber (R.S.primeCurveCartier R.hreg V.val) : ℚ) := by
    unfold ResolutionDatum.fibreDivisor
    rw [PrimeCurve.intersectionNumber_add, PrimeCurve.intersectionNumber_add, two_zsmul,
      PrimeCurve.intersectionNumber_add]
    push_cast
    ring
  suffices h : ((i.val).intersectionNumber (R.fibreDivisor U V P) : ℚ) ≤ 2 by exact_mod_cast h
  rw [hexp]
  have hiP : ((i.val).intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) =
      (R.contact P i : ℚ) := by
    rw [inter_comm]
  by_cases hiU : i = U
  · rw [hiU] at hiP
    rw [hiU, inter_self, hwU, inter_of_not_adj R hUV hnadj, hiP, hPU]
    norm_num
  by_cases hiV : i = V
  · rw [hiV] at hiP
    rw [hiV, inter_self, hwV, inter_of_not_adj R (Ne.symm hUV) (fun h => hnadj h.symm), hiP, hPV]
    norm_num
  have hle1 : ∀ j : R.Vertices, i ≠ j →
      ((i.val).intersectionNumber (R.S.primeCurveCartier R.hreg j.val) : ℚ) ≤ 1 := by
    intro j hij
    rw [inter_vertices]
    by_cases hadj : R.graph.Adj i j
    · rw [M_eq_one_of_adj R hadj]
    · rw [M_eq_zero_of_not_adj R hij hadj]
      norm_num
  rcases contact_eq_zero_or_one R p hp hrho P hP hcount i with hc0 | hc1
  · rw [hiP, hc0]
    have := hle1 U hiU
    have := hle1 V hiV
    push_cast
    linarith
  · have hw : 3 ≤ R.w i := by
      rcases w_eq_two_or_three_le R i with hw | hw
      · exfalso
        rcases honly i hw (by rw [hc1]; norm_num) with h | h
        · exact hiU h
        · exact hiV h
      · exact hw
    have hnU : ¬ R.graph.Adj i U :=
      not_adj_higher_contact R p hrho P hP hp0 i U V hw hwU hc1 hPU hPV (Ne.symm hiV) hUV.symm
    have hnV : ¬ R.graph.Adj i V :=
      not_adj_higher_contact R p hrho P hP hp0 i V U hw hwV hc1 hPV hPU (Ne.symm hiU) hUV
    rw [hiP, hc1, inter_vertices, inter_vertices, M_eq_zero_of_not_adj R hiU hnU,
      M_eq_zero_of_not_adj R hiV hnV]
    norm_num

include hp hrho hP hcount in
/-- Manuscript lines 2363–2373: exactly one weight-two contact `C`. The one-component
replacement (Theorem 4.5) and Picard minimality leave `j = 2` higher-weight contacts `B₁, B₂`
in distinct components, with `C` of valency at most one; `j = 0` is excluded by the projection
identity and `j = 1` by Theorem 4.6 (`IsolatedExchangeHyp`). -/
theorem one_weightTwo_contact (hIso : IsolatedExchangeHyp R)
    (hmin : ∀ R' : ResolutionDatum k, 7 < R'.X.singularPoints.card →
      R.S.picardRank ≤ R'.S.picardRank)
    (C : R.Vertices) (hwC : R.w C = 2) (hPC : R.contact P C = 1)
    (honly : ∀ i, R.w i = 2 → R.contact P i ≠ 0 → i = C) :
    ∃ B₁ B₂ : R.Vertices, B₁ ≠ B₂ ∧ 3 ≤ R.w B₁ ∧ 3 ≤ R.w B₂ ∧
      R.contact P B₁ = 1 ∧ R.contact P B₂ = 1 ∧
      (∀ i, i ≠ C → i ≠ B₁ → i ≠ B₂ → R.contact P i = 0) ∧ ¬ R.graph.Reachable B₁ B₂ ∧
      (∀ i j, R.graph.Adj C i → R.graph.Adj C j → i = j) := by
  classical
  have hp0 : 0 < p := by omega
  -- the higher-weight contacts
  set Hs : Finset R.Vertices := Finset.univ.filter (fun i => 3 ≤ R.w i ∧ R.contact P i ≠ 0)
    with hHs
  have hmemH : ∀ i, i ∈ Hs ↔ 3 ≤ R.w i ∧ R.contact P i ≠ 0 := by
    intro i
    simp [hHs]
  have hcontact1 : ∀ i ∈ Hs, R.contact P i = 1 := by
    intro i hi
    rcases contact_eq_zero_or_one R p hp hrho P hP hcount i with h | h
    · exact absurd h ((hmemH i).mp hi).2
    · exact h
  have hzero : ∀ i, i ≠ C → i ∉ Hs → R.contact P i = 0 := by
    intro i hiC hiH
    refine Classical.byContradiction (fun hne => ?_)
    rcases w_eq_two_or_three_le R i with hw | hw
    · exact hiC (honly i hw hne)
    · exact hiH ((hmemH i).mpr ⟨hw, hne⟩)
  -- (4) two higher-weight contacts lie in distinct components
  have hunreach : ∀ i ∈ Hs, ∀ j ∈ Hs, i ≠ j → ¬ R.graph.Reachable i j := by
    intro i hi j hj hij hreach
    have h1 := discrepancySeparation R i j hij ((hmemH i).mp hi).1 ((hmemH j).mp hj).1 hreach
    have h2 := two_contacts_mul_lam_lt_one R P hP.1 hij
    rw [contactVector_eq, contactVector_eq, hcontact1 i hi, hcontact1 j hj] at h2
    push_cast at h2
    linarith
  -- (4) at most two higher-weight contacts
  have hcard : Hs.card ≤ 2 := by
    have hsum : (Hs.card : ℚ) * (1 / 3) ≤ ∑ i ∈ Hs, contactVector R P i * R.lam i := by
      have := Finset.card_nsmul_le_sum Hs (fun i => contactVector R P i * R.lam i) (1 / 3)
        (fun i hi => ?_)
      · simpa [nsmul_eq_mul] using this
      · show (1 : ℚ) / 3 ≤ contactVector R P i * R.lam i
        rw [contactVector_eq, hcontact1 i hi]
        push_cast
        rw [one_mul]
        have hw := ((hmemH i).mp hi).1
        have hl := elementaryDiscrepancyBound R i hw
        have : (1 : ℚ) / 3 ≤ (R.w i - 2) / R.w i := by
          rw [le_div_iff₀ (by linarith)]
          linarith
        linarith
    have hle : ∑ i ∈ Hs, contactVector R P i * R.lam i ≤ contactVector R P ⬝ᵥ R.lam :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Hs)
        (fun i _ _ => mul_nonneg (contactVector_nonneg R P hP.1.2 i) (R.lam_nonneg i))
    have hlt := rankOneProjection_charge_lt_one R P hP.1
    have h3 : (Hs.card : ℚ) < 3 := by linarith
    have h3' : Hs.card < 3 := by exact_mod_cast h3
    omega
  -- Theorem 4.5 applied to `C`
  have hexC : IsExcessContact R P C := by
    unfold IsExcessContact ResolutionDatum.q
    rw [contactVector_eq, hPC, hwC]
    norm_num
  have hbdd : ∀ i, i ≠ C → IsBoundedContact R P i := by
    intro i hiC
    unfold IsBoundedContact ResolutionDatum.q
    rw [contactVector_eq]
    by_cases hi : i ∈ Hs
    · rw [hcontact1 i hi]
      have := ((hmemH i).mp hi).1
      push_cast
      linarith
    · rw [hzero i hiC hi]
      have := R.two_le_w i
      push_cast
      linarith
  have hsep : ∀ i j : R.Vertices, i ≠ C → j ≠ C → R.contact P i ≠ 0 → R.contact P j ≠ 0 →
      i ≠ j → ¬ R.graph.Reachable i j := by
    intro i j hiC hjC hi hj hij
    have hw : ∀ l : R.Vertices, l ≠ C → R.contact P l ≠ 0 → 3 ≤ R.w l := by
      intro l hlC hl
      rcases w_eq_two_or_three_le R l with hw | hw
      · exact absurd (honly l hw hl) hlC
      · exact hw
    exact hunreach i ((hmemH i).mpr ⟨hw i hiC hi, hi⟩) j ((hmemH j).mpr ⟨hw j hjC hj, hj⟩) hij
  have hacyclic := famG_isAcyclic R C P hP.1.2 hsep
  obtain ⟨R₁, hρ, hcase0, hcase1⟩ :=
    oneComponentReplacement_datum_cases R C P p hp0 hP.1 hexC hbdd hacyclic
  have hR₁ : R₁.X.singularPoints.card ≤ 7 := by
    refine Classical.byContradiction (fun h => ?_)
    push_neg at h
    have := hmin R₁ h
    omega
  -- `a = contactCount = #Hs`
  have hcc : contactCount R C P = Hs.card := by
    unfold contactCount
    rw [← Finset.card_map (Function.Embedding.subtype (fun i : R.Vertices => i ≠ C))]
    congr 1
    ext i
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coe_subtype, hHs]
    constructor
    · rintro ⟨⟨j, hjC⟩, hj, rfl⟩
      have hne : R.contact P j ≠ 0 := by
        intro h0
        apply hj
        show contactVector R P j = 0
        rw [contactVector_eq, h0]
        simp
      refine ⟨?_, hne⟩
      rcases w_eq_two_or_three_le R j with hw | hw
      · exact absurd (honly j hw hne) hjC
      · exact hw
    · rintro ⟨hw, hne⟩
      have hiC : i ≠ C := fun h => by
        rw [h, hwC] at hw
        norm_num at hw
      refine ⟨⟨i, hiC⟩, ?_, rfl⟩
      show contactVector R P i ≠ 0
      rw [contactVector_eq]
      exact_mod_cast hne
  rcases (by omega : Hs.card = 0 ∨ Hs.card = 1 ∨ Hs.card = 2) with h0 | h1 | h2
  · -- `j = 0`: `C` is isolated and the only contact; `pᵀA⁻¹p = 1/2`
    exfalso
    have hcc0 : contactCount R C P = 0 := by rw [hcc, h0]
    have hdeg : R.graph.degree C = 0 := by
      have := hcase0 hcc0
      omega
    have hiso : ∀ y, ¬ R.graph.Adj C y := by
      intro y hy
      have : 0 < R.graph.degree C := (SimpleGraph.degree_pos_iff_exists_adj R.graph C).mpr ⟨y, hy⟩
      omega
    have hHempty : Hs = ∅ := Finset.card_eq_zero.mp h0
    have honlyC : ∀ i, i ≠ C → R.contact P i = 0 := fun i hi => hzero i hi (by rw [hHempty]; simp)
    exact green_isolated_contradiction R p hp0 P hP.1 C hwC hPC hiso honlyC
  · -- `j = 1`: `C` is isolated, the isolated-`A₁` mixed exchange (Theorem 4.6)
    exfalso
    obtain ⟨B, hB⟩ := Finset.card_eq_one.mp h1
    have hBmem : B ∈ Hs := by
      rw [hB]
      exact Finset.mem_singleton_self B
    obtain ⟨hwB, -⟩ := (hmemH B).mp hBmem
    have hPB : R.contact P B = 1 := hcontact1 B hBmem
    have hcc1 : contactCount R C P = 1 := by rw [hcc, h1]
    have hdeg : R.graph.degree C = 0 := by
      have := hcase1 (by rw [hcc1])
      rw [hcc1] at this
      omega
    have hiso : ∀ y, ¬ R.graph.Adj C y := by
      intro y hy
      have : 0 < R.graph.degree C := (SimpleGraph.degree_pos_iff_exists_adj R.graph C).mpr ⟨y, hy⟩
      omega
    have hother : ∀ i, i ≠ C → i ≠ B → R.contact P i = 0 := by
      intro i hiC hiB
      apply hzero i hiC
      rw [hB]
      simp [hiB]
    obtain ⟨R₂, hρ₂, hle₂⟩ := hIso C B P hP.1 hwC hiso hwB hPC hPB hother
    have := hmin R₂ (by omega)
    omega
  · -- `j = 2`
    obtain ⟨B₁, B₂, hne, hB⟩ := Finset.card_eq_two.mp h2
    have hB₁mem : B₁ ∈ Hs := by
      rw [hB]
      simp
    have hB₂mem : B₂ ∈ Hs := by
      rw [hB]
      simp
    have hcc2 : contactCount R C P = 2 := by rw [hcc, h2]
    have hdeg : R.graph.degree C ≤ 1 := by
      have := hcase1 (by rw [hcc2]; norm_num)
      rw [hcc2] at this
      omega
    refine ⟨B₁, B₂, hne, ((hmemH B₁).mp hB₁mem).1, ((hmemH B₂).mp hB₂mem).1,
      hcontact1 B₁ hB₁mem, hcontact1 B₂ hB₂mem, ?_, hunreach B₁ hB₁mem B₂ hB₂mem hne, ?_⟩
    · intro i hiC hi1 hi2
      apply hzero i hiC
      rw [hB]
      simp [hi1, hi2]
    · intro i j hi hj
      have h := Finset.card_le_one.mp (by rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg)
        i ((R.graph.mem_neighborFinset C i).2 hi) j ((R.graph.mem_neighborFinset C j).2 hj)
      exact h

end Steps


/-! ### Steps (10)–(12): the adjoint identity and the configuration (manuscript lines 2417–2445) -/

/-- Given the contact data of steps (2)–(10) (`C` of weight two, `B₁, B₂` of weights `(3, β)`,
`β ∈ {3,4,5}`, simple contacts, no further contact, pairwise disjoint, `B₁, B₂` in distinct
components, `C` of valency `≤ 1`), the effective adjoint `N ∼ K_S + C + B₁ + B₂ + 2P` is a single
exterior `(-1)`-curve `R'` and all clauses of `AdjointConfiguration` hold. -/
theorem adjointConfiguration_of_core (p : ℕ) [CharP k p] (hp : 2 < p) (hrho : 2 < R.S.picardRank)
    (hcount : ¬ R.X.singularPoints.card ≤ 7)
    (P : R.S.PrimeCurve) (hP : R.IsShortestExteriorMinusOne P)
    (C B₁ B₂ : R.Vertices) (β : ℕ) (hβ : β = 3 ∨ β = 4 ∨ β = 5)
    (hwC : R.w C = 2) (hwB₁ : R.w B₁ = 3) (hwB₂ : R.w B₂ = β)
    (hPC : R.contact P C = 1) (hPB₁ : R.contact P B₁ = 1) (hPB₂ : R.contact P B₂ = 1)
    (hother : ∀ i, i ≠ C → i ≠ B₁ → i ≠ B₂ → R.contact P i = 0)
    (hCB₁ : C ≠ B₁) (hCB₂ : C ≠ B₂) (hB₁B₂ : B₁ ≠ B₂)
    (hnCB₁ : ¬ R.graph.Adj C B₁) (hnCB₂ : ¬ R.graph.Adj C B₂) (hnB : ¬ R.graph.Adj B₁ B₂)
    (hreach : ¬ R.graph.Reachable B₁ B₂)
    (hval : ∀ i j, R.graph.Adj C i → R.graph.Adj C j → i = j) :
    AdjointConfiguration R P := by
  classical
  have hp0 : 0 < p := by omega
  have hβ3 : (3 : ℚ) ≤ R.w B₂ := by
    rw [hwB₂]
    rcases hβ with h | h | h <;> rw [h] <;> norm_num
  have hℓ := Ldeg_pos R P hP.1.2
  have hv := R.Lsq_pos
  -- the intersection table
  have iPC := inter_contact R P C hPC
  have iPB₁ := inter_contact R P B₁ hPB₁
  have iPB₂ := inter_contact R P B₂ hPB₂
  have iCP := inter_contact' R P C hPC
  have iB₁P := inter_contact' R P B₁ hPB₁
  have iB₂P := inter_contact' R P B₂ hPB₂
  have iCC := inter_self R C
  have iB₁B₁ := inter_self R B₁
  have iB₂B₂ := inter_self R B₂
  have iCB₁ := inter_of_not_adj R hCB₁ hnCB₁
  have iB₁C := inter_of_not_adj R hCB₁.symm (fun h => hnCB₁ h.symm)
  have iCB₂ := inter_of_not_adj R hCB₂ hnCB₂
  have iB₂C := inter_of_not_adj R hCB₂.symm (fun h => hnCB₂ h.symm)
  have iB₁B₂ := inter_of_not_adj R hB₁B₂ hnB
  have iB₂B₁ := inter_of_not_adj R hB₁B₂.symm (fun h => hnB h.symm)
  have iPP := inter_self_minusOne R P hP.1.1
  -- `T = C + B₁ + B₂ + 2P`: `T² = 3 - β`, `K_S · T = β - 3`, `L · T = 2ℓ`
  set T := cubDiv R P C B₁ B₂ 1 1 1 2 with hTdef
  have dTC : degW R C.val T = 0 := by
    rw [hTdef, degW_cubDiv, iCC, hwC, iCB₁, iCB₂, iCP]
    push_cast
    ring
  have dTB₁ : degW R B₁.val T = -1 := by
    rw [hTdef, degW_cubDiv, iB₁C, iB₁B₁, hwB₁, iB₁B₂, iB₁P]
    push_cast
    ring
  have dTB₂ : degW R B₂.val T = 2 - R.w B₂ := by
    rw [hTdef, degW_cubDiv, iB₂C, iB₂B₁, iB₂B₂, iB₂P]
    push_cast
    ring
  have dTP : degW R P T = 1 := by
    rw [hTdef, degW_cubDiv, iPC, iPB₁, iPB₂, iPP]
    push_cast
    ring
  have hTT : 𝔅 (numW R T) (numW R T) = 3 - R.w B₂ := by
    rw [hTdef, pairing_cubDiv, ← hTdef, dTC, dTB₁, dTB₂, dTP]
    push_cast
    ring
  have hKT : 𝔅 R.Knum (numW R T) = R.w B₂ - 3 := by
    rw [hTdef, Knum_pairing_cubDiv R P C B₁ B₂ hP.1, hwC, hwB₁]
    push_cast
    ring
  have hLT : 𝔅 R.Lnum (numW R T) = 2 * R.Ldeg P := by
    rw [hTdef, Lnum_pairing_cubDiv]
    push_cast
    ring
  -- Riemann–Roch: `χ(K_S + T) = 1` and `h⁰(-T) = 0` (`T · π^*A > 0`)
  obtain ⟨N, hNeff, hNlin⟩ : ∃ N : R.S.WeilDivisor, EffectiveDivisor N ∧
      R.S.LinearlyEquivalent N (R.S.cartierToWeilHom R.KS + T) := by
    obtain ⟨n, hn, Aamp, hample, hL⟩ := R.exists_ample_numerator
    have hcls := KltDP.Manuscript.S03.cartierClass_pullback_eq R n Aamp hL hn
    have hn' : (0 : ℚ) < n := by exact_mod_cast hn
    refine SurfaceRiemannRochNef.exists_effectiveWeil R.S R.hreg (R.S.cartierToWeilHom R.KS + T)
      (R.S.cartierToWeilHom R.KS) (DominantCartierPullback.pullbackHom R.π Aamp) (isCanonical_KS R)
      (AmplePullbackNef.isNef_signedCartier_pullback R.π Aamp hample) ?_ ?_
    · have e1 : (R.S.intersectionPairing R.hreg
          ((R.S.regularCartierWeilEquiv R.hreg).symm (R.S.cartierToWeilHom R.KS))
          (DominantCartierPullback.pullbackHom R.π Aamp) : ℚ) = (n : ℚ) * (-R.Lsq) := by
        rw [← NefNullCurveNegativeSquare.cartierClass_pairing, cartierClass_symm, numW_KS, hcls,
          LinearMap.BilinForm.smul_right, R.Knum_pairing_Lnum]
      have e2 : (R.S.intersectionPairing R.hreg
          ((R.S.regularCartierWeilEquiv R.hreg).symm (R.S.cartierToWeilHom R.KS + T))
          (DominantCartierPullback.pullbackHom R.π Aamp) : ℚ) =
          (n : ℚ) * (-R.Lsq + 2 * R.Ldeg P) := by
        rw [← NefNullCurveNegativeSquare.cartierClass_pairing, cartierClass_symm, map_add, numW_KS,
          hcls, LinearMap.BilinForm.smul_right, LinearMap.BilinForm.add_left, R.Knum_pairing_Lnum,
          (R.S.numericalIntersectionBilinForm_isSymm R.hreg).eq (numW R T) R.Lnum, hLT]
      have hlt : (R.S.intersectionPairing R.hreg
          ((R.S.regularCartierWeilEquiv R.hreg).symm (R.S.cartierToWeilHom R.KS))
          (DominantCartierPullback.pullbackHom R.π Aamp) : ℚ) <
          (R.S.intersectionPairing R.hreg
          ((R.S.regularCartierWeilEquiv R.hreg).symm (R.S.cartierToWeilHom R.KS + T))
          (DominantCartierPullback.pullbackHom R.π Aamp) : ℚ) := by
        rw [e1, e2]
        exact mul_lt_mul_of_pos_left (by linarith only [hℓ]) hn'
      exact_mod_cast hlt
    · rw [rrNumber_adjoint R p hp0 T, LinearMap.BilinForm.add_left, hKT, hTT]
      norm_num
  have hnumN : numW R N = R.Knum + numW R T := by
    rw [numW_eq_of_linearlyEquivalent R hNlin, map_add, numW_KS]
  have hdegN : ∀ Q, degW R Q N = (R.Kdeg Q : ℚ) + degW R Q T :=
    degW_of_linearlyEquivalent_KS_add R N T hNlin
  have hKC : (R.Kdeg C.val : ℚ) = 0 := by
    rw [R.Kdeg_exceptional]
    unfold ResolutionDatum.q
    rw [hwC]
    norm_num
  have hKB₁ : (R.Kdeg B₁.val : ℚ) = 1 := by
    rw [R.Kdeg_exceptional]
    unfold ResolutionDatum.q
    rw [hwB₁]
    norm_num
  have hKB₂ : (R.Kdeg B₂.val : ℚ) = R.w B₂ - 2 := by
    rw [R.Kdeg_exceptional]
    rfl
  have hKP : (R.Kdeg P : ℚ) = -1 := by
    rw [Kdeg_eq_neg_one_of_isMinusOne R P hP.1.1]
    norm_num
  -- `N · P = N · C = N · B₁ = N · B₂ = 0`, `L · N = 2ℓ - v`, `N · T = 0`
  have dNC : degW R C.val N = 0 := by
    rw [hdegN, hKC, dTC]
    norm_num
  have dNB₁ : degW R B₁.val N = 0 := by
    rw [hdegN, hKB₁, dTB₁]
    norm_num
  have dNB₂ : degW R B₂.val N = 0 := by
    rw [hdegN, hKB₂, dTB₂]
    ring
  have dNP : degW R P N = 0 := by
    rw [hdegN, hKP, dTP]
    norm_num
  have hLN : LdegW R N = 2 * R.Ldeg P - R.Lsq := by
    rw [LdegW_eq_pairing, hnumN, LinearMap.BilinForm.add_right,
      (R.S.numericalIntersectionBilinForm_isSymm R.hreg).eq R.Lnum R.Knum, R.Knum_pairing_Lnum,
      hLT]
    ring
  have hNT : 𝔅 (numW R N) (numW R T) = 0 := by
    rw [(R.S.numericalIntersectionBilinForm_isSymm R.hreg).eq, hTdef, pairing_cubDiv, dNC, dNB₁,
      dNB₂, dNP]
    push_cast
    ring
  -- the exterior part of `N` has total coefficient `M ≤ 1` (Lemma 3.3 (e))
  set ext : Finset R.S.PrimeCurve := N.support.filter (fun Q => ¬ IsExceptionalCurve R.π Q)
    with hext
  have hmem : ∀ Q, Q ∈ ext ↔ N Q ≠ 0 ∧ ¬ IsExceptionalCurve R.π Q := by
    intro Q
    simp only [hext, Finset.mem_filter, Finsupp.mem_support_iff]
  have hpos : ∀ Q ∈ ext, 0 < N Q :=
    fun Q hQ => lt_of_le_of_ne (hNeff Q) (Ne.symm ((hmem Q).mp hQ).1)
  set M : ℤ := ∑ Q ∈ ext, N Q with hM
  have hLsum : ∑ Q ∈ ext, (N Q : ℚ) * R.Ldeg Q = 2 * R.Ldeg P - R.Lsq := by
    rw [← hLN, LdegW_eq_sum, hext, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    by_cases hQ : IsExceptionalCurve R.π Q
    · rw [if_neg (not_not.mpr hQ), R.Ldeg_exceptional ⟨Q, hQ⟩, mul_zero]
    · rw [if_pos hQ]
  have hMle : (M : ℚ) * R.Ldeg P ≤ 2 * R.Ldeg P - R.Lsq := by
    rw [← hLsum, hM, Int.cast_sum, Finset.sum_mul]
    refine Finset.sum_le_sum (fun Q hQ => ?_)
    have h1 := KltDP.Manuscript.S03.Ldeg_ge_of_not_exceptional R hrho P hP Q ((hmem Q).mp hQ).2
    exact mul_le_mul_of_nonneg_left h1 (by exact_mod_cast (hpos Q hQ).le)
  have hM1 : M ≤ 1 := by
    refine Classical.byContradiction (fun h => ?_)
    push_neg at h
    have h2 : (2 : ℚ) ≤ M := by exact_mod_cast h
    have h3 : (2 : ℚ) * R.Ldeg P ≤ (M : ℚ) * R.Ldeg P := mul_le_mul_of_nonneg_right h2 hℓ.le
    linarith only [h3, hMle, hv]
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun Q hQ => (hpos Q hQ).le)
  rcases (by omega : M = 0 ∨ M = 1) with hM_zero | hM_one
  · -- `M = 0`: `N` is supported on `D`, hence `N = 0` and `-K_S ∼ T` (Proposition 5.5)
    exfalso
    have hexc : ∀ Q, N Q ≠ 0 → IsExceptionalCurve R.π Q := by
      intro Q hQ
      refine Classical.byContradiction (fun hext' => ?_)
      have hQmem : Q ∈ ext := (hmem Q).mpr ⟨hQ, hext'⟩
      rw [hM] at hM_zero
      exact hQ ((Finset.sum_eq_zero_iff_of_nonneg (fun Q hQ => (hpos Q hQ).le)).mp hM_zero Q
        hQmem)
    have hN0 : N = 0 := eq_zero_of_exceptional_adjoint R N hNeff hexc _ hnumN hNT
    have hpic0 : R.S.regularWeilPicardClass R.hreg 0 = 1 := by
      have h := R.S.regularWeilPicardClass_add R.hreg 0 0
      rw [add_zero] at h
      have h' : R.S.regularWeilPicardClass R.hreg 0 * R.S.regularWeilPicardClass R.hreg 0 =
          R.S.regularWeilPicardClass R.hreg 0 * 1 := by
        rw [mul_one]
        exact h.symm
      exact mul_left_cancel h'
    have hpic : cartierPicardClass R.S.toScheme R.KS * R.curvePic C.val * R.curvePic B₁.val *
        R.curvePic B₂.val * R.curvePic P ^ 2 = 1 := by
      have h := picW_eq_of_linearlyEquivalent R hNlin
      rw [hN0, hpic0] at h
      have e : Finsupp.single P (2 : ℤ) = Finsupp.single P 1 + Finsupp.single P 1 := by
        rw [← Finsupp.single_add]
        norm_num
      simp only [hTdef, cubDiv, e, R.S.regularWeilPicardClass_add, picW_KS, picW_single, mul_assoc,
        sq] at h
      simp only [mul_assoc, sq]
      exact h.symm
    exact hcount (KltDP.Manuscript.S05.zeroAdjointBound_pic R p hp C B₁ B₂ P hP.1 hnCB₁ hnCB₂ hnB
      hCB₁ hCB₂ hB₁B₂ hwC hwB₁ hβ3 hPC hPB₁ hPB₂ hpic)
  · -- `M = 1`: `N = R' + Z` with `R'` exterior of coefficient one and `Z ≥ 0` on `D`
    have hne : ext.Nonempty := by
      refine Classical.byContradiction (fun h => ?_)
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [hM, h, Finset.sum_empty] at hM_one
      exact absurd hM_one (by norm_num)
    have hcard : ext.card = 1 := by
      have h1 : ext.card • (1 : ℤ) ≤ ∑ Q ∈ ext, N Q :=
        Finset.card_nsmul_le_sum ext (fun Q => N Q) 1 (fun Q hQ => by
          have := hpos Q hQ
          show (1 : ℤ) ≤ N Q
          omega)
      have h2 := hne.card_pos
      rw [← hM, hM_one] at h1
      simp only [nsmul_eq_mul, mul_one] at h1
      omega
    obtain ⟨R', hR'⟩ := Finset.card_eq_one.mp hcard
    have hR'mem : R' ∈ ext := by
      rw [hR']
      exact Finset.mem_singleton_self R'
    obtain ⟨hNR'ne, hR'ext⟩ := (hmem R').mp hR'mem
    have hNR' : N R' = 1 := by rw [← hM_one, hM, hR', Finset.sum_singleton]
    have hother_ext : ∀ Q, N Q ≠ 0 → ¬ IsExceptionalCurve R.π Q → Q = R' := by
      intro Q hQ hQext
      have hQmem : Q ∈ ext := (hmem Q).mpr ⟨hQ, hQext⟩
      rw [hR'] at hQmem
      exact Finset.mem_singleton.mp hQmem
    -- the exceptional part `Z = N - R'`
    set Z : R.S.WeilDivisor := N - Finsupp.single R' 1 with hZdef
    have hZapply : ∀ Q, Z Q = N Q - if R' = Q then 1 else 0 := by
      intro Q
      simp only [hZdef, Finsupp.sub_apply, Finsupp.single_apply]
    have hZR' : Z R' = 0 := by
      rw [hZapply]
      simp [hNR']
    have hZother : ∀ Q, Q ≠ R' → Z Q = N Q := by
      intro Q hQ
      rw [hZapply]
      simp [Ne.symm hQ]
    have hZeff : EffectiveDivisor Z := by
      intro Q
      by_cases hQ : Q = R'
      · rw [hQ, hZR']
      · rw [hZother Q hQ]
        exact hNeff Q
    have hZne : ∀ Q, Z Q ≠ 0 → Q ≠ R' ∧ N Q ≠ 0 := fun Q hQ => by
      have hQR : Q ≠ R' := fun h => hQ (h ▸ hZR')
      exact ⟨hQR, by rwa [hZother Q hQR] at hQ⟩
    have hZexc : ∀ Q, Z Q ≠ 0 → IsExceptionalCurve R.π Q := by
      intro Q hQ
      obtain ⟨hQR, hNQ⟩ := hZne Q hQ
      refine Classical.byContradiction (fun hext' => ?_)
      exact hQR (hother_ext Q hNQ hext')
    have hNdecomp : N = Z + Finsupp.single R' 1 := by
      rw [hZdef]
      abel
    have hdegN' : ∀ Q, degW R Q N = degW R Q Z +
        (Q.intersectionNumber (R.S.primeCurveCartier R.hreg R') : ℚ) := by
      intro Q
      conv_lhs => rw [hNdecomp]
      rw [degW_add, degW_single]
      push_cast
      ring
    -- `R' ≠ P` (manuscript lines 2431–2433)
    have hR'P : R' ≠ P := by
      intro hRP
      have hZP : Z P = 0 := by
        rw [← hRP]
        exact hZR'
      have key : ∀ (E : R.Vertices), R.contact P E = 1 → degW R E.val N = 0 → Z E.val ≠ 0 := by
        intro E hPE hdeg hZE
        have h1 := degW_nonneg_of_coeff_eq_zero R E.val Z hZeff hZE
        have h2 := hdegN' E.val
        rw [hRP, inter_contact' R P E hPE, hdeg] at h2
        linarith only [h1, h2]
      have hZC' := key C hPC dNC
      have hZB₁' := key B₁ hPB₁ dNB₁
      have h3 : (2 : ℚ) ≤ degW R P Z := by
        rw [degW_eq_sum]
        have hterm : ∀ Q ∈ Z.support,
            0 ≤ (Z Q : ℚ) * (P.intersectionNumber (R.S.primeCurveCartier R.hreg Q) : ℚ) := by
          intro Q hQ
          have hQP : P ≠ Q := fun h => (Finsupp.mem_support_iff.mp hQ) (h ▸ hZP)
          exact mul_nonneg (by exact_mod_cast hZeff Q) (inter_nonneg R P Q hQP)
        have hC1 : (1 : ℚ) ≤ Z C.val := by
          have := hZeff C.val
          exact_mod_cast (show (1 : ℤ) ≤ Z C.val by omega)
        have hB1 : (1 : ℚ) ≤ Z B₁.val := by
          have := hZeff B₁.val
          exact_mod_cast (show (1 : ℤ) ≤ Z B₁.val by omega)
        have hle := Finset.add_le_sum
          (f := fun Q => (Z Q : ℚ) * (P.intersectionNumber (R.S.primeCurveCartier R.hreg Q) : ℚ))
          hterm (Finsupp.mem_support_iff.mpr hZC') (Finsupp.mem_support_iff.mpr hZB₁')
          (vertex_ne_of_ne R hCB₁)
        simp only [iPC, iPB₁, mul_one] at hle
        linarith only [hle, hC1, hB1]
      have h4 := hdegN' P
      rw [hRP, iPP, dNP] at h4
      linarith only [h3, h4]
    -- `R' · P = Z · P = 0`; `C, B₁, B₂ ∉ Z`; `R'` and `Z` are disjoint from `C, B₁, B₂`
    have hNP0 : N P = 0 := by
      refine Classical.byContradiction (fun h => ?_)
      exact hR'P (hother_ext P h hP.1.2).symm
    have hZP : Z P = 0 := by
      rw [hZother P (Ne.symm hR'P)]
      exact hNP0
    have hPR'nonneg := inter_nonneg R P R' (Ne.symm hR'P)
    have hZPnonneg := degW_nonneg_of_coeff_eq_zero R P Z hZeff hZP
    have hPR' : (P.intersectionNumber (R.S.primeCurveCartier R.hreg R') : ℚ) = 0 := by
      have h := hdegN' P
      rw [dNP] at h
      linarith only [h, hPR'nonneg, hZPnonneg]
    have hdegPZ : degW R P Z = 0 := by
      have h := hdegN' P
      rw [dNP] at h
      linarith only [h, hPR'nonneg, hZPnonneg]
    have hZcompP : ∀ Q, Z Q ≠ 0 → (P.intersectionNumber (R.S.primeCurveCartier R.hreg Q) : ℚ) = 0 :=
      inter_eq_zero_of_degW_eq_zero R P Z hZeff hZP hdegPZ
    have hZC : Z C.val = 0 := by
      refine Classical.byContradiction (fun h => ?_)
      have := hZcompP _ h
      rw [iPC] at this
      exact one_ne_zero this
    have hZB₁ : Z B₁.val = 0 := by
      refine Classical.byContradiction (fun h => ?_)
      have := hZcompP _ h
      rw [iPB₁] at this
      exact one_ne_zero this
    have hZB₂ : Z B₂.val = 0 := by
      refine Classical.byContradiction (fun h => ?_)
      have := hZcompP _ h
      rw [iPB₂] at this
      exact one_ne_zero this
    have hsplit : ∀ (E : R.Vertices), Z E.val = 0 → degW R E.val N = 0 →
        ((E.val).intersectionNumber (R.S.primeCurveCartier R.hreg R') : ℚ) = 0 ∧
        ∀ Q, Z Q ≠ 0 → ((E.val).intersectionNumber (R.S.primeCurveCartier R.hreg Q) : ℚ) = 0 := by
      intro E hZE hdeg
      have h1 := degW_nonneg_of_coeff_eq_zero R E.val Z hZeff hZE
      have h2 := inter_nonneg R E.val R' (fun h => hR'ext (h ▸ E.property))
      have h3 := hdegN' E.val
      rw [hdeg] at h3
      have hER' : ((E.val).intersectionNumber (R.S.primeCurveCartier R.hreg R') : ℚ) = 0 := by
        linarith only [h1, h2, h3]
      have hEZ : degW R E.val Z = 0 := by linarith only [h1, h2, h3]
      exact ⟨hER', inter_eq_zero_of_degW_eq_zero R E.val Z hZeff hZE hEZ⟩
    obtain ⟨iCR', hZcompC⟩ := hsplit C hZC dNC
    obtain ⟨iB₁R', hZcompB₁⟩ := hsplit B₁ hZB₁ dNB₁
    obtain ⟨iB₂R', hZcompB₂⟩ := hsplit B₂ hZB₂ dNB₂
    -- `R'` is a `(-1)`-curve: `N · R' = K_S · R' < 0` forces `R'² < 0`; adjunction
    have hKR' := Kdeg_neg_of_not_exceptional R R' hR'ext
    have hR'T : degW R R' T = 0 := by
      rw [hTdef, degW_cubDiv, inter_comm R R' C.val, iCR', inter_comm R R' B₁.val, iB₁R',
        inter_comm R R' B₂.val, iB₂R', inter_comm R R' P, hPR']
      push_cast
      ring
    have hdegR'N : degW R R' N = (R.Kdeg R' : ℚ) := by rw [hdegN, hR'T, add_zero]
    have hR'Znonneg := degW_nonneg_of_coeff_eq_zero R R' Z hZeff hZR'
    have hself : (R'.intersectionNumber (R.S.primeCurveCartier R.hreg R') : ℚ) =
        (R'.selfIntersectionNumber R.hreg : ℚ) := by
      rw [← curveClass_pairing_eq_intersectionNumber, curveClass_self_pairing]
    have hsqneg : R'.selfIntersectionNumber R.hreg < 0 := by
      have h := hdegN' R'
      rw [hdegR'N] at h
      have hK' : (R.Kdeg R' : ℚ) < 0 := by exact_mod_cast hKR'
      have hlt : (R'.intersectionNumber (R.S.primeCurveCartier R.hreg R') : ℚ) < 0 := by
        linarith only [h, hK', hR'Znonneg]
      rw [hself] at hlt
      exact_mod_cast hlt
    haveI : FiniteDimensional ℚ R.S.NumericalClassGroup :=
      SurfaceNumericalFinitenessProved.numericalClassGroup_finite R.S R.hreg
    have hR'minus : IsMinusOneCurve R.hreg R' :=
      KltDP.Manuscript.S03.NefThresholdCore.isMinusOneCurve_of_neg R.S R.hreg R.KS R.eKS R' hsqneg
        hKR'
    have hR'ext1 : R.IsExteriorMinusOne R' := ⟨hR'minus, hR'ext⟩
    have iR'R' := inter_self_minusOne R R' hR'minus
    have hKR'1 : (R.Kdeg R' : ℚ) = -1 := by
      rw [Kdeg_eq_neg_one_of_isMinusOne R R' hR'minus]
      norm_num
    -- `Z · R' = 0`, and `Z · A = K_S · A ≥ 0` on the components of `Z`: `Z = 0`
    have hR'Z : degW R R' Z = 0 := by
      have h := hdegN' R'
      rw [hdegR'N, hKR'1, iR'R'] at h
      linarith only [h]
    have hZcompR' : ∀ Q, Z Q ≠ 0 →
        (R'.intersectionNumber (R.S.primeCurveCartier R.hreg Q) : ℚ) = 0 :=
      inter_eq_zero_of_degW_eq_zero R R' Z hZeff hZR' hR'Z
    have hZ0 : Z = 0 := by
      apply eq_zero_of_exceptional_of_square_nonneg R Z hZexc
      rw [pairing_numW_eq_sum]
      refine Finset.sum_nonneg (fun Q hQ => mul_nonneg (by exact_mod_cast hZeff Q) ?_)
      have hQ' : Z Q ≠ 0 := Finsupp.mem_support_iff.mp hQ
      have h1 := hdegN' Q
      rw [inter_comm, hZcompR' Q hQ', add_zero] at h1
      have h2 : degW R Q T = 0 := by
        rw [hTdef, degW_cubDiv, inter_comm R Q C.val, hZcompC Q hQ', inter_comm R Q B₁.val,
          hZcompB₁ Q hQ', inter_comm R Q B₂.val, hZcompB₂ Q hQ', inter_comm R Q P, hZcompP Q hQ']
        push_cast
        ring
      rw [← h1, hdegN, h2, add_zero]
      exact Kdeg_nonneg_of_exceptional R Q (hZexc Q hQ')
    have hNsingle : N = Finsupp.single R' 1 := by rw [hNdecomp, hZ0, zero_add]
    have hlin' : R.S.LinearlyEquivalent (Finsupp.single R' 1) (R.S.cartierToWeilHom R.KS + T) := by
      rw [← hNsingle]
      exact hNlin
    -- the remaining clauses (manuscript lines 2435–2445)
    have hLR' : R.Ldeg R' = 2 * R.Ldeg P - R.Lsq := by
      rw [← hLN, hNsingle, LdegW_eq_pairing, numW_single, LinearMap.BilinForm.smul_right,
        Lnum_pairing_curveClass]
      push_cast
      ring
    have hvℓ : R.Lsq ≤ R.Ldeg P := by
      have := KltDP.Manuscript.S03.Ldeg_ge_of_not_exceptional R hrho P hP R' hR'ext
      linarith only [this, hLR']
    have hpic : R.curvePic R' = cartierPicardClass R.S.toScheme R.KS * R.curvePic C.val *
        R.curvePic B₁.val * R.curvePic B₂.val * R.curvePic P ^ 2 := by
      have h := picW_eq_of_linearlyEquivalent R hlin'
      rw [picW_single] at h
      rw [h]
      have e : Finsupp.single P (2 : ℤ) = Finsupp.single P 1 + Finsupp.single P 1 := by
        rw [← Finsupp.single_add]
        norm_num
      simp only [hTdef, cubDiv, e, R.S.regularWeilPicardClass_add, picW_KS, picW_single, mul_assoc,
        sq]
    have hdegR'single : ∀ Q, degW R Q N =
        (Q.intersectionNumber (R.S.primeCurveCartier R.hreg R') : ℚ) := by
      intro Q
      rw [hNsingle, degW_single]
      push_cast
      ring
    have hcontact : ∀ i : R.Vertices, i ≠ C → i ≠ B₁ → i ≠ B₂ →
        (R.contact R' i : ℚ) = (R.w i - 2) +
          ((R.contact C.val i : ℚ) + (R.contact B₁.val i : ℚ) + (R.contact B₂.val i : ℚ)) := by
      intro i hiC hi1 hi2
      have h1 := hdegR'single i.val
      rw [hdegN, hTdef, degW_cubDiv] at h1
      have hiP : ((i.val).intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) = 0 := by
        rw [inter_comm]
        exact_mod_cast hother i hiC hi1 hi2
      rw [hiP, R.Kdeg_exceptional] at h1
      unfold ResolutionDatum.q at h1
      push_cast at h1
      show (R'.intersectionNumber (R.S.primeCurveCartier R.hreg i.val) : ℚ) = _
      rw [inter_comm R R' i.val, ← h1]
      unfold ResolutionDatum.contact
      rw [inter_comm R C.val i.val, inter_comm R B₁.val i.val, inter_comm R B₂.val i.val]
      ring
    have hedge : ∃ i : R.Vertices, R.graph.Adj C i ∨ R.graph.Adj B₁ i ∨ R.graph.Adj B₂ i := by
      refine Classical.byContradiction (fun hno => ?_)
      push_neg at hno
      obtain ⟨i, hi⟩ := exists_excess_contact R p hp0 R' hR'ext1
      unfold IsExcessContact ResolutionDatum.q at hi
      rw [contactVector_eq] at hi
      have hcR' : ∀ j : R.Vertices, (R.contact R' j : ℚ) =
          ((j.val).intersectionNumber (R.S.primeCurveCartier R.hreg R') : ℚ) := by
        intro j
        unfold ResolutionDatum.contact
        rw [inter_comm]
      by_cases hiC : i = C
      · rw [hiC, hcR', iCR', hwC] at hi
        norm_num at hi
      by_cases hi1 : i = B₁
      · rw [hi1, hcR', iB₁R', hwB₁] at hi
        norm_num at hi
      by_cases hi2 : i = B₂
      · rw [hi2, hcR', iB₂R'] at hi
        linarith only [hi, hβ3]
      have h := hcontact i hiC hi1 hi2
      have hC0 : (R.contact C.val i : ℚ) = 0 := by
        unfold ResolutionDatum.contact
        rw [inter_vertices, M_eq_zero_of_not_adj R (Ne.symm hiC) (hno i).1]
      have hB₁0 : (R.contact B₁.val i : ℚ) = 0 := by
        unfold ResolutionDatum.contact
        rw [inter_vertices, M_eq_zero_of_not_adj R (Ne.symm hi1) (hno i).2.1]
      have hB₂0 : (R.contact B₂.val i : ℚ) = 0 := by
        unfold ResolutionDatum.contact
        rw [inter_vertices, M_eq_zero_of_not_adj R (Ne.symm hi2) (hno i).2.2]
      rw [h, hC0, hB₁0, hB₂0] at hi
      linarith only [hi]
    exact ⟨⟨C, B₁, B₂, β, R', hβ, hwC, hwB₁, hwB₂, hPC, hPB₁, hPB₂, hother, hCB₁, hCB₂, hB₁B₂,
      hnCB₁, hnCB₂, hnB, hreach, hval, hR'ext1, hpic,
      disjoint_of_inter_eq_zero R R' C.val (exterior_ne_vertex R R' hR'ext C)
        (by rw [inter_comm]; exact iCR'),
      disjoint_of_inter_eq_zero R R' B₁.val (exterior_ne_vertex R R' hR'ext B₁)
        (by rw [inter_comm]; exact iB₁R'),
      disjoint_of_inter_eq_zero R R' B₂.val (exterior_ne_vertex R R' hR'ext B₂)
        (by rw [inter_comm]; exact iB₂R'),
      disjoint_of_inter_eq_zero R R' P hR'P (by rw [inter_comm]; exact hPR'),
      hLR', R.Lsq_pos, hvℓ, hcontact, hedge⟩⟩

/-! ### Theorem 7.1 -/

/-- **Manuscript Theorem 7.1 (`thm:adjoint-reduction`, lines 2324–2445)**, conditional form: the
two inputs still being formalized are the explicit hypotheses `hTwo` (Theorem 7.5,
`thm:two-contact-ruling`) and `hIso` (Theorem 4.6, `thm:isolated-node-exchange`). -/
theorem singleExteriorAdjointReduction_of (R : ResolutionDatum k) (p : ℕ) [CharP k p] (hp : 2 < p)
    (hR : R.IsMinimalCounterexample)
    (hTwo : ∀ P, R.IsShortestExteriorMinusOne P → TwoContactRulingHyp R P)
    (hIso : IsolatedExchangeHyp R) :
    ∃ P : R.S.PrimeCurve, R.IsShortestExteriorMinusOne P ∧ AdjointConfiguration R P := by
  classical
  have hp0 : 0 < p := by omega
  -- (1) `ρ(S) ≥ 9` and a shortest exterior `(-1)`-curve
  have hrho : 2 < R.S.picardRank := by
    have := (ResolutionDatum.IsMinimalCounterexample.canonicalSquare_le_one_and_picardRank R hR p
      hp0).2
    omega
  obtain ⟨P, hP⟩ := KltDP.Manuscript.S03.exists_shortestExteriorMinusOne R hrho
  refine ⟨P, hP, ?_⟩
  have hcount : ¬ R.X.singularPoints.card ≤ 7 := by
    have := hR.1
    omega
  -- (5) an excess contact exists, hence a weight-two contact
  obtain ⟨C, hwC, hPC⟩ : ∃ C : R.Vertices, R.w C = 2 ∧ R.contact P C = 1 := by
    obtain ⟨i, hi⟩ := exists_excess_contact R p hp0 P hP.1
    have hle := contact_le_one R p hp hrho P hP hcount i
    have hpos := contact_pos_of_excess R P i hi
    rw [contactVector_eq] at hpos
    have hpos' : 0 < R.contact P i := by exact_mod_cast hpos
    have hc1 : R.contact P i = 1 := by omega
    refine ⟨i, ?_, hc1⟩
    unfold IsExcessContact ResolutionDatum.q at hi
    rw [contactVector_eq, hc1] at hi
    push_cast at hi
    rcases w_eq_two_or_three_le R i with hw | hw
    · exact hw
    · linarith
  by_cases hmore : ∃ V : R.Vertices, V ≠ C ∧ R.w V = 2 ∧ R.contact P V ≠ 0
  · -- (6)–(8) two weight-two contacts
    exfalso
    obtain ⟨V, hVC, hwV, hPV0⟩ := hmore
    have hPV : R.contact P V = 1 := by
      rcases contact_eq_zero_or_one R p hp hrho P hP hcount V with h | h
      · exact absurd h hPV0
      · exact h
    have honly : ∀ i, R.w i = 2 → R.contact P i ≠ 0 → i = C ∨ i = V := by
      intro i hwi hi
      refine Classical.byContradiction (fun hno => ?_)
      push_neg at hno
      have hPi : R.contact P i = 1 := by
        rcases contact_eq_zero_or_one R p hp hrho P hP hcount i with h | h
        · exact absurd h hi
        · exact h
      exact not_three_weightTwo_contacts R p hp hrho P hP hcount C V i hVC.symm (Ne.symm hno.1)
        (Ne.symm hno.2) hwC hwV hwi hPC hPV hPi
    exact not_two_weightTwo_contacts R p hp hrho P hP hcount (hTwo P hP) C V hVC.symm hwC hwV hPC
      hPV honly
  · -- (9)–(12) exactly one weight-two contact
    push_neg at hmore
    have honly : ∀ i, R.w i = 2 → R.contact P i ≠ 0 → i = C := by
      intro i hwi hi
      refine Classical.byContradiction (fun hiC => ?_)
      exact hi (hmore i hiC hwi)
    obtain ⟨B, B', hne, hwB, hwB', hPB, hPB', hother, hreach, hval⟩ :=
      one_weightTwo_contact R p hp hrho P hP hcount hIso hR.2 C hwC hPC honly
    have hBC : B ≠ C := fun h => by
      rw [h, hwC] at hwB
      norm_num at hwB
    have hB'C : B' ≠ C := fun h => by
      rw [h, hwC] at hwB'
      norm_num at hwB'
    -- (10) `C` is adjacent to neither `B` nor `B'`
    have hnBC : ¬ R.graph.Adj B C :=
      not_adj_higher_contact R p hrho P hP hp0 B C B' hwB hwC hPB hPC hPB' hne.symm hB'C
    have hnB'C : ¬ R.graph.Adj B' C :=
      not_adj_higher_contact R p hrho P hP hp0 B' C B hwB' hwC hPB' hPC hPB hne hBC
    have hnBB' : ¬ R.graph.Adj B B' := fun h => hreach h.reachable
    -- the weights `(3, β)`
    rcases weights_of_two_higher_contacts R P hP.1 B B' hne hwB hwB' hPB hPB' with
      ⟨h3, hβ⟩ | ⟨h3, hβ⟩
    · obtain ⟨β, hβ', hwβ⟩ : ∃ β : ℕ, (β = 3 ∨ β = 4 ∨ β = 5) ∧ R.w B' = β := by
        rcases hβ with h | h | h
        · exact ⟨3, Or.inl rfl, by rw [h]; norm_num⟩
        · exact ⟨4, Or.inr (Or.inl rfl), by rw [h]; norm_num⟩
        · exact ⟨5, Or.inr (Or.inr rfl), by rw [h]; norm_num⟩
      exact adjointConfiguration_of_core R p hp hrho hcount P hP C B B' β hβ' hwC h3 hwβ hPC hPB
        hPB' hother hBC.symm hB'C.symm hne (fun h => hnBC h.symm) (fun h => hnB'C h.symm) hnBB'
        hreach hval
    · obtain ⟨β, hβ', hwβ⟩ : ∃ β : ℕ, (β = 3 ∨ β = 4 ∨ β = 5) ∧ R.w B = β := by
        rcases hβ with h | h | h
        · exact ⟨3, Or.inl rfl, by rw [h]; norm_num⟩
        · exact ⟨4, Or.inr (Or.inl rfl), by rw [h]; norm_num⟩
        · exact ⟨5, Or.inr (Or.inr rfl), by rw [h]; norm_num⟩
      exact adjointConfiguration_of_core R p hp hrho hcount P hP C B' B β hβ' hwC h3 hwβ hPC hPB'
        hPB (fun i h1 h2 h3 => hother i h1 h3 h2) hB'C.symm hBC.symm hne.symm
        (fun h => hnB'C h.symm) (fun h => hnBC h.symm) (fun h => hnBB' h.symm)
        (fun h => hreach h.symm) hval

end KltDP.Manuscript.S07

#print axioms KltDP.Manuscript.S07.singleExteriorAdjointReduction_of

import KltDP.Manuscript.S07.AdjointConfiguration
import KltDP.Manuscript.Main.SevenPointBound
import KltDP.Manuscript.S04.DiscrepancyLemmas
import KltDP.Manuscript.S05.PicardIndex
import KltDP.Manuscript.S02.Projection
import KltDP.Lattices.TenForestLatticeReduction
import KltDP.Support.WeightedForestCore

/-!
# Theorem 8.3: the single exterior adjoint configuration is impossible

Manuscript `source/manuscript.tex`, Theorem 8.3 (`thm:forest-exclusion`, lines 2780–2842):
the configuration of Theorem 7.1 (`AdjointConfiguration R P`) cannot occur on a minimal
counterexample in positive characteristic different from two.

Proof, following the manuscript:

1. *Extra weights.* For a vertex `A ∉ {C, B₁, B₂}` of weight `b`, the adjoint identity of the
   configuration gives `R'·A = b − 2 + (C + B₁ + B₂)·A ≥ b − 2`. The discrepancy sum of the
   exterior `(−1)`-curve `R'` is `Σ λ_i (R'·D_i) = 1 − L·R' = 1 − 2ℓ + v < 1`
   (`rankOneProjection_charge`, `L·R' = 2ℓ − v`, `0 < v ≤ ℓ`), and every term is nonnegative.
   With `λ_A ≥ (b−2)/b` (`elementaryDiscrepancyBound`) this forces `(b−2)²/b < 1`, so `b ≤ 3`;
   each extra weight-three vertex contributes at least `1/3`, so there are at most two.
2. *Graph data.* Valency `≤ 3` (`exceptionalValencyAtMostThree`); `C` has valency `≤ 1`, the
   three marked vertices are pairwise non-adjacent and `B₁, B₂` are in different components
   (all from the configuration); the exceptional graph is a forest whose components are the
   singular points (`exceptional_forest_and_singular_count_from_klt`), so with `n(X) ≥ 8`
   singular points `#edges = #V − n(X) ≤ β − 1` (`forest_card_edges`).
3. *Counts.* Pairing `K_S` with `R' ~ K_S + C + B₁ + B₂ + 2P` gives `K_S² = 2 − β`; Noether
   `K_S² + ρ(S) = 10` and `ρ(S) = 1 + #V` give `#V = β + 7`.
4. *Scalar identities.* `λ = A⁻¹q`, `v = 2 − β + qᵀλ`, `ℓ = 1 − pᵀλ`, `v ≤ ℓ`,
   `v (pᵀA⁻¹p − 1) = ℓ²` (`Lsq_eq_Ksq_add_dot`, `rankOneProjection_charge/green`).
5. *Lattice data* (`exists_picard_lattice_data`) and the union's abstract endgame
   `ten_forest_integral_half_sum`: only row A2 survives, with `β = 3` and a class
   `m ∈ Pic S` with `2m = W₁ + W₂ + W₃ + W₄` for four isolated weight-two vertices.
6. Theorem 5.1 in class form (`isolated_nodes_no_half_sum`, `p > 2`) excludes it.

Everything is derived from the datum and the compiled union; nothing is assumed beyond the
hypotheses of the theorem.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Codes KltDP.LinearAlgebra KltDP.Lattices.SmallADEForestLattice
open KltDP.Lattices.TenForestLatticeReduction
open KltDP.Manuscript
open scoped BigOperators

universe u

namespace KltDP.Manuscript.S08

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)

local instance integralSource (T : NormalProjectiveSurface k) : IsIntegral T.toScheme := T.integral

/-! ### Auxiliary datum lemmas -/

/-- The natural-number weight `b_i = -D_i²` of an exceptional curve. -/
def natWeight (i : R.Vertices) : ℕ := (-(i.val.selfIntersectionNumber R.hreg)).toNat

/-- The rational weight `R.w i` is the cast of the natural weight. -/
theorem natWeight_cast (i : R.Vertices) : (natWeight R i : ℚ) = R.w i := by
  have hw := S05.w_eq_neg_selfIntersection R i
  have h2 : (2 : ℚ) ≤ -(i.val.selfIntersectionNumber R.hreg : ℚ) := by
    rw [← hw]; exact R.two_le_w i
  have hnn : (0 : ℤ) ≤ -(i.val.selfIntersectionNumber R.hreg) := by
    have h : (0 : ℚ) ≤ ((-(i.val.selfIntersectionNumber R.hreg) : ℤ) : ℚ) := by
      push_cast
      linarith
    exact_mod_cast h
  rw [hw, natWeight, ← Int.cast_natCast, Int.toNat_of_nonneg hnn]
  exact Int.cast_neg _

/-- Distinct prime curves meet nonnegatively: `X · D_j ≥ 0` for `X ≠ D_j`. -/
theorem contact_nonneg (X : R.S.PrimeCurve) (j : R.Vertices) (hne : X ≠ j.val) :
    0 ≤ R.contact X j := by
  have h := PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg R.S R.hreg X j.val hne
  rwa [PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber
    R.S R.hreg X j.val] at h

/-- `K_S · X` as the integral Picard pairing of `[K_S]` with `[X]`. -/
theorem pairing_Kcls_primeClass (X : R.S.PrimeCurve) :
    R.S.integralPicardIntersectionBilinForm R.hreg (S05.Kcls R) (S05.primeClass R X) =
      R.Kdeg X := by
  rw [integralPicardIntersectionBilinForm_apply]
  simp only [S05.Kcls, S05.primeClass, cartierPicardHom_apply, toMul_ofMul]
  rw [R.S.picardPairing_class R.hreg, R.S.intersectionPairing_primeCurve R.hreg]
  rfl

/-- `K_S²` as the integral Picard pairing of `[K_S]` with itself. -/
theorem pairing_Kcls_Kcls :
    R.S.integralPicardIntersectionBilinForm R.hreg (S05.Kcls R) (S05.Kcls R) =
      R.S.intersectionPairing R.hreg R.KS R.KS := by
  rw [integralPicardIntersectionBilinForm_apply]
  simp only [S05.Kcls, cartierPicardHom_apply]
  exact R.S.picardPairing_class R.hreg R.KS R.KS

/-! ### Theorem 8.3 -/

/-- **Manuscript Theorem 8.3 (`thm:forest-exclusion`, lines 2780–2842).** The single exterior
adjoint configuration of Theorem 7.1 cannot occur on a minimal counterexample in
characteristic `p > 2`. -/
theorem singleAdjointForestImpossible (R : ResolutionDatum k) (P : R.S.PrimeCurve)
    (p : ℕ) [CharP k p] (hp : 2 < p)
    (hR : R.IsMinimalCounterexample) (hP : R.IsShortestExteriorMinusOne P)
    (hconf : AdjointConfiguration R P) : False := by
  classical
  obtain ⟨C, B₁, B₂, β, R', hβ, hwC, hwB₁, hwB₂, hPC, hPB₁, hPB₂, hPother, hCB₁, hCB₂, hB₁B₂,
    hnadjCB₁, hnadjCB₂, hnadjB₁B₂, hsep, huniq, hR', hpicId, _, _, _, _, hLR', hv0, hvl,
    hcontR', hboundary⟩ := hconf.exists_data
  have hp0 : 0 < p := by omega
  /- notation: natural weights, the weight matrix, the contact vector of `P` -/
  have hWv : ∀ v : R.Vertices, (natWeight R v : ℚ) = R.w v := natWeight_cast R
  have hW : (fun v : R.Vertices => (natWeight R v : ℚ)) = R.w := funext hWv
  have hq : (fun v : R.Vertices => (natWeight R v : ℚ) - 2) = R.q := by
    funext v
    rw [hWv]
    rfl
  have hAeq : graphWeightMatrix R.graph (fun v : R.Vertices => (natWeight R v : ℚ)) = R.A := by
    rw [hW]
    exact R.A_eq_graphWeightMatrix.symm
  have hcv : S02.contactVector R P = S05.contact R P := rfl
  have hsrc : (threeMarkedSource C B₁ B₂ : R.Vertices → ℚ) = S05.contact R P := by
    funext i
    simp only [threeMarkedSource, Pi.add_apply]
    show _ = ((R.contact P i : ℤ) : ℚ)
    by_cases hiC : i = C
    · rw [hiC, Pi.single_eq_same, Pi.single_eq_of_ne hCB₁, Pi.single_eq_of_ne hCB₂, hPC]
      norm_num
    by_cases hiB₁ : i = B₁
    · rw [hiB₁, Pi.single_eq_of_ne hCB₁.symm, Pi.single_eq_same, Pi.single_eq_of_ne hB₁B₂, hPB₁]
      norm_num
    by_cases hiB₂ : i = B₂
    · rw [hiB₂, Pi.single_eq_of_ne hCB₂.symm, Pi.single_eq_of_ne hB₁B₂.symm, Pi.single_eq_same,
        hPB₂]
      norm_num
    rw [Pi.single_eq_of_ne hiC, Pi.single_eq_of_ne hiB₁, Pi.single_eq_of_ne hiB₂,
      hPother i hiC hiB₁ hiB₂]
    norm_num
  /- forest structure and the singular-point count -/
  obtain ⟨_, hsing, hG, _⟩ := R.hmin.exceptional_forest_and_singular_count_from_klt R.hklt
  /- Step 1: the discrepancy sum of `R'` is `< 1` and each term is nonnegative -/
  have hcharge : dotProduct (S02.contactVector R R') R.lam = 1 - R.Ldeg R' :=
    S02.rankOneProjection_charge R R' hR'
  have hsum_lt : dotProduct (S02.contactVector R R') R.lam < 1 := by
    rw [hcharge, hLR']
    linarith
  have hterm_nonneg : ∀ j : R.Vertices, 0 ≤ S02.contactVector R R' j * R.lam j := by
    intro j
    apply mul_nonneg _ (R.lam_nonneg j)
    show (0 : ℚ) ≤ (R.contact R' j : ℚ)
    exact_mod_cast contact_nonneg R R' j (fun h => hR'.2 (by rw [h]; exact j.property))
  have hcont : ∀ i : R.Vertices, i ≠ C → i ≠ B₁ → i ≠ B₂ →
      R.w i - 2 ≤ S02.contactVector R R' i := by
    intro i hiC hiB₁ hiB₂
    have h := hcontR' i hiC hiB₁ hiB₂
    have h1 : (0 : ℚ) ≤ (R.contact C.val i : ℚ) := by
      exact_mod_cast contact_nonneg R C.val i (fun h => hiC (Subtype.ext h.symm))
    have h2 : (0 : ℚ) ≤ (R.contact B₁.val i : ℚ) := by
      exact_mod_cast contact_nonneg R B₁.val i (fun h => hiB₁ (Subtype.ext h.symm))
    have h3 : (0 : ℚ) ≤ (R.contact B₂.val i : ℚ) := by
      exact_mod_cast contact_nonneg R B₂.val i (fun h => hiB₂ (Subtype.ext h.symm))
    show R.w i - 2 ≤ (R.contact R' i : ℚ)
    rw [h]
    linarith
  -- every other vertex has weight `< 4`
  have hbig : ∀ i : R.Vertices, i ≠ C → i ≠ B₁ → i ≠ B₂ → R.w i < 4 := by
    intro i hiC hiB₁ hiB₂
    by_contra hcon
    push_neg at hcon
    have hlam := S04.elementaryDiscrepancyBound R i (by linarith)
    have hc := hcont i hiC hiB₁ hiB₂
    have hwpos : 0 < R.w i := by linarith
    have h1 : 1 ≤ (R.w i - 2) / R.w i * (R.w i - 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hwpos]
      nlinarith [mul_nonneg (sub_nonneg.2 hcon) (by linarith : (0 : ℚ) ≤ R.w i - 1)]
    have h2 : (R.w i - 2) / R.w i * (R.w i - 2) ≤ R.lam i * S02.contactVector R R' i :=
      mul_le_mul hlam hc (by linarith) (R.lam_nonneg i)
    have h3 : R.lam i * S02.contactVector R R' i ≤ dotProduct (S02.contactVector R R') R.lam := by
      rw [mul_comm]
      simp only [dotProduct]
      exact Finset.single_le_sum (fun j _ => hterm_nonneg j) (Finset.mem_univ i)
    linarith
  have hother : ∀ v : R.Vertices, v ≠ C → v ≠ B₁ → v ≠ B₂ →
      natWeight R v = 2 ∨ natWeight R v = 3 := by
    intro v hvC hvB₁ hvB₂
    have h4 := hbig v hvC hvB₁ hvB₂
    have h2 := R.two_le_w v
    rw [← hWv v] at h4 h2
    have h4' : natWeight R v < 4 := by exact_mod_cast h4
    have h2' : 2 ≤ natWeight R v := by exact_mod_cast h2
    omega
  -- at most two extra weight-three vertices
  have hextraCard : (candidateExtraVertices (natWeight R) C B₁ B₂).card ≤ 2 := by
    have hterm3 : ∀ i ∈ candidateExtraVertices (natWeight R) C B₁ B₂,
        (1 : ℚ) / 3 ≤ S02.contactVector R R' i * R.lam i := by
      intro i hi
      rw [mem_candidateExtraVertices] at hi
      obtain ⟨hiC, hiB₁, hiB₂, hw3⟩ := hi
      have hw3' : R.w i = 3 := by
        rw [← hWv i, hw3]
        norm_num
      have hlam := S04.elementaryDiscrepancyBound R i hw3'.symm.le
      rw [hw3'] at hlam
      have hc := hcont i hiC hiB₁ hiB₂
      rw [hw3'] at hc
      norm_num at hlam hc
      nlinarith [mul_nonneg (sub_nonneg.2 hc) (R.lam_nonneg i)]
    have hle : ∑ i ∈ candidateExtraVertices (natWeight R) C B₁ B₂,
        S02.contactVector R R' i * R.lam i ≤ dotProduct (S02.contactVector R R') R.lam := by
      simp only [dotProduct]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => hterm_nonneg j)
    have hcard := Finset.card_nsmul_le_sum _ _ _ hterm3
    rw [nsmul_eq_mul] at hcard
    have h3 : ((candidateExtraVertices (natWeight R) C B₁ B₂).card : ℚ) < 3 := by linarith
    have h3' : (candidateExtraVertices (natWeight R) C B₁ B₂).card < 3 := by exact_mod_cast h3
    omega
  /- Step 2: graph data -/
  have hC : natWeight R C = 2 := by
    have h := hwC
    rw [← hWv C] at h
    exact_mod_cast h
  have hB : natWeight R B₁ = 3 := by
    have h := hwB₁
    rw [← hWv B₁] at h
    exact_mod_cast h
  have hD : natWeight R B₂ = β := by
    have h := hwB₂
    rw [← hWv B₂] at h
    exact_mod_cast h
  have hdegreeC : R.graph.degree C ≤ 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_le_one.mpr (fun a ha b hb =>
      huniq a b ((R.graph.mem_neighborFinset C a).1 ha) ((R.graph.mem_neighborFinset C b).1 hb))
  have hdegree : ∀ v : R.Vertices, R.graph.degree v ≤ 3 :=
    fun v => S04.exceptionalValencyAtMostThree R v
  /- Step 3: `K_S² = 2 − β`, `#V = β + 7`, `#edges ≤ β − 1` -/
  have hadd : S05.primeClass R R' = S05.Kcls R + S05.cls R C + S05.cls R B₁ + S05.cls R B₂ +
      S05.primeClass R P + S05.primeClass R P := by
    show Additive.ofMul (R.curvePic R') =
      Additive.ofMul (cartierPicardClass R.S.toScheme R.KS) + Additive.ofMul (R.curvePic C.val) +
        Additive.ofMul (R.curvePic B₁.val) + Additive.ofMul (R.curvePic B₂.val) +
        Additive.ofMul (R.curvePic P) + Additive.ofMul (R.curvePic P)
    rw [hpicId, pow_two, ← mul_assoc, ofMul_mul, ofMul_mul, ofMul_mul, ofMul_mul, ofMul_mul]
  have hKP : (R.Kdeg P : ℚ) = -1 := by
    rw [S02.Kdeg_eq_neg_one_of_isMinusOne R P hP.1.1]
    norm_num
  have hKR' : (R.Kdeg R' : ℚ) = -1 := by
    rw [S02.Kdeg_eq_neg_one_of_isMinusOne R R' hR'.1]
    norm_num
  have hQ : ((R.S.integralPicardIntersectionBilinForm R.hreg (S05.Kcls R)
      (S05.primeClass R R') : ℤ) : ℚ) = (R.Kdeg R' : ℚ) := by
    rw [pairing_Kcls_primeClass]
  rw [hadd, map_add, map_add, map_add, map_add, map_add, pairing_Kcls_Kcls,
    pairing_Kcls_primeClass] at hQ
  push_cast at hQ
  rw [S05.pairing_Kcls_cls R C, S05.pairing_Kcls_cls R B₁, S05.pairing_Kcls_cls R B₂, hwC, hwB₁,
    hwB₂, hKP, hKR'] at hQ
  have hKsq : (R.S.intersectionPairing R.hreg R.KS R.KS : ℚ) = 2 - (β : ℚ) := by linarith
  have hKsqZ : R.S.intersectionPairing R.hreg R.KS R.KS = 2 - (β : ℤ) := by exact_mod_cast hKsq
  have hnoether := R.hmin.noetherRelation_of_kltDelPezzo R.hDP R.hrank p hp0 R.KS R.eKS
  change R.S.intersectionPairing R.hreg R.KS R.KS + (R.S.picardRank : ℤ) = 10 at hnoether
  have hpic := R.hmin.picardRank_eq_of_klt R.hklt p hp0
  rw [R.hrank] at hpic
  have hV : Nat.card (ActualExceptionalIncidence.Vertices R.π) = Fintype.card R.Vertices :=
    Nat.card_eq_fintype_card
  have hcard : Fintype.card R.Vertices = β + 7 := by omega
  have hedgecount := KltDP.Support.WeightedForestCore.forest_card_edges R.graph hG
  have hcomp : R.X.singularPoints.card = Fintype.card R.graph.ConnectedComponent := by
    rw [hsing]
    exact Nat.card_eq_fintype_card
  have hedges : R.graph.edgeFinset.card ≤ β - 1 := by
    have h7 := hR.1
    omega
  /- Step 4: the scalar identities -/
  have hA : (graphWeightMatrix R.graph (fun v : R.Vertices => (natWeight R v : ℚ))).PosDef := by
    rw [hAeq]
    exact R.A_posDef
  have hsolve : R.lam = (graphWeightMatrix R.graph (fun v : R.Vertices => (natWeight R v : ℚ)))⁻¹ *ᵥ
      (fun v : R.Vertices => (natWeight R v : ℚ) - 2) := by
    rw [hAeq, hq]
    exact (S02.A_inv_mulVec_q R).symm
  have hcoeffBounds : ∀ v : R.Vertices, 0 ≤ R.lam v ∧ R.lam v < 1 :=
    fun v => ⟨R.lam_nonneg v, R.lam_lt_one v⟩
  have hKsqQ : R.Ksq = 2 - (β : ℚ) := by
    rw [R.Ksq_eq_intersectionPairing]
    exact hKsq
  have hLsq : R.Lsq = 2 - (β : ℚ) +
      dotProduct (fun v : R.Vertices => (natWeight R v : ℚ) - 2) R.lam := by
    rw [hq, R.Lsq_eq_Ksq_add_dot, hKsqQ]
  have hcharge_P : dotProduct (S05.contact R P) R.lam = 1 - R.Ldeg P := by
    rw [← hcv]
    exact S02.rankOneProjection_charge R P hP.1
  have hgreen : dotProduct (S05.contact R P) (R.A⁻¹ *ᵥ S05.contact R P) =
      1 + R.Ldeg P ^ 2 / R.Lsq := by
    rw [← hcv]
    exact S02.rankOneProjection_green R p hp0 P hP.1
  have hvolume : 0 < 2 - (β : ℚ) +
      dotProduct (fun v : R.Vertices => (natWeight R v : ℚ) - 2) R.lam := by
    rw [← hLsq]
    exact hv0
  have hbudget : 2 - (β : ℚ) +
      dotProduct (fun v : R.Vertices => (natWeight R v : ℚ) - 2) R.lam ≤
      1 - dotProduct (threeMarkedSource C B₁ B₂) R.lam := by
    rw [← hLsq, hsrc, hcharge_P]
    linarith
  have hprojection : (2 - (β : ℚ) +
      dotProduct (fun v : R.Vertices => (natWeight R v : ℚ) - 2) R.lam) *
      (dotProduct (threeMarkedSource C B₁ B₂)
        ((graphWeightMatrix R.graph (fun v : R.Vertices => (natWeight R v : ℚ)))⁻¹ *ᵥ
          threeMarkedSource C B₁ B₂) - 1) =
      (1 - dotProduct (threeMarkedSource C B₁ B₂) R.lam) ^ 2 := by
    rw [← hLsq, hsrc, hAeq, hgreen, hcharge_P]
    have hv' : R.Lsq ≠ 0 := ne_of_gt hv0
    field_simp
  /- Step 5: the lattice data and the abstract endgame -/
  obtain ⟨b, hunimod, hchar, hK, hGram⟩ := S05.exists_picard_lattice_data R p hp0 P hP.1.1
  have hK' : ∀ x : R.Vertices,
      (R.S.integralPicardIntersectionBilinForm R.hreg (S05.Kcls R) (S05.cls R x) : ℚ) =
        (natWeight R x : ℚ) - 2 := by
    intro x
    rw [hWv]
    exact hK x
  have hGram' : (familyGram (R.S.integralPicardIntersectionBilinForm R.hreg)
      (Sum.elim (S05.cls R) (fun _ : Unit => S05.primeClass R P))).map (fun z : ℤ => (z : ℚ)) =
      borderedGram (graphWeightMatrix R.graph (fun v : R.Vertices => (natWeight R v : ℚ)))
        (threeMarkedSource C B₁ B₂) (-1) := by
    rw [hAeq, hsrc]
    exact hGram
  obtain ⟨_, T, u, v, _, _, _, _, _, _, _, _, _, hrest⟩ :=
    ten_forest_integral_half_sum R.graph (natWeight R) R.lam C B₁ B₂ β hβ hcard hG hC hB hD
      hother hextraCard hnadjCB₁ hnadjCB₂ hnadjB₁B₂ hsep hdegreeC hdegree hedges hboundary hA
      hsolve hcoeffBounds hvolume hbudget hprojection b
      (R.S.integralPicardIntersectionBilinForm R.hreg) hunimod (S05.cls R) (S05.primeClass R P)
      (S05.Kcls R) hchar hK' hGram'
  obtain ⟨hcard4, hiso, -, m, hm, -, -⟩ := hrest
  /- Step 6: the four isolated nodes contradict Theorem 5.1 -/
  refine S05.isolated_nodes_no_half_sum R p hp (Finset.univ \ {u, v, C, T, B₁, B₂}) ?_ ?_ ?_
    ⟨m, hm⟩
  · exact Finset.card_pos.mp (by rw [hcard4]; norm_num)
  · intro W hW
    have h2 := (hiso W hW).1
    rw [← hWv W, h2]
    norm_num
  · intro W hW
    exact (hiso W hW).2

end KltDP.Manuscript.S08

#print axioms KltDP.Manuscript.S08.singleAdjointForestImpossible

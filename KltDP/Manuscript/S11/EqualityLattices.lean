import KltDP.Manuscript.S11.EqualityAdjoints
import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
# Corollary 11.3 (`cor:equality-lattice`, manuscript lines 3336–3361):
# intersection lattices at equality

For the resolution datum `R = (S_{3,3}, X, π)` of the seven-point surface (`S11/NegativeCurves`):

* `K_S² = -1` (`datum_Ksq`), ten original exceptional components (`card_vertices`), three
  original edges and seven connected components of the exceptional graph
  (`graph_card_edgeFinset`, `graph_card_connectedComponent`), no isolated exceptional nodes
  (`graph_no_isolated_node`), `det A_D = 3^7` (`datum_A_det`), `ℓ = L² = 1/3`, the discrepancy
  coefficients `λ_B = λ_{F_i} = 1/3`, `λ_{U_i} = λ_{V_i} = 0` (`datum_lam`), and the consistency
  `L² = K_S² + qᵀ A_D⁻¹ q = -1 + 4/3` (`datum_Lsq_eq_Ksq_add`);
* at every shortest centre `P_i`: `pᵀ A_D⁻¹ p = 4/3` (`datum_green_newest`),
  `|det ⟨D, P_i⟩| = 3^6` (`datum_borderedGram_newest`), and the full Picard index
  `[Pic S : ⟨D, P_i⟩] = 27` (`datum_index_newest`), through `S05.fullPicardIndexObstruction`.

The same values at the centres `T_i` are the lattice statements `contactT_green`,
`borderedGram_contactT_det` of the union; the actual curves `T_i` are not in the union
(see `S11/NegativeCurves`). The remark on the single-adjoint table for `β = 3`
(lines 3349–3351) is not formalized. The optimality statement (line 3338) is the seven singular
points of `sevenPointNegativeCurves` together with Theorem 1.1 (`Main/SevenPointBound`).
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Examples KltDP.Examples.FrobeniusMultiCentreSurface
open KltDP.Examples.FrobeniusMultiCentreIntegral KltDP.Examples.FrobeniusProjectivityProved
open KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
open KltDP.Examples.FrobeniusMultiCentreCanonicalWeilRepresentatives
open KltDP.Examples.FrobeniusMultiCentreContractingNef
open KltDP.Examples.FrobeniusMultiCentreContractingClass
open KltDP.Examples.FrobeniusMultiCentreExceptionalPrime
open KltDP.Examples.FrobeniusMultiCentrePicardRealization
open KltDP.Geometry.PrimeCurveClassPairing
open KltDP.Geometry.PrimeCurvePairingSupport
open KltDP.Geometry.InvertibleSheafSectionPowers
open KltDP.LinearAlgebra
open KltDP.Manuscript KltDP.Manuscript.S10
open KltDP.Support.EqualityNumbers

universe u

namespace KltDP.Manuscript.S11

/-- Dot products are invariant under a simultaneous reindexing. -/
theorem dotProduct_comp_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (u w : β → ℚ) :
    dotProduct (u ∘ e) (w ∘ e) = dotProduct u w := by
  show ∑ i, u (e i) * w (e i) = ∑ j, u j * w j
  exact Equiv.sum_comp e (fun j => u j * w j)

/-- `A_D⁻¹ q = (1/3, 1/3, 1/3, 1/3, 0, …, 0)`: the discrepancy coefficients of the seven-point
surface (line 3220, "all four higher-weight coefficients are `1/3`"). -/
theorem negMatrixQ_inv_mulVec_canonicalSource :
    negMatrixQ⁻¹ *ᵥ canonicalSourceQ = fun v => Sum.elim (fun _ => (1 / 3 : ℚ)) (fun _ => 0) v := by
  rw [negMatrixQ_inv, negMatrixInvQ_eq_smul, Matrix.smul_mulVec_assoc]
  have h : negMatrixInv3 *ᵥ canonicalSource = Sum.elim (fun _ => 1) (fun _ => 0) := by decide
  have hc : negMatrixInv3.map (Int.cast : ℤ → ℚ) *ᵥ canonicalSourceQ =
      fun v => ((negMatrixInv3 *ᵥ canonicalSource) v : ℚ) := by
    funext v
    exact ((Int.castRingHom ℚ).map_mulVec negMatrixInv3 canonicalSource v).symm
  rw [hc, h]
  funext v
  rcases v with j | c <;> simp

section Geometry

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 3]

local instance factPrimeThreeL : Fact (2 + 1).Prime := ⟨Nat.prime_three⟩

local instance {k : Type u} [Field k] (T : NormalProjectiveSurface k) :
    IsLocallyNoetherian T.toScheme := T.isLocallyNoetherian

variable (a : Fin 3 → k) (ha : Function.Injective a)

/-- The intersection matrix of the retained curves, as Cartier pairings. -/
theorem intersectionPairing_retained (l l' : RetainedLabel 2 3) :
    (sevenSurface a ha).intersectionPairing (sevenRegular a ha) (retainedDiv a ha l)
      (retainedDiv a ha l') = gram 2 3 l l' := by
  rw [intersectionPairing_primeCurves_eq_intersectionNumber, retainedCurve_intersectionNumber]

variable (Y : NormalProjectiveSurface k) (π : (sevenSurface a ha).toScheme ⟶ Y.toScheme)
    (hπ : π ≫ Y.structureMorphism = multiStructure (2 + 1) 3 a)
    (hcriterion : ∀ C : (sevenSurface a ha).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
        C.restrictionDegree (originalLine 2 3 a ha) = 0)
    (hmin : IsMinimalResolution (sevenSurface a ha) Y π) (hDP : IsKltDelPezzo Y)
    (hrank : Y.picardRank = 1)

local notation "R₀" => datum a ha Y π hmin hDP hrank
local notation "ι₀" => vertexIndex a ha Y π hπ hcriterion hmin hDP hrank
local notation "e₀" => labelEquiv a ha Y π hπ hcriterion hmin hDP hrank

/-- **`K_S² = -1`** (line 3339). -/
theorem datum_Ksq : (R₀).Ksq = -1 := by
  rw [(R₀).Ksq_eq_intersectionPairing]
  have h1 : (sevenSurface a ha).intersectionPairing (sevenRegular a ha) (R₀).KS (R₀).KS =
      pairing (sevenSurface a ha) (sevenRegular a ha)
        (cartierPicardHom (sevenSurface a ha).toScheme (R₀).KS)
        (cartierPicardHom (sevenSurface a ha).toScheme (R₀).KS) :=
    (picardPairing_class (sevenSurface a ha) (sevenRegular a ha) _ _).symm
  change ((sevenSurface a ha).intersectionPairing (sevenRegular a ha) (R₀).KS (R₀).KS : ℚ) = -1
  rw [h1, datum_KS_class a ha Y π hmin hDP hrank]
  have h2 : pairing (sevenSurface a ha) (sevenRegular a ha) (latticeClass a ha Kvec)
      (latticeClass a ha Kvec) = FrobeniusPicard.pairing Kvec Kvec :=
    realization_preserves_pairing 2 3 a ha (sevenProj a) Kvec Kvec
  have h3 : FrobeniusPicard.pairing Kvec Kvec = -1 := by decide
  rw [h2, h3]
  norm_num

include hπ hcriterion in
/-- **`det A_D = 3^7 = 2187`** (line 3340). -/
theorem datum_A_det [DecidableEq (R₀).Vertices] : (R₀).A.det = 3 ^ 7 := by
  rw [A_eq_submatrix a ha Y π hπ hcriterion hmin hDP hrank, Matrix.det_submatrix_equiv_self,
    negMatrixQ_det]
  norm_num

include hπ hcriterion in
theorem datum_A_inv [DecidableEq (R₀).Vertices] :
    (R₀).A⁻¹ = negMatrixQ⁻¹.submatrix ι₀ ι₀ := by
  rw [A_eq_submatrix a ha Y π hπ hcriterion hmin hDP hrank, Matrix.inv_submatrix_equiv]

include hπ hcriterion in
/-- **`pᵀ A_D⁻¹ p = 4/3` at every shortest centre `P_i`** (line 3343). -/
theorem datum_green_newest [DecidableEq (R₀).Vertices] (i : Fin 3) :
    dotProduct (S05.contact R₀ (newestCurveP 2 3 a ha i))
      ((R₀).A⁻¹ *ᵥ S05.contact R₀ (newestCurveP 2 3 a ha i)) = 4 / 3 := by
  rw [datum_A_inv a ha Y π hπ hcriterion hmin hDP hrank,
    contact_newest a ha Y π hπ hcriterion hmin hDP hrank i, Matrix.submatrix_mulVec_equiv]
  have h1 : (fun v => contactPQ i (ι₀ v)) ∘ (ι₀).symm = contactPQ i := by
    funext w
    simp
  rw [h1]
  exact (dotProduct_comp_equiv ι₀ (contactPQ i) (negMatrixQ⁻¹ *ᵥ contactPQ i)).trans
    (contactP_green i)

include hπ hcriterion hmin hDP hrank in
/-- **The full Picard index at every shortest centre is `27`** (line 3345):
`[Pic S : ⟨D, P_i⟩] = 27`, from `S05.fullPicardIndexObstruction`
(`I² = det A_D · (pᵀA_D⁻¹p - 1) = 3^7 · (1/3) = 3^6`). -/
theorem datum_index_newest (i : Fin 3) :
    ((sevenSurface a ha).exceptionalExteriorPicardSpan π (sevenRegular a ha)
      (newestCurveP 2 3 a ha i)).toAddSubgroup.index = 27 := by
  classical
  obtain ⟨h1, -, -⟩ := S05.fullPicardIndexObstruction R₀ 3 (by norm_num) (newestCurveP 2 3 a ha i)
    (newestCurveP_isMinusOne a ha i) (newestCurveP_not_exceptional 2 3 a ha Y π hπ hcriterion i)
  rw [datum_A_det a ha Y π hπ hcriterion hmin hDP hrank,
    datum_green_newest a ha Y π hπ hcriterion hmin hDP hrank i] at h1
  have h2 : (((R₀).S.exceptionalExteriorPicardSpan (R₀).π (R₀).hreg
      (newestCurveP 2 3 a ha i)).toAddSubgroup.index : ℚ) ^ 2 = ((27 : ℕ) : ℚ) ^ 2 := by
    rw [h1]
    norm_num
  have h3 : ((R₀).S.exceptionalExteriorPicardSpan (R₀).π (R₀).hreg
      (newestCurveP 2 3 a ha i)).toAddSubgroup.index ^ 2 = 27 ^ 2 := by
    exact_mod_cast h2
  exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h3

include hπ hcriterion in
/-- **`|det ⟨D, P_i⟩| = 3^6 = 729`** (line 3344): the bordered Gram determinant at a shortest
centre. -/
theorem datum_borderedGram_newest [DecidableEq (R₀).Vertices] (i : Fin 3) :
    |(borderedGram (R₀).A (S05.contact R₀ (newestCurveP 2 3 a ha i)) (-1)).det| = 3 ^ 6 := by
  have h := S05.index_sq_eq_abs_det_borderedGram R₀ 3 (by norm_num) (newestCurveP 2 3 a ha i)
    (newestCurveP_isMinusOne a ha i) (newestCurveP_not_exceptional 2 3 a ha Y π hπ hcriterion i)
  rw [← h]
  have h27 : ((R₀).S.exceptionalExteriorPicardSpan (R₀).π (R₀).hreg
      (newestCurveP 2 3 a ha i)).toAddSubgroup.index = 27 :=
    datum_index_newest a ha Y π hπ hcriterion hmin hDP hrank i
  rw [h27]
  norm_num

/-! ### The discrepancy coefficients -/

include hπ hcriterion in
/-- `q = (1, 1, 1, 1, 0, …, 0)`: the canonical degrees `b_i - 2`. -/
theorem datum_q_eq : (R₀).q = fun v => canonicalSourceQ (ι₀ v) := by
  funext v
  obtain ⟨l, rfl⟩ := (e₀).surjective v
  rw [ResolutionDatum.q, w_labelEquiv a ha Y π hπ hcriterion hmin hDP hrank,
    vertexIndex_labelEquiv]
  generalize toIndex l = w
  rcases w with j | ⟨c, i⟩ <;> norm_num [weight, canonicalSourceQ, canonicalSource]

include hπ hcriterion in
/-- **The discrepancy coefficients**: `λ_B = λ_{F_i} = 1/3` and `λ_{U_i} = λ_{V_i} = 0`
(line 3220; Proposition 10.1 at `(p, n) = (3, 3)`), computed from `A_D λ = q`. -/
theorem datum_lam :
    (R₀).lam = fun v => Sum.elim (fun _ => (1 / 3 : ℚ)) (fun _ => 0) (ι₀ v) := by
  classical
  rw [← S02.A_inv_mulVec_q R₀, datum_A_inv a ha Y π hπ hcriterion hmin hDP hrank,
    datum_q_eq a ha Y π hπ hcriterion hmin hDP hrank, Matrix.submatrix_mulVec_equiv]
  have h1 : (fun v => canonicalSourceQ (ι₀ v)) ∘ (ι₀).symm = canonicalSourceQ := by
    funext w
    simp
  rw [h1, negMatrixQ_inv_mulVec_canonicalSource]
  rfl

include hπ hcriterion in
/-- `qᵀ A_D⁻¹ q = qᵀ λ = 4/3`. -/
theorem datum_q_dot_lam : dotProduct (R₀).q (R₀).lam = 4 / 3 := by
  rw [datum_lam a ha Y π hπ hcriterion hmin hDP hrank, datum_q_eq a ha Y π hπ hcriterion hmin hDP hrank]
  show dotProduct (canonicalSourceQ ∘ ι₀)
    ((fun v => Sum.elim (fun _ => (1 / 3 : ℚ)) (fun _ => 0) v) ∘ ι₀) = 4 / 3
  rw [dotProduct_comp_equiv, ← negMatrixQ_inv_mulVec_canonicalSource]
  exact canonicalSource_green

include hπ hcriterion in
/-- **`L² = K_S² + qᵀ A_D⁻¹ q = -1 + 4/3 = 1/3`** (lines 3339–3340 through the manuscript's
formula `L² = K_S² + q·λ`). -/
theorem datum_Lsq_eq_Ksq_add : (R₀).Lsq = -1 + 4 / 3 := by
  rw [(R₀).Lsq_eq_Ksq_add_dot, datum_Ksq, datum_q_dot_lam a ha Y π hπ hcriterion hmin hDP hrank]

/-! ### The exceptional graph: three edges, seven components, no isolated nodes -/

include hπ hcriterion in
/-- Adjacency in the exceptional graph is a nonzero off-diagonal intersection number. -/
theorem graph_adj_iff (l l' : RetainedLabel 2 3) :
    (R₀).graph.Adj (e₀ l) (e₀ l') ↔ l ≠ l' ∧ gram 2 3 l l' ≠ 0 := by
  change e₀ l ≠ e₀ l' ∧
    ((retainedCurve 2 3 a ha l : Set (sevenSurface a ha).toScheme) ∩
      (retainedCurve 2 3 a ha l' : Set (sevenSurface a ha).toScheme)).Nonempty ↔ _
  rw [(e₀).injective.ne_iff, ← Set.not_disjoint_iff_nonempty_inter]
  have hCE : l ≠ l' → retainedCurve 2 3 a ha l ≠ retainedCurve 2 3 a ha l' :=
    fun hne h => hne (retainedCurve_injective 2 3 a ha (by norm_num) h)
  constructor
  · rintro ⟨hne, hnd⟩
    refine ⟨hne, fun h0 => hnd ?_⟩
    exact (intersectionPairing_primeCurves_eq_zero_iff_disjoint (sevenSurface a ha)
      (sevenRegular a ha) _ _ (hCE hne)).mp ((intersectionPairing_retained a ha l l').trans h0)
  · rintro ⟨hne, h0⟩
    refine ⟨hne, fun hd => h0 ?_⟩
    rw [← intersectionPairing_retained a ha l l']
    exact (intersectionPairing_primeCurves_eq_zero_iff_disjoint (sevenSurface a ha)
      (sevenRegular a ha) _ _ (hCE hne)).mpr hd

include hπ hcriterion in
/-- **The exceptional graph is the graph read off `negMatrix`** (`Support.EqualityNumbers.dualGraph`). -/
def graphIso : (R₀).graph ≃g dualGraph where
  toEquiv := ι₀
  map_rel_iff' := by
    intro v w
    obtain ⟨l, rfl⟩ := (e₀).surjective v
    obtain ⟨l', rfl⟩ := (e₀).surjective w
    rw [graph_adj_iff]
    change (ι₀ (e₀ l) ≠ ι₀ (e₀ l') ∧ negMatrix (ι₀ (e₀ l)) (ι₀ (e₀ l')) ≠ 0) ↔ _
    rw [vertexIndex_labelEquiv, vertexIndex_labelEquiv, ← gram_eq_negMatrix, neg_ne_zero]
    exact and_congr_left' labelIndexEquiv.injective.ne_iff

include hπ hcriterion in
/-- **Three original edges** (line 3340). -/
theorem graph_card_edgeFinset [DecidableRel (R₀).graph.Adj] [Fintype (R₀).graph.edgeSet] :
    (R₀).graph.edgeFinset.card = 3 := by
  rw [SimpleGraph.Iso.card_edgeFinset_eq (graphIso a ha Y π hπ hcriterion hmin hDP hrank)]
  convert dualGraph_card_edgeFinset

include hπ hcriterion in
/-- **Seven connected components** of the exceptional forest (`10 - 3 = 7`, line 3360): the
seven singular points. -/
theorem graph_card_connectedComponent : Nat.card (R₀).graph.ConnectedComponent = 7 := by
  rw [Nat.card_congr (graphIso a ha Y π hπ hcriterion hmin hDP hrank).connectedComponentEquiv]
  exact card_connectedComponent

include hπ hcriterion in
/-- **No isolated exceptional nodes** (line 3347): every weight-two vertex has a neighbour. -/
theorem graph_no_isolated_node (v : (R₀).Vertices) (hv : (R₀).w v = 2) :
    ∃ u, (R₀).graph.Adj v u := by
  obtain ⟨l, rfl⟩ := (e₀).surjective v
  rw [w_labelEquiv a ha Y π hπ hcriterion hmin hDP hrank] at hv
  have hv' : negMatrix (toIndex l) (toIndex l) = 2 := by
    rw [negMatrix_diag]
    exact_mod_cast hv
  obtain ⟨j, hj, hne⟩ := negMatrix_no_isolated_node (toIndex l) hv'
  refine ⟨(ι₀).symm j, ?_⟩
  rw [← (graphIso a ha Y π hπ hcriterion hmin hDP hrank).map_rel_iff]
  change dualGraph.Adj (ι₀ (e₀ l)) (ι₀ ((ι₀).symm j))
  rw [Equiv.apply_symm_apply, vertexIndex_labelEquiv]
  exact ⟨fun h => hj h.symm, hne⟩

end Geometry

/-! ### The corollary, assembled -/

section Existence

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 3]

local instance factPrimeThreeLE : Fact (2 + 1).Prime := ⟨Nat.prime_three⟩

local instance {k : Type u} [Field k] (T : NormalProjectiveSurface k) :
    IsLocallyNoetherian T.toScheme := T.isLocallyNoetherian

/-- **Corollary 11.3, formalized part.** For the resolution datum of the seven-point surface:
seven singular points, `K_S² = -1`, ten original exceptional components, three original edges and
seven components of the exceptional graph (no isolated nodes), `det A_D = 3^7`, `ℓ = L² = 1/3`
(also as `K_S² + qᵀA_D⁻¹q = -1 + 4/3`), and at every shortest centre `P_i`:
`pᵀ A_D⁻¹ p = 4/3`, `|det ⟨D, P_i⟩| = 3^6`, `[Pic S : ⟨D, P_i⟩] = 27`. -/
theorem sevenPointLattices (a : Fin 3 → k) (ha : Function.Injective a) :
    ∃ (X : NormalProjectiveSurface k) (π : (sevenSurface a ha).toScheme ⟶ X.toScheme)
      (hmin : IsMinimalResolution (sevenSurface a ha) X π) (hDP : IsKltDelPezzo X)
      (hrank : X.picardRank = 1),
      X.singularPoints.card = 7 ∧
      (datum a ha X π hmin hDP hrank).Ksq = -1 ∧
      Fintype.card (datum a ha X π hmin hDP hrank).Vertices = 10 ∧
      Nat.card (datum a ha X π hmin hDP hrank).graph.ConnectedComponent = 7 ∧
      (∀ v, (datum a ha X π hmin hDP hrank).w v = 2 →
        ∃ u, (datum a ha X π hmin hDP hrank).graph.Adj v u) ∧
      (datum a ha X π hmin hDP hrank).Lsq = 1 / 3 ∧
      (datum a ha X π hmin hDP hrank).Lsq = -1 + 4 / 3 ∧
      (∃ ι : (datum a ha X π hmin hDP hrank).Vertices ≃ Index,
        (datum a ha X π hmin hDP hrank).A = negMatrixQ.submatrix ι ι ∧
        (datum a ha X π hmin hDP hrank).lam = fun v =>
          Sum.elim (fun _ => (1 / 3 : ℚ)) (fun _ => 0) (ι v)) ∧
      (∀ i : Fin 3,
        ((sevenSurface a ha).exceptionalExteriorPicardSpan π (sevenRegular a ha)
          (newestCurveP 2 3 a ha i)).toAddSubgroup.index = 27) ∧
      (∀ (_ : DecidableEq (datum a ha X π hmin hDP hrank).Vertices),
        (datum a ha X π hmin hDP hrank).A.det = 3 ^ 7 ∧
        ∀ i : Fin 3,
          dotProduct (S05.contact (datum a ha X π hmin hDP hrank) (newestCurveP 2 3 a ha i))
            ((datum a ha X π hmin hDP hrank).A⁻¹ *ᵥ
              S05.contact (datum a ha X π hmin hDP hrank) (newestCurveP 2 3 a ha i)) = 4 / 3 ∧
          |(borderedGram (datum a ha X π hmin hDP hrank).A
            (S05.contact (datum a ha X π hmin hDP hrank) (newestCurveP 2 3 a ha i)) (-1)).det|
            = 3 ^ 6) ∧
      (∀ (_ : DecidableRel (datum a ha X π hmin hDP hrank).graph.Adj)
        (_ : Fintype (datum a ha X π hmin hDP hrank).graph.edgeSet),
        (datum a ha X π hmin hDP hrank).graph.edgeFinset.card = 3) := by
  have hn : 2 < 3 := by norm_num
  letI : IsIntegral (multiSurface (2 + 1) 3 a) := multiSurface_isIntegral (2 + 1) 3 a ha
  obtain ⟨m, hm, X, π, hπ, hproper, hsurj, hbir, hc, hgeom,
      hpoints, hcriterion, A, hA, ⟨e⟩, hdim, hrank, hminimal,
      hKlt, hIsKlt, hsing, hcard, hcount⟩ :=
    exists_normal_projective_surface_rank_one_klt_exact_singular_count 2 3 a ha hn
  letI : IsProper π := hproper
  letI : Surjective π := hsurj
  letI : IsIso π.c := hc
  have hDP : IsKltDelPezzo X :=
    (target_isKltDelPezzo_iff_parameters 2 3 a ha hn X π hπ hbir hpoints hcriterion A m hm e hA).mpr
      (Or.inr ⟨rfl, rfl⟩)
  have hLsq : (datum a ha X π hminimal hDP hrank).Lsq = 1 / 3 := by
    have h := S01.lsq_frobenius_datum 2 3 a ha hn X π hπ hbir hpoints hcriterion A m hm e
      hminimal hDP hrank
    change (ResolutionDatum.mk (sevenSurface a ha) X π hminimal hDP hrank).Lsq = 1 / 3
    rw [h]
    norm_num
  refine ⟨X, π, hminimal, hDP, hrank, hcard, datum_Ksq a ha X π hminimal hDP hrank,
    card_vertices a ha X π hπ hcriterion hminimal hDP hrank,
    graph_card_connectedComponent a ha X π hπ hcriterion hminimal hDP hrank,
    graph_no_isolated_node a ha X π hπ hcriterion hminimal hDP hrank,
    hLsq, datum_Lsq_eq_Ksq_add a ha X π hπ hcriterion hminimal hDP hrank,
    ⟨vertexIndex a ha X π hπ hcriterion hminimal hDP hrank,
      A_eq_submatrix a ha X π hπ hcriterion hminimal hDP hrank,
      datum_lam a ha X π hπ hcriterion hminimal hDP hrank⟩,
    datum_index_newest a ha X π hπ hcriterion hminimal hDP hrank,
    fun _ => ⟨datum_A_det a ha X π hπ hcriterion hminimal hDP hrank,
      fun i => ⟨datum_green_newest a ha X π hπ hcriterion hminimal hDP hrank i,
        datum_borderedGram_newest a ha X π hπ hcriterion hminimal hDP hrank i⟩⟩,
    fun _ _ => graph_card_edgeFinset a ha X π hπ hcriterion hminimal hDP hrank⟩

end Existence

end KltDP.Manuscript.S11

#print axioms KltDP.Manuscript.S11.datum_Ksq
#print axioms KltDP.Manuscript.S11.datum_index_newest
#print axioms KltDP.Manuscript.S11.datum_lam
#print axioms KltDP.Manuscript.S11.graph_card_connectedComponent
#print axioms KltDP.Manuscript.S11.sevenPointLattices

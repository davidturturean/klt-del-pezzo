import KltDP.LinearAlgebra.TenForestRowUniqueness
import KltDP.LinearAlgebra.ABNonvacuity
import KltDP.LinearAlgebra.FamilyCNonvacuity
import KltDP.LinearAlgebra.FamilyDNonvacuity
import KltDP.LinearAlgebra.FamilyDPositiveDefinite
import KltDP.LinearAlgebra.FamilyENonvacuity

/-!
# Original-hypothesis nonvacuity of all ten candidate rows

Each witness uses the actual finite graph and source vectors already
constructed in the family witness modules. The source predicate lists
only the original classifier hypotheses; the selected row is a separate
proved conclusion. No geometric realization is asserted.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exactly the original input conditions of `ten_forest_classification`.
This conjunction contains no row classification, determinant-table
conclusion, graph isomorphism or literature axiom. -/
def TenForestOriginalHypotheses (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (coeff : V → ℚ) (C B D : V) (β : ℕ) : Prop :=
  (β = 3 ∨ β = 4 ∨ β = 5) ∧ Fintype.card V = β + 7 ∧ G.IsAcyclic ∧
  weight C = 2 ∧ weight B = 3 ∧ weight D = β ∧
  (∀ v, v ≠ C → v ≠ B → v ≠ D → weight v = 2 ∨ weight v = 3) ∧
  (candidateExtraVertices weight C B D).card ≤ 2 ∧
  ¬ G.Adj C B ∧ ¬ G.Adj C D ∧ ¬ G.Adj B D ∧ ¬ G.Reachable B D ∧
  G.degree C ≤ 1 ∧ (∀ v, G.degree v ≤ 3) ∧ G.edgeFinset.card ≤ β - 1 ∧
  (∃ v, G.Adj C v ∨ G.Adj B v ∨ G.Adj D v) ∧
  (graphWeightMatrix G (fun v => (weight v : ℚ))).PosDef ∧
  coeff = (graphWeightMatrix G (fun v => (weight v : ℚ)))⁻¹ *ᵥ
    (fun v => (weight v : ℚ) - 2) ∧
  (∀ v, 0 ≤ coeff v ∧ coeff v < 1) ∧
  0 < 2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff ∧
  2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff ≤
    1 - dotProduct (threeMarkedSource C B D) coeff ∧
  (2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff) *
    (dotProduct (threeMarkedSource C B D)
      ((graphWeightMatrix G (fun v => (weight v : ℚ)))⁻¹ *ᵥ
        threeMarkedSource C B D) - 1) =
    (1 - dotProduct (threeMarkedSource C B D) coeff)^2

theorem TenForestOriginalHypotheses.classification
    {G : SimpleGraph V} [DecidableRel G.Adj] {weight : V → ℕ} {coeff : V → ℚ}
    {C B D : V} {β : ℕ} (h : TenForestOriginalHypotheses G weight coeff C B D β) :
    TenForestRows G weight coeff C B D β := by
  rcases h with ⟨hβ, hcard, hG, hC, hB, hD, hother, hextra, hCB, hCD, hBD,
    hseparate, hdegC, hdeg, hedges, hboundary, hA, hsolve, hcoeff, hv, hbudget, hproj⟩
  exact ten_forest_classification G weight coeff C B D β hβ hcard hG hC hB hD hother
    hextra hCB hCD hBD hseparate hdegC hdeg hedges hboundary hA hsolve hcoeff hv hbudget hproj

/-- A proved determinant identifies which actual classified row occurs.
The complete original input conjunction is still required and retained. -/
theorem TenForestOriginalHypotheses.realized_of_determinant
    {G : SimpleGraph V} [DecidableRel G.Adj] {weight : V → ℕ} {coeff : V → ℚ}
    {C B D : V} {β : ℕ} (h : TenForestOriginalHypotheses G weight coeff C B D β)
    (row : TenForestRow)
    (hd : (graphWeightMatrix G (fun i => (weight i : ℚ))).det = row.exceptionalDet) :
    row.Realized G weight coeff C B D β := by
  obtain ⟨actual, ha⟩ := TenForestRows.exists_realized G weight coeff C B D β h.classification
  have heq : actual = row := TenForestRow.exceptionalDet_injective
    (ha.values.2.2.2.2.1.symm.trans hd)
  exact heq ▸ ha

namespace TenForestNonvacuity

private theorem det_transport {V : Type*} [Fintype V] [DecidableEq V]
    (A B : Matrix V V ℚ) (hAB : A = B) (d : ℚ) (hd : B.det = d) : A.det = d :=
  (congrArg Matrix.det hAB).trans hd

private theorem three_constant : (2 : ℚ) - 3 = -1 := by norm_num
private theorem four_constant : (2 : ℚ) - 4 = -2 := by norm_num

/-- Transport scalar data before specializing the matrix index type. -/
private theorem scalar_data_transport
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ)
    (coeff : V → ℚ) (C B D : V) (β : ℕ)
    (A : Matrix V V ℚ) (q p : V → ℚ) (k : ℚ)
    (hA : graphWeightMatrix G (fun v => (weight v : ℚ)) = A)
    (hq : (fun v => (weight v : ℚ) - 2) = q)
    (hp : threeMarkedSource C B D = p) (hk : 2 - (β : ℚ) = k)
    (hsolve : coeff = A⁻¹ *ᵥ q)
    (hv : 0 < k + dotProduct q coeff)
    (hb : k + dotProduct q coeff ≤ 1 - dotProduct p coeff)
    (hproj : (k + dotProduct q coeff) * (dotProduct p (A⁻¹ *ᵥ p) - 1) =
      (1 - dotProduct p coeff)^2) :
    coeff = (graphWeightMatrix G (fun v => (weight v : ℚ)))⁻¹ *ᵥ
      (fun v => (weight v : ℚ) - 2) ∧
    0 < 2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff ∧
    2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff ≤
      1 - dotProduct (threeMarkedSource C B D) coeff ∧
    (2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff) *
      (dotProduct (threeMarkedSource C B D)
        ((graphWeightMatrix G (fun v => (weight v : ℚ)))⁻¹ *ᵥ
          threeMarkedSource C B D) - 1) =
      (1 - dotProduct (threeMarkedSource C B D) coeff)^2 := by
  rw [hA, hq, hp, hk]
  exact ⟨hsolve, hv, hb, hproj⟩

private theorem det_value_trans (A : Matrix V V ℚ) (a b : ℚ)
    (ha : A.det = a) (hab : a = b) : A.det = b := ha.trans hab

/- Apply each determinant theorem and normalize its scalar result while the
vertex type is abstract. Concrete complement enumerations are instantiated
only after the complete equality has been proved. -/
private theorem empty_det_of_scalar
    (G : SimpleGraph V) [DecidableRel G.Adj] (he : G.edgeFinset = ∅)
    (d : ℚ) (hd : 2 ^ Fintype.card V = d) :
    (graphWeightMatrix G (fun _ => (2 : ℚ))).det = d :=
  (canonical_empty_det G he).trans hd

private theorem single_edge_det_of_scalar
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) (hxy : x ≠ y)
    (he : G.edgeFinset = {s(x, y)})
    (d : ℚ) (hd : 3 * 2 ^ (Fintype.card V - 2) = d) :
    (graphWeightMatrix G (fun _ => (2 : ℚ))).det = d :=
  (canonical_single_edge_det G x y hxy he).trans hd

private theorem two_path_det_of_scalar
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y z : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (he : G.edgeFinset = {s(x, y), s(y, z)})
    (d : ℚ) (hd : 4 * 2 ^ (Fintype.card V - 3) = d) :
    (graphWeightMatrix G (fun _ => (2 : ℚ))).det = d :=
  (canonical_two_path_det G x y z hxy hxz hyz he).trans hd

private theorem disjoint_edges_det_of_scalar
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y z w : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (he : G.edgeFinset = {s(x, y), s(z, w)})
    (d : ℚ) (hd : 9 * 2 ^ (Fintype.card V - 4) = d) :
    (graphWeightMatrix G (fun _ => (2 : ℚ))).det = d :=
  (canonical_disjoint_edges_det G x y z w hxy hxz hxw hyz hyw hzw he).trans hd

def abLabel : ABNonvacuity.Row → TenForestRow
  | .a1 => .a1 | .a2 => .a2 | .b => .b

theorem ab_original (r : ABNonvacuity.Row) :
    TenForestOriginalHypotheses (ABNonvacuity.graph r) ABNonvacuity.weight
      (ABNonvacuity.canonicalCoeff r) 0 1 2 3 := by
  have h := ABNonvacuity.original_source_hypotheses r
  rw [ABNonvacuity.inverse_canonical] at h
  rcases h with ⟨hcard, hG, hC, hB, hD, hother, hextra, hCB, hCD, hBD,
    hseparate, hdegC, hdeg, hedges, hboundary, hA, hcoeff, hv, hbudget, hproj⟩
  have hs := scalar_data_transport (ABNonvacuity.graph r) ABNonvacuity.weight
    (ABNonvacuity.canonicalCoeff r) 0 1 2 3 (ABNonvacuity.gram r)
    ABNonvacuity.canonicalSource ABNonvacuity.marked (-1) rfl rfl rfl
    (by norm_num) (ABNonvacuity.canonical_definition r) hv hbudget hproj
  exact ⟨Or.inl rfl, hcard, hG, hC, hB, hD, hother, hextra, hCB, hCD, hBD,
    hseparate, hdegC, hdeg, hedges, hboundary, hA,
    hs.1, hcoeff, hs.2.1, hs.2.2.1, hs.2.2.2⟩

theorem ab_realized (r : ABNonvacuity.Row) :
    (abLabel r).Realized (ABNonvacuity.graph r) ABNonvacuity.weight
      (ABNonvacuity.canonicalCoeff r) 0 1 2 3 := by
  apply (ab_original r).realized_of_determinant
  apply det_transport
    (graphWeightMatrix (ABNonvacuity.graph r) (fun i => (ABNonvacuity.weight i : ℚ)))
    (ABNonvacuity.gram r) rfl (abLabel r).exceptionalDet
  cases r <;> exact ABNonvacuity.exceptional_det _

def cWeight (i : Fin 10) : ℕ := if i ∈ FamilyCNonvacuity.heavyVertices then 3 else 2

theorem c_weight_cast : (fun i => (cWeight i : ℚ)) = FamilyCNonvacuity.weight := by
  funext i
  by_cases hi : i ∈ FamilyCNonvacuity.heavyVertices <;>
    simp only [cWeight, FamilyCNonvacuity.weight, hi, if_true, if_false, Nat.cast_ofNat]

theorem c_weight_cast_apply (i : Fin 10) : (cWeight i : ℚ) = FamilyCNonvacuity.weight i :=
  congrFun c_weight_cast i

theorem c_original :
    TenForestOriginalHypotheses FamilyCNonvacuity.graph cWeight
      FamilyCNonvacuity.canonicalCoeff 0 1 3 3 := by
  have hlocal : (∀ i, i ≠ 0 → i ≠ 1 → i ≠ 3 → cWeight i = 2 ∨ cWeight i = 3) ∧
      (candidateExtraVertices cWeight 0 1 3).card ≤ 2 ∧
      ¬ FamilyCNonvacuity.graph.Adj 0 1 ∧ ¬ FamilyCNonvacuity.graph.Adj 0 3 ∧
      ¬ FamilyCNonvacuity.graph.Adj 1 3 ∧
      FamilyCNonvacuity.graph.degree 0 ≤ 1 ∧
      (∀ i, FamilyCNonvacuity.graph.degree i ≤ 3) := by decide
  have hseparate : ¬ FamilyCNonvacuity.graph.Reachable 1 3 := by
    rw [FamilyCNonvacuity.component_one]
    decide
  have hc := FamilyCNonvacuity.canonical_bounds
  have hv := FamilyCNonvacuity.positive_volume_budget
  have hp := FamilyCNonvacuity.projection_identity
  rw [FamilyCNonvacuity.inverse_canonical] at hc hv hp
  have hs := scalar_data_transport FamilyCNonvacuity.graph cWeight
    FamilyCNonvacuity.canonicalCoeff 0 1 3 3 FamilyCNonvacuity.gram
    FamilyCNonvacuity.canonicalSource FamilyCNonvacuity.marked (-1)
    (congrArg (graphWeightMatrix FamilyCNonvacuity.graph) c_weight_cast)
    (funext fun v => congrArg (fun x : ℚ => x - 2) (c_weight_cast_apply v))
    rfl (by norm_num) FamilyCNonvacuity.inverse_canonical.symm hv.1 hv.2 hp
  refine ⟨Or.inl rfl, by decide, FamilyCNonvacuity.graph_isAcyclic,
    by decide, by decide, by decide, hlocal.1, hlocal.2.1, hlocal.2.2.1,
    hlocal.2.2.2.1, hlocal.2.2.2.2.1, hseparate, hlocal.2.2.2.2.2.1,
    hlocal.2.2.2.2.2.2, ?_, ⟨2, Or.inr (Or.inl FamilyCNonvacuity.first_adj)⟩,
    ?_, hs.1, hc, hs.2.1, hs.2.2.1, hs.2.2.2⟩
  · rw [FamilyCNonvacuity.edge_card]
  · simpa only [c_weight_cast, FamilyCNonvacuity.gram] using FamilyCNonvacuity.gram_posDef

theorem c_realized : TenForestRow.c.Realized FamilyCNonvacuity.graph cWeight
    FamilyCNonvacuity.canonicalCoeff 0 1 3 3 := by
  apply c_original.realized_of_determinant
  exact det_transport (graphWeightMatrix FamilyCNonvacuity.graph (fun i => (cWeight i : ℚ)))
    FamilyCNonvacuity.gram (congrArg (graphWeightMatrix FamilyCNonvacuity.graph) c_weight_cast)
    2400 FamilyCNonvacuity.exceptional_det

def dLabel (secondEdge : Bool) : TenForestRow := if secondEdge then .d2 else .d1

theorem d_original (secondEdge : Bool) :
    TenForestOriginalHypotheses (FamilyDNonvacuity.graph secondEdge)
      FamilyDNonvacuity.weight FamilyDNonvacuity.canonicalCoeff 0 2 3 3 := by
  have hlocal :
      (∀ i, i ≠ 0 → i ≠ 2 → i ≠ 3 →
        FamilyDNonvacuity.weight i = 2 ∨ FamilyDNonvacuity.weight i = 3) ∧
      (candidateExtraVertices FamilyDNonvacuity.weight 0 2 3).card ≤ 2 ∧
      ¬ (FamilyDNonvacuity.graph secondEdge).Adj 0 2 ∧
      ¬ (FamilyDNonvacuity.graph secondEdge).Adj 0 3 ∧
      ¬ (FamilyDNonvacuity.graph secondEdge).Adj 2 3 ∧
      (FamilyDNonvacuity.graph secondEdge).degree 0 ≤ 1 ∧
      (∀ i, (FamilyDNonvacuity.graph secondEdge).degree i ≤ 3) := by
    cases secondEdge <;> decide
  have hc := FamilyDNonvacuity.canonical_bounds secondEdge
  have hv := (FamilyDNonvacuity.scalar_values secondEdge).2.1
  rw [FamilyDNonvacuity.inverse_canonical] at hc hv
  have hpositive : 0 < -1 + dotProduct FamilyDNonvacuity.canonicalSource
      FamilyDNonvacuity.canonicalCoeff := by rw [hv]; norm_num
  have hs := scalar_data_transport (FamilyDNonvacuity.graph secondEdge)
    FamilyDNonvacuity.weight FamilyDNonvacuity.canonicalCoeff 0 2 3 3
    (FamilyDNonvacuity.gram secondEdge) FamilyDNonvacuity.canonicalSource
    FamilyDNonvacuity.marked (-1) rfl rfl rfl (by norm_num)
    (FamilyDNonvacuity.inverse_canonical secondEdge).symm hpositive
    (FamilyDNonvacuity.source_budget secondEdge) (FamilyDNonvacuity.source_projection secondEdge)
  exact ⟨Or.inl rfl, by decide, FamilyDNonvacuity.graph_isAcyclic secondEdge,
    by decide, by decide, by decide, hlocal.1, hlocal.2.1, hlocal.2.2.1,
    hlocal.2.2.2.1, hlocal.2.2.2.2.1,
    (FamilyDNonvacuity.marked_components_separate secondEdge).2.2,
    hlocal.2.2.2.2.2.1, hlocal.2.2.2.2.2.2,
    FamilyDNonvacuity.edge_card_le_two secondEdge,
    ⟨1, Or.inl (FamilyDNonvacuity.canonical_adj secondEdge)⟩,
    FamilyDNonvacuity.gram_posDef secondEdge,
    hs.1, hc, hs.2.1, hs.2.2.1, hs.2.2.2⟩

theorem d_realized (secondEdge : Bool) :
    (dLabel secondEdge).Realized (FamilyDNonvacuity.graph secondEdge)
      FamilyDNonvacuity.weight FamilyDNonvacuity.canonicalCoeff 0 2 3 3 := by
  apply (d_original secondEdge).realized_of_determinant
  apply det_transport
    (graphWeightMatrix (FamilyDNonvacuity.graph secondEdge)
      (fun i => (FamilyDNonvacuity.weight i : ℚ)))
    (FamilyDNonvacuity.gram secondEdge) rfl (dLabel secondEdge).exceptionalDet
  cases secondEdge <;> exact FamilyDNonvacuity.exceptional_det _

def eLabel (row : Fin 4) : TenForestRow :=
  if row = 0 then .e1 else if row = 1 then .e2 else if row = 2 then .e3 else .e4

def eWeight (i : Fin 11) : ℕ :=
  if i = 1 ∨ i = 4 ∨ i = 5 then 3 else if i = 3 then 4 else 2

theorem e_weight_cast : (fun i => (eWeight i : ℚ)) = FamilyENonvacuity.weight := by
  funext i
  dsimp only [eWeight, FamilyENonvacuity.weight]
  split_ifs <;> norm_num

theorem e_weight_cast_apply (i : Fin 11) : (eWeight i : ℚ) = FamilyENonvacuity.weight i :=
  congrFun e_weight_cast i

theorem e_original (row : Fin 4) :
    TenForestOriginalHypotheses (FamilyENonvacuity.graph row) eWeight
      FamilyENonvacuity.canonicalCoeff 0 1 3 4 := by
  have hlocal :
      (∀ i, i ≠ 0 → i ≠ 1 → i ≠ 3 → eWeight i = 2 ∨ eWeight i = 3) ∧
      (candidateExtraVertices eWeight 0 1 3).card ≤ 2 ∧
      ¬ (FamilyENonvacuity.graph row).Adj 0 1 ∧
      ¬ (FamilyENonvacuity.graph row).Adj 0 3 ∧
      ¬ (FamilyENonvacuity.graph row).Adj 1 3 ∧
      (FamilyENonvacuity.graph row).degree 0 ≤ 1 ∧
      (∀ i, (FamilyENonvacuity.graph row).degree i ≤ 3) := by
    fin_cases row <;> decide
  have hseparate : ¬ (FamilyENonvacuity.graph row).Reachable 1 3 := by
    rw [FamilyENonvacuity.component_core]
    decide
  have hs := scalar_data_transport (FamilyENonvacuity.graph row) eWeight
    FamilyENonvacuity.canonicalCoeff 0 1 3 4 (FamilyENonvacuity.gram row)
    FamilyENonvacuity.canonicalSource FamilyENonvacuity.marked (-2)
    (congrArg (graphWeightMatrix (FamilyENonvacuity.graph row)) e_weight_cast)
    (funext fun v => congrArg (fun x : ℚ => x - 2) (e_weight_cast_apply v))
    rfl (by norm_num) (FamilyENonvacuity.inverse_canonical row).symm
    (FamilyENonvacuity.positive_volume_budget row).1
    (FamilyENonvacuity.positive_volume_budget row).2 (FamilyENonvacuity.projection_identity row)
  refine ⟨Or.inr (Or.inl rfl), by decide, FamilyENonvacuity.graph_isAcyclic row,
    by decide, by decide, by decide, hlocal.1, hlocal.2.1, hlocal.2.2.1,
    hlocal.2.2.2.1, hlocal.2.2.2.2.1, hseparate, hlocal.2.2.2.2.2.1,
    hlocal.2.2.2.2.2.2, FamilyENonvacuity.edge_card_le_three row,
    ⟨2, Or.inr (Or.inl (FamilyENonvacuity.core_adj row))⟩,
    ?_, hs.1, FamilyENonvacuity.canonical_bounds, hs.2.1, hs.2.2.1, hs.2.2.2⟩
  · simpa only [e_weight_cast, FamilyENonvacuity.gram] using FamilyENonvacuity.gram_posDef row

private def eFixed : Finset (Fin 11) := {0, 1, 2, 3, 4, 5}
private abbrev ERestVertex := {v : Fin 11 // v ∉ eFixed}

private def eRestGraph (row : Fin 4) : SimpleGraph ERestVertex :=
  (FamilyENonvacuity.graph row).induce {v | v ∉ eFixed}

private instance eRestDecidable (row : Fin 4) : DecidableRel (eRestGraph row).Adj := by
  intro v w
  change Decidable ((FamilyENonvacuity.graph row).Adj v.val w.val)
  infer_instance

private def e6 : ERestVertex := ⟨6, by decide⟩
private def e7 : ERestVertex := ⟨7, by decide⟩
private def e8 : ERestVertex := ⟨8, by decide⟩
private def e9 : ERestVertex := ⟨9, by decide⟩

private theorem e_rest_card : Fintype.card ERestVertex = 5 := by decide

private theorem e_rest_weight (v : ERestVertex) :
    FamilyENonvacuity.weight v.val = 2 := by
  have hn : v.val ≠ 0 ∧ v.val ≠ 1 ∧ v.val ≠ 2 ∧ v.val ≠ 3 ∧
      v.val ≠ 4 ∧ v.val ≠ 5 := by
    simpa only [eFixed, Finset.mem_insert, Finset.mem_singleton, not_or] using v.property
  exact FamilyENonvacuity.weight_other v.val hn.2.1 hn.2.2.2.1
    hn.2.2.2.2.1 hn.2.2.2.2.2

private theorem e_rest_edges_zero : (eRestGraph 0).edgeFinset = ∅ := by decide
private theorem e_rest_edges_one : (eRestGraph 1).edgeFinset = {s(e6, e7)} := by decide
private theorem e_rest_edges_two :
    (eRestGraph 2).edgeFinset = {s(e6, e7), s(e7, e8)} := by decide
private theorem e_rest_edges_three :
    (eRestGraph 3).edgeFinset = {s(e6, e7), s(e8, e9)} := by decide

/-- Select the four values before substituting the concrete determinant
predicate, so enumeration casts are compared only at the row index. -/
private theorem fin_four_cases (P : Fin 4 → Prop)
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (row : Fin 4) : P row := by
  fin_cases row <;> assumption

/-- Compute the actual canonical five-vertex complement in its four cases. -/
private theorem e_remainder_det (row : Fin 4) :
    (graphWeightMatrix (eRestGraph row) (fun _ => (2 : ℚ))).det =
      (eLabel row).remainingDet := by
  have hscalar3 : (9 : ℚ) * 2 ^ (Fintype.card ERestVertex - 4) =
      (eLabel 3).remainingDet := by
    rw [e_rest_card] <;>
      change (9 : ℚ) * 2 ^ (5 - 4 : ℕ) = 18 <;> norm_num
  -- Elaborate each complete application without an expected determinant type.
  have h0 := empty_det_of_scalar (V := ERestVertex) (eRestGraph 0) e_rest_edges_zero
    (eLabel 0).remainingDet (by
      rw [e_rest_card] <;> norm_num [eLabel, TenForestRow.remainingDet, Fin.ext_iff])
  have h1 := single_edge_det_of_scalar (V := ERestVertex)
    (eRestGraph 1) e6 e7 (by decide) e_rest_edges_one
    (eLabel 1).remainingDet (by
      rw [e_rest_card] <;> norm_num [eLabel, TenForestRow.remainingDet, Fin.ext_iff])
  have h2 := two_path_det_of_scalar (V := ERestVertex) (eRestGraph 2) e6 e7 e8
    (by decide) (by decide) (by decide) e_rest_edges_two
    (eLabel 2).remainingDet (by
      rw [e_rest_card] <;> norm_num [eLabel, TenForestRow.remainingDet, Fin.ext_iff])
  have h3 := disjoint_edges_det_of_scalar (V := ERestVertex) (eRestGraph 3) e6 e7 e8 e9
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    e_rest_edges_three (eLabel 3).remainingDet hscalar3
  have h := fin_four_cases
    (fun r => (graphWeightMatrix (eRestGraph r) (fun _ => (2 : ℚ))).det =
      (eLabel r).remainingDet) h0 h1 h2 h3 row
  exact h

/-- All equality transport is proved with abstract matrix index types.
Concrete aliases are compared as matrices, never below determinant. -/
private theorem e_det_from_factor
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {A B : Matrix V V ℚ} {Z Z' : Matrix W W ℚ} {d delta : ℚ}
    (hAB : A = B) (hfactor : B.det = 360 * Z.det) (hZZ' : Z = Z')
    (hd : Z'.det = d) (hdelta : 360 * d = delta) : A.det = delta := by
  refine (congrArg Matrix.det hAB).trans (hfactor.trans ?_)
  exact (congrArg (fun M : Matrix W W ℚ => 360 * M.det) hZZ').trans
    ((congrArg (fun t : ℚ => 360 * t) hd).trans hdelta)

/-- Apply the fixed-block theorem with abstract vertices and transport the
actual complement graph before specializing either determinant. -/
private theorem e_fixed_det_of_canonical_complement
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℚ)
    (C B M D T U : V) (A : Matrix V V ℚ)
    (hA : A = graphWeightMatrix G weight)
    (Z : SimpleGraph {v : V // v ∉ ({C, B, M, D, T, U} : Finset V)})
    [adjZ : DecidableRel Z.Adj]
    (hZ : Z = G.induce {v | v ∉ ({C, B, M, D, T, U} : Finset V)})
    (hweight : ∀ v : {v : V // v ∉ ({C, B, M, D, T, U} : Finset V)},
      weight v.val = 2)
    (hC : weight C = 2) (hB : weight B = 3) (hM : weight M = 2)
    (hD : weight D = 4) (hT : weight T = 3) (hU : weight U = 3)
    (hTB : T ≠ B) (hUB : U ≠ B) (hTU : T ≠ U)
    (hBM : G.Adj B M) (hnB : G.neighborFinset B = {M}) (hnM : G.neighborFinset M = {B})
    (hCiso : ∀ v, ¬ G.Adj C v) (hDiso : ∀ v, ¬ G.Adj D v)
    (hTiso : ∀ v, ¬ G.Adj T v) (hUiso : ∀ v, ¬ G.Adj U v)
    (d delta : ℚ) (hd : (graphWeightMatrix Z (fun _ => (2 : ℚ))).det = d)
    (hdelta : 360 * d = delta) : A.det = delta := by
  subst Z
  have hadj : adjZ = SimpleGraph.instDecidableComapAdj
      (fun v : {v : V // v ∉ ({C, B, M, D, T, U} : Finset V)} => v.val) G :=
    Subsingleton.elim _ _
  subst adjZ
  have hfactor := familyE_fixed_det_factor G weight C B M D T U
    hC hB hM hD hT hU hTB hUB hTU hBM hnB hnM hCiso hDiso hTiso hUiso
  have hw : (fun v : {v : V // v ∉ ({C, B, M, D, T, U} : Finset V)} =>
      weight v.val) = fun _ => (2 : ℚ) := funext hweight
  have hmatrix := congrArg
    (graphWeightMatrix (G.induce {v | v ∉ ({C, B, M, D, T, U} : Finset V)})) hw
  exact e_det_from_factor hA hfactor hmatrix hd hdelta

/-- Retain the named complement set in the concrete premise. Its equality
with the six fixed vertices is substituted while the vertex type is abstract. -/
private theorem e_fixed_det_of_named_complement
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℚ)
    (C B M D T U : V) (A : Matrix V V ℚ)
    (hA : A = graphWeightMatrix G weight)
    (fixed : Finset V) (hfixed : fixed = {C, B, M, D, T, U})
    (Z : SimpleGraph {v : V // v ∉ fixed}) [DecidableRel Z.Adj]
    (hZ : Z = G.induce {v | v ∉ fixed})
    (hweight : ∀ v : {v : V // v ∉ fixed}, weight v.val = 2)
    (hC : weight C = 2) (hB : weight B = 3) (hM : weight M = 2)
    (hD : weight D = 4) (hT : weight T = 3) (hU : weight U = 3)
    (hTB : T ≠ B) (hUB : U ≠ B) (hTU : T ≠ U)
    (hBM : G.Adj B M) (hnB : G.neighborFinset B = {M}) (hnM : G.neighborFinset M = {B})
    (hCiso : ∀ v, ¬ G.Adj C v) (hDiso : ∀ v, ¬ G.Adj D v)
    (hTiso : ∀ v, ¬ G.Adj T v) (hUiso : ∀ v, ¬ G.Adj U v)
    (d delta : ℚ) (hd : (graphWeightMatrix Z (fun _ => (2 : ℚ))).det = d)
    (hdelta : 360 * d = delta) : A.det = delta := by
  subst fixed
  have h := e_fixed_det_of_canonical_complement G weight C B M D T U A hA Z hZ hweight
    hC hB hM hD hT hU hTB hUB hTU hBM hnB hnM hCiso hDiso hTiso hUiso d delta hd hdelta
  exact h

universe uComplement

/-- Keep the named vertex type and its enumeration in the determinant premise.
Normalize them to the actual complement while the ambient type is abstract. -/
private theorem e_fixed_det_of_named_vertex_type
    {V W : Type uComplement} [Fintype V] [DecidableEq V]
    [finW : Fintype W] [decW : DecidableEq W]
    (Z : SimpleGraph W) [DecidableRel Z.Adj]
    (d : ℚ) (hd : (graphWeightMatrix Z (fun _ => (2 : ℚ))).det = d)
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℚ)
    (C B M D T U : V) (A : Matrix V V ℚ)
    (hA : A = graphWeightMatrix G weight)
    (fixed : Finset V) (hfixed : fixed = {C, B, M, D, T, U})
    (hW : W = {v : V // v ∉ fixed})
    (hZ : HEq Z (G.induce {v | v ∉ fixed}))
    (hweight : ∀ v : {v : V // v ∉ fixed}, weight v.val = 2)
    (hC : weight C = 2) (hB : weight B = 3) (hM : weight M = 2)
    (hD : weight D = 4) (hT : weight T = 3) (hU : weight U = 3)
    (hTB : T ≠ B) (hUB : U ≠ B) (hTU : T ≠ U)
    (hBM : G.Adj B M) (hnB : G.neighborFinset B = {M}) (hnM : G.neighborFinset M = {B})
    (hCiso : ∀ v, ¬ G.Adj C v) (hDiso : ∀ v, ¬ G.Adj D v)
    (hTiso : ∀ v, ¬ G.Adj T v) (hUiso : ∀ v, ¬ G.Adj U v)
    (delta : ℚ)
    (hdelta : 360 * d = delta) : A.det = delta := by
  subst W
  have hfin : finW = Subtype.fintype (fun v : V => v ∉ fixed) :=
    Subsingleton.elim _ _
  subst finW
  have hdec : decW = @Subtype.instDecidableEq V (fun v : V => v ∉ fixed) _ :=
    Subsingleton.elim _ _
  subst decW
  have hgraph : Z = G.induce {v | v ∉ fixed} := eq_of_heq hZ
  have h := e_fixed_det_of_named_complement G weight C B M D T U A hA
    fixed hfixed Z hgraph hweight hC hB hM hD hT hU hTB hUB hTU hBM hnB hnM
    hCiso hDiso hTiso hUiso d delta hd hdelta
  exact h

/-- The determinant of each actual E witness, in the manuscript's row order. -/
theorem e_exceptional_det (row : Fin 4) :
    (FamilyENonvacuity.gram row).det = (eLabel row).exceptionalDet := by
  have hscale : 360 * (eLabel row).remainingDet = (eLabel row).exceptionalDet := by
    fin_cases row <;>
      norm_num [eLabel, TenForestRow.remainingDet, TenForestRow.exceptionalDet, Fin.ext_iff]
  have hrest := e_remainder_det row
  have h := e_fixed_det_of_named_vertex_type (V := Fin 11) (W := ERestVertex)
    (eRestGraph row) (eLabel row).remainingDet hrest
    (FamilyENonvacuity.graph row) FamilyENonvacuity.weight 0 1 2 3 4 5
    (FamilyENonvacuity.gram row) rfl eFixed rfl rfl HEq.rfl e_rest_weight
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (FamilyENonvacuity.core_adj row)
    (FamilyENonvacuity.core_neighbors row).1 (FamilyENonvacuity.core_neighbors row).2
    (FamilyENonvacuity.fixed_isolated row 0 (by simp))
    (FamilyENonvacuity.fixed_isolated row 3 (by simp))
    (FamilyENonvacuity.fixed_isolated row 4 (by simp))
    (FamilyENonvacuity.fixed_isolated row 5 (by simp))
    (eLabel row).exceptionalDet hscale
  exact h


theorem e_realized (row : Fin 4) :
    (eLabel row).Realized (FamilyENonvacuity.graph row) eWeight
      FamilyENonvacuity.canonicalCoeff 0 1 3 4 := by
  apply (e_original row).realized_of_determinant
  exact det_transport
    (graphWeightMatrix (FamilyENonvacuity.graph row) (fun i => (eWeight i : ℚ)))
    (FamilyENonvacuity.gram row)
    (congrArg (graphWeightMatrix (FamilyENonvacuity.graph row)) e_weight_cast)
    (eLabel row).exceptionalDet (e_exceptional_det row)

end TenForestNonvacuity

/-- Every one of the ten labels has an actual finite weighted-forest
witness satisfying all the original hypotheses and realizing that label.
The vertex count is fixed to beta+7, and the chosen adjacency decision
procedure is shared by both conjuncts. No surface realization is claimed. -/
theorem ten_forest_all_rows_nonvacuous (row : TenForestRow) :
    ∃ (G : SimpleGraph (Fin (row.beta + 7))) (adj : DecidableRel G.Adj)
      (weight : Fin (row.beta + 7) → ℕ) (coeff : Fin (row.beta + 7) → ℚ)
      (C B D : Fin (row.beta + 7)),
      letI : DecidableRel G.Adj := adj
      TenForestOriginalHypotheses G weight coeff C B D row.beta ∧
        row.Realized G weight coeff C B D row.beta := by
  cases row
  case a1 =>
    exact ⟨ABNonvacuity.graph .a1, inferInstance, ABNonvacuity.weight,
      ABNonvacuity.canonicalCoeff .a1, 0, 1, 2,
      TenForestNonvacuity.ab_original .a1, TenForestNonvacuity.ab_realized .a1⟩
  case a2 =>
    exact ⟨ABNonvacuity.graph .a2, inferInstance, ABNonvacuity.weight,
      ABNonvacuity.canonicalCoeff .a2, 0, 1, 2,
      TenForestNonvacuity.ab_original .a2, TenForestNonvacuity.ab_realized .a2⟩
  case b =>
    exact ⟨ABNonvacuity.graph .b, inferInstance, ABNonvacuity.weight,
      ABNonvacuity.canonicalCoeff .b, 0, 1, 2,
      TenForestNonvacuity.ab_original .b, TenForestNonvacuity.ab_realized .b⟩
  case c =>
    exact ⟨FamilyCNonvacuity.graph, inferInstance, TenForestNonvacuity.cWeight,
      FamilyCNonvacuity.canonicalCoeff, 0, 1, 3,
      TenForestNonvacuity.c_original, TenForestNonvacuity.c_realized⟩
  case d1 =>
    exact ⟨FamilyDNonvacuity.graph false, inferInstance, FamilyDNonvacuity.weight,
      FamilyDNonvacuity.canonicalCoeff, 0, 2, 3,
      TenForestNonvacuity.d_original false, TenForestNonvacuity.d_realized false⟩
  case d2 =>
    exact ⟨FamilyDNonvacuity.graph true, inferInstance, FamilyDNonvacuity.weight,
      FamilyDNonvacuity.canonicalCoeff, 0, 2, 3,
      TenForestNonvacuity.d_original true, TenForestNonvacuity.d_realized true⟩
  case e1 =>
    exact ⟨FamilyENonvacuity.graph 0, inferInstance, TenForestNonvacuity.eWeight,
      FamilyENonvacuity.canonicalCoeff, 0, 1, 3,
      TenForestNonvacuity.e_original 0, TenForestNonvacuity.e_realized 0⟩
  case e2 =>
    exact ⟨FamilyENonvacuity.graph 1, inferInstance, TenForestNonvacuity.eWeight,
      FamilyENonvacuity.canonicalCoeff, 0, 1, 3,
      TenForestNonvacuity.e_original 1, TenForestNonvacuity.e_realized 1⟩
  case e3 =>
    exact ⟨FamilyENonvacuity.graph 2, inferInstance, TenForestNonvacuity.eWeight,
      FamilyENonvacuity.canonicalCoeff, 0, 1, 3,
      TenForestNonvacuity.e_original 2, TenForestNonvacuity.e_realized 2⟩
  case e4 =>
    exact ⟨FamilyENonvacuity.graph 3, inferInstance, TenForestNonvacuity.eWeight,
      FamilyENonvacuity.canonicalCoeff, 0, 1, 3,
      TenForestNonvacuity.e_original 3, TenForestNonvacuity.e_realized 3⟩

end KltDP.LinearAlgebra

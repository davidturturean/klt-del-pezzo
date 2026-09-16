import KltDP.LinearAlgebra.TenForestClassification
import Mathlib.Logic.ExistsUnique

/-!
# Unique labels for the ten actual candidate forests

The row relation below separates the existing classifier's disjunction
without dropping its actual graph witnesses. Its existential union is
equivalent to `TenForestRows`. The actual exceptional determinant then
identifies the row uniquely. Table functions are data; their connection
to a graph is supplied by the proved row relation and classifier.

Reuse: pinned and current official Mathlib `ExistsUnique` and ordinary
finite constructor elimination. No new foundation, port or axiom is used.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph

/-- The ten completions in the manuscript's displayed order. -/
inductive TenForestRow where
  | a1 | a2 | b | c | d1 | d2 | e1 | e2 | e3 | e4
  deriving DecidableEq, Fintype

namespace TenForestRow

def beta : TenForestRow → ℕ
  | .e1 | .e2 | .e3 | .e4 => 4
  | _ => 3

def length : TenForestRow → ℚ
  | .a1 | .a2 => 2 / 15
  | .b => 4 / 21
  | .c => 1 / 5
  | .d1 | .d2 => 1 / 3
  | .e1 | .e2 | .e3 | .e4 => 1 / 10

def volume : TenForestRow → ℚ
  | .a1 | .a2 | .e1 | .e2 | .e3 | .e4 => 1 / 15
  | .b => 2 / 21
  | .c => 2 / 15
  | .d1 | .d2 => 1 / 3

def green : TenForestRow → ℚ
  | .a1 | .a2 => 19 / 15
  | .b => 29 / 21
  | .c => 13 / 10
  | .d1 | .d2 => 4 / 3
  | .e1 | .e2 | .e3 | .e4 => 23 / 20

def exceptionalDet : TenForestRow → ℚ
  | .a1 => 2880 | .a2 => 2160 | .b => 2016 | .c => 2400
  | .d1 => 3888 | .d2 => 2916
  | .e1 => 11520 | .e2 => 8640 | .e3 => 5760 | .e4 => 6480

def borderedDet : TenForestRow → ℚ
  | .a1 | .b => 768 | .a2 => 576 | .c => 720
  | .d1 => 1296 | .d2 => 972
  | .e1 => -1728 | .e2 => -1296 | .e3 => -864 | .e4 => -972

/-- The numerical root determinant of the displayed remaining forest.
Its identification with an actual induced matrix is a separate theorem. -/
def remainingDet : TenForestRow → ℚ
  | .a1 => 64 | .a2 => 48 | .b => 32 | .c => 16
  | .d1 => 16 | .d2 => 12
  | .e1 => 32 | .e2 => 24 | .e3 => 16 | .e4 => 18

def deltaFactor : TenForestRow → ℚ
  | .a1 | .a2 => 12 | .b => 24 | .c => 45
  | .d1 | .d2 => 81
  | .e1 | .e2 | .e3 | .e4 => 54

theorem card_rows : Fintype.card TenForestRow = 10 := by decide

theorem exceptionalDet_injective : Function.Injective exceptionalDet := by
  intro r s h
  cases r <;> cases s <;> norm_num [exceptionalDet] at h ⊢

theorem table_identities (row : TenForestRow) :
    0 < row.volume ∧ row.volume ≤ row.length ∧
    row.volume * (row.green - 1) = row.length ^ 2 ∧
    row.borderedDet = (-1 : ℚ) ^ (row.beta + 7) *
      row.exceptionalDet * (row.green - 1) ∧
    |row.borderedDet| = row.deltaFactor * row.remainingDet := by
  cases row <;> norm_num [beta, length, volume, green, exceptionalDet,
    borderedDet, deltaFactor, remainingDet]

end TenForestRow

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One exact A1/A2/B branch, including its entire actual edge set and
canonical isolated complement. Other row labels have no such branch. -/
def TenForestABCase (row : TenForestRow) (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (coeff : V → ℚ) (C B D T : V) : Prop :=
  let A := graphWeightMatrix G (fun i => (weight i : ℚ))
  let p := threeMarkedSource C B D
  let ell := 1 - dotProduct p coeff
  let vol := -1 + dotProduct (fun i => (weight i : ℚ) - 2) coeff
  let g := dotProduct p (A⁻¹ *ᵥ p)
  match row with
  | .a1 => G.edgeFinset = {s(C, T)} ∧
      (Finset.univ \ ({C, T, B, D} : Finset V)).card = 6 ∧
      (∀ v ∈ Finset.univ \ ({C, T, B, D} : Finset V),
        weight v = 2 ∧ ∀ u, ¬ G.Adj v u) ∧
      ell = 2 / 15 ∧ vol = 1 / 15 ∧ g = 19 / 15 ∧
      A.det = 2880 ∧ (borderedGram A p (-1)).det = 768
  | .a2 => ∃ u v, u ≠ v ∧ u ∉ ({C, T, B, D} : Finset V) ∧
      v ∉ ({C, T, B, D} : Finset V) ∧ weight u = 2 ∧ weight v = 2 ∧
      G.edgeFinset = {s(C, T), s(u, v)} ∧
      (Finset.univ \ ({u, v, C, T, B, D} : Finset V)).card = 4 ∧
      (∀ w ∈ Finset.univ \ ({u, v, C, T, B, D} : Finset V),
        weight w = 2 ∧ ∀ z, ¬ G.Adj w z) ∧
      ell = 2 / 15 ∧ vol = 1 / 15 ∧ g = 19 / 15 ∧
      A.det = 2160 ∧ (borderedGram A p (-1)).det = 576
  | .b => ∃ M, weight M = 2 ∧ G.Adj C M ∧ G.Adj M T ∧
      G.edgeFinset = {s(C, M), s(M, T)} ∧
      (Finset.univ \ ({C, M, T, B, D} : Finset V)).card = 5 ∧
      (∀ v ∈ Finset.univ \ ({C, M, T, B, D} : Finset V),
        weight v = 2 ∧ ∀ u, ¬ G.Adj v u) ∧
      ell = 4 / 21 ∧ vol = 2 / 21 ∧ g = 29 / 21 ∧
      A.det = 2016 ∧ (borderedGram A p (-1)).det = 768
  | _ => False

/-- One exact D remainder on the original ambient graph. -/
def TenForestDCase (row : TenForestRow) (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (C M B D T U : V) : Prop :=
  let A := graphWeightMatrix G (fun i => (weight i : ℚ))
  let p := threeMarkedSource C B D
  match row with
  | .d1 => G.edgeFinset = {s(C, M)} ∧
      (Finset.univ \ ({C, M, B, D, T, U} : Finset V)).card = 4 ∧
      (∀ i ∈ Finset.univ \ ({C, M, B, D, T, U} : Finset V),
        weight i = 2 ∧ ∀ j, ¬ G.Adj i j) ∧
      A.det = 3888 ∧ (borderedGram A p (-1)).det = 1296
  | .d2 => ∃ x y, G.Adj x y ∧ x ∉ ({C, M, B, D, T, U} : Finset V) ∧
      y ∉ ({C, M, B, D, T, U} : Finset V) ∧ weight x = 2 ∧ weight y = 2 ∧
      G.edgeFinset = {s(C, M), s(x, y)} ∧
      (Finset.univ \ ({x, y, C, M, B, D, T, U} : Finset V)).card = 2 ∧
      (∀ i ∈ Finset.univ \ ({x, y, C, M, B, D, T, U} : Finset V),
        weight i = 2 ∧ ∀ j, ¬ G.Adj i j) ∧
      A.det = 2916 ∧ (borderedGram A p (-1)).det = 972
  | _ => False

/-- One exact E remainder with the same ambient determinant arguments
as `FiveVertexForestShapeDet`. Its graph is the actual induced complement. -/
def TenForestECase (row : TenForestRow) (G : SimpleGraph V) [DecidableRel G.Adj]
    (exceptional bordered : ℚ) : Prop :=
  match row with
  | .e1 => G.edgeFinset = ∅ ∧ exceptional = 11520 ∧ bordered = -1728
  | .e2 => ∃ x y, x ≠ y ∧ G.edgeFinset = {s(x, y)} ∧
      (Finset.univ \ ({x, y} : Finset V)).card = 3 ∧
      (∀ v ∉ ({x, y} : Finset V), ∀ w, ¬ G.Adj v w) ∧
      exceptional = 8640 ∧ bordered = -1296
  | .e3 => ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      G.edgeFinset = {s(x, y), s(y, z)} ∧
      (Finset.univ \ ({x, y, z} : Finset V)).card = 2 ∧
      (∀ v ∉ ({x, y, z} : Finset V), ∀ w, ¬ G.Adj v w) ∧
      exceptional = 5760 ∧ bordered = -864
  | .e4 => ∃ x y z w, x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w ∧
      G.edgeFinset = {s(x, y), s(z, w)} ∧
      (Finset.univ \ ({x, y, z, w} : Finset V)).card = 1 ∧
      (∀ v ∉ ({x, y, z, w} : Finset V), ∀ u, ¬ G.Adj v u) ∧
      exceptional = 6480 ∧ bordered = -972
  | _ => False

/-- An exact selected classifier output. Every label retains its actual
graph witnesses, weights, complementary vertices and scalar identities.
This is a conclusion relation, never an additional source premise. -/
def TenForestRow.Realized (row : TenForestRow) (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (coeff : V → ℚ) (C B D : V) (β : ℕ) : Prop :=
  β = row.beta ∧
  match row with
  | .a1 | .a2 | .b => ∃ T, T ≠ B ∧ T ≠ D ∧ weight T = 3 ∧
      (∀ u, ¬ G.Adj B u) ∧ (∀ u, ¬ G.Adj D u) ∧
      TenForestABCase row G weight coeff C B D T
  | .c => ∃ T, T ≠ B ∧ T ≠ D ∧ weight T = 3 ∧
      CForestRow G (fun v => (weight v : ℚ)) coeff C B D T
  | .d1 | .d2 => ∃ T U, T ≠ B ∧ T ≠ D ∧ U ≠ B ∧ U ≠ D ∧ T ≠ U ∧
      weight T = 3 ∧ weight U = 3 ∧ ∃ M,
      G.Adj C M ∧ weight C = 2 ∧ weight M = 2 ∧
      G.neighborFinset C = {M} ∧ G.neighborFinset M = {C} ∧
      (∀ i, G.Reachable C i ↔ i = C ∨ i = M) ∧
      (∀ i, ¬ G.Adj B i) ∧ (∀ i, ¬ G.Adj D i) ∧
      (∀ i, ¬ G.Adj T i) ∧ (∀ i, ¬ G.Adj U i) ∧
      1 - dotProduct (threeMarkedSource C B D) coeff = 1 / 3 ∧
      -1 + dotProduct (fun i => (weight i : ℚ) - 2) coeff = 1 / 3 ∧
      dotProduct (threeMarkedSource C B D)
        ((graphWeightMatrix G (fun i => (weight i : ℚ)))⁻¹ *ᵥ
          threeMarkedSource C B D) = 4 / 3 ∧
      TenForestDCase row G weight C M B D T U
  | .e1 | .e2 | .e3 | .e4 => ∃ T U, T ≠ B ∧ T ≠ D ∧ U ≠ B ∧ U ≠ D ∧ T ≠ U ∧
      weight T = 3 ∧ weight U = 3 ∧ ∃ M,
      (weight M : ℚ) = 2 ∧ G.Adj B M ∧ G.neighborFinset B = {M} ∧
      G.neighborFinset M = {B} ∧
      (∀ v, G.Reachable B v ↔ v = B ∨ v = M) ∧
      (∀ v, ¬ G.Adj C v) ∧ (∀ v, ¬ G.Adj D v) ∧
      (∀ v, ¬ G.Adj T v) ∧ (∀ v, ¬ G.Adj U v) ∧
      1 - dotProduct (threeMarkedSource C B D) coeff = 1 / 10 ∧
      -2 + dotProduct (fun i => (weight i : ℚ) - 2) coeff = 1 / 15 ∧
      dotProduct (threeMarkedSource C B D)
        ((graphWeightMatrix G (fun i => (weight i : ℚ)))⁻¹ *ᵥ
          threeMarkedSource C B D) = 23 / 20 ∧
      (let fixed : Finset V := {C, B, M, D, T, U}
       let Z := G.induce {v | v ∉ fixed}
       fixed.card = 6 ∧ Fintype.card {v | v ∉ fixed} = 5 ∧
         (∀ v : {v | v ∉ fixed}, (weight v.val : ℚ) = 2) ∧
         Z.edgeFinset.card = G.edgeFinset.card - 1 ∧ TenForestECase row Z
           (graphWeightMatrix G (fun i => (weight i : ℚ))).det
           (borderedGram (graphWeightMatrix G (fun i => (weight i : ℚ)))
             (threeMarkedSource C B D) (-1)).det)

/-- Splitting the existing output selects a label while preserving each
whole actual branch, including the induced graph used in family E. -/
theorem TenForestRows.exists_realized
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ) (coeff : V → ℚ)
    (C B D : V) (β : ℕ) (h : TenForestRows G weight coeff C B D β) :
    ∃ row : TenForestRow, row.Realized G weight coeff C B D β := by
  rcases h with ⟨hβ, T, hTB, hTD, hT, h⟩ | ⟨hβ, T, hTB, hTD, hT, h⟩ |
    ⟨hβ, T, U, hTB, hTD, hUB, hUD, hTU, hT, hU, h⟩ |
    ⟨hβ, T, U, hTB, hTD, hUB, hUD, hTU, hT, hU, h⟩
  · rcases h with ⟨hBiso, hDiso, h | h | h⟩
    · exact ⟨.a1, hβ, T, hTB, hTD, hT, hBiso, hDiso, h⟩
    · exact ⟨.a2, hβ, T, hTB, hTD, hT, hBiso, hDiso, h⟩
    · exact ⟨.b, hβ, T, hTB, hTD, hT, hBiso, hDiso, h⟩
  · exact ⟨.c, hβ, T, hTB, hTD, hT, h⟩
  · rcases h with ⟨M, hCM, hC, hM, hnC, hnM, hr, hBiso, hDiso, hTiso, hUiso,
      hl, hv, hg, h | h⟩
    · exact ⟨.d1, hβ, T, U, hTB, hTD, hUB, hUD, hTU, hT, hU,
        M, hCM, hC, hM, hnC, hnM, hr, hBiso, hDiso, hTiso, hUiso, hl, hv, hg, h⟩
    · exact ⟨.d2, hβ, T, U, hTB, hTD, hUB, hUD, hTU, hT, hU,
        M, hCM, hC, hM, hnC, hnM, hr, hBiso, hDiso, hTiso, hUiso, hl, hv, hg, h⟩
  · rcases h with ⟨M, hM, hBM, hnB, hnM, hr, hCiso, hDiso, hTiso, hUiso,
      hl, hv, hg, hremaining⟩
    rcases hremaining with ⟨hfixed, hcard, hcanonical, hedges, h⟩
    rcases h with h | h | h | h
    · exact ⟨.e1, hβ, T, U, hTB, hTD, hUB, hUD, hTU, hT, hU,
        M, hM, hBM, hnB, hnM, hr, hCiso, hDiso, hTiso, hUiso, hl, hv, hg,
        hfixed, hcard, hcanonical, hedges, h⟩
    · exact ⟨.e2, hβ, T, U, hTB, hTD, hUB, hUD, hTU, hT, hU,
        M, hM, hBM, hnB, hnM, hr, hCiso, hDiso, hTiso, hUiso, hl, hv, hg,
        hfixed, hcard, hcanonical, hedges, h⟩
    · exact ⟨.e3, hβ, T, U, hTB, hTD, hUB, hUD, hTU, hT, hU,
        M, hM, hBM, hnB, hnM, hr, hCiso, hDiso, hTiso, hUiso, hl, hv, hg,
        hfixed, hcard, hcanonical, hedges, h⟩
    · exact ⟨.e4, hβ, T, U, hTB, hTD, hUB, hUD, hTU, hT, hU,
        M, hM, hBM, hnB, hnM, hr, hCiso, hDiso, hTiso, hUiso, hl, hv, hg,
        hfixed, hcard, hcanonical, hedges, h⟩

/-- Forgetting the label recovers exactly the original classifier output. -/
theorem TenForestRow.Realized.to_rows
    {row : TenForestRow} {G : SimpleGraph V} [DecidableRel G.Adj]
    {weight : V → ℕ} {coeff : V → ℚ} {C B D : V} {β : ℕ}
    (h : row.Realized G weight coeff C B D β) : TenForestRows G weight coeff C B D β := by
  cases row
  case a1 =>
    rcases h with ⟨hβ, T, hTB, hTD, hT, hBiso, hDiso, hcase⟩
    exact Or.inl ⟨hβ, T, hTB, hTD, hT, hBiso, hDiso, Or.inl hcase⟩
  case a2 =>
    rcases h with ⟨hβ, T, hTB, hTD, hT, hBiso, hDiso, hcase⟩
    exact Or.inl ⟨hβ, T, hTB, hTD, hT, hBiso, hDiso, Or.inr (Or.inl hcase)⟩
  case b =>
    rcases h with ⟨hβ, T, hTB, hTD, hT, hBiso, hDiso, hcase⟩
    exact Or.inl ⟨hβ, T, hTB, hTD, hT, hBiso, hDiso, Or.inr (Or.inr hcase)⟩
  case c =>
    exact Or.inr (Or.inl h)
  case d1 =>
    rcases h with ⟨hβ, T, U, hTB, hTD, hUB, hUD, hTU, hT, hU,
      M, hCM, hC, hM, hnC, hnM, hr, hBiso, hDiso, hTiso, hUiso, hl, hv, hg, hcase⟩
    exact Or.inr (Or.inr (Or.inl ⟨hβ, T, U, hTB, hTD, hUB, hUD, hTU, hT, hU,
      M, hCM, hC, hM, hnC, hnM, hr, hBiso, hDiso, hTiso, hUiso, hl, hv, hg,
      Or.inl hcase⟩))
  case d2 =>
    rcases h with ⟨hβ, T, U, hTB, hTD, hUB, hUD, hTU, hT, hU,
      M, hCM, hC, hM, hnC, hnM, hr, hBiso, hDiso, hTiso, hUiso, hl, hv, hg, hcase⟩
    exact Or.inr (Or.inr (Or.inl ⟨hβ, T, U, hTB, hTD, hUB, hUD, hTU, hT, hU,
      M, hCM, hC, hM, hnC, hnM, hr, hBiso, hDiso, hTiso, hUiso, hl, hv, hg,
      Or.inr hcase⟩))
  case e1 =>
    rcases h with ⟨hβ, T, U, hTB, hTD, hUB, hUD, hTU, hT, hU,
      M, hM, hBM, hnB, hnM, hr, hCiso, hDiso, hTiso, hUiso, hl, hv, hg,
      hfixed, hcard, hcanonical, hedges, hcase⟩
    exact Or.inr (Or.inr (Or.inr ⟨hβ, T, U, hTB, hTD, hUB, hUD, hTU, hT, hU,
      M, hM, hBM, hnB, hnM, hr, hCiso, hDiso, hTiso, hUiso, hl, hv, hg,
      hfixed, hcard, hcanonical, hedges, Or.inl hcase⟩))
  case e2 =>
    rcases h with ⟨hβ, T, U, hTB, hTD, hUB, hUD, hTU, hT, hU,
      M, hM, hBM, hnB, hnM, hr, hCiso, hDiso, hTiso, hUiso, hl, hv, hg,
      hfixed, hcard, hcanonical, hedges, hcase⟩
    exact Or.inr (Or.inr (Or.inr ⟨hβ, T, U, hTB, hTD, hUB, hUD, hTU, hT, hU,
      M, hM, hBM, hnB, hnM, hr, hCiso, hDiso, hTiso, hUiso, hl, hv, hg,
      hfixed, hcard, hcanonical, hedges, Or.inr (Or.inl hcase)⟩))
  case e3 =>
    rcases h with ⟨hβ, T, U, hTB, hTD, hUB, hUD, hTU, hT, hU,
      M, hM, hBM, hnB, hnM, hr, hCiso, hDiso, hTiso, hUiso, hl, hv, hg,
      hfixed, hcard, hcanonical, hedges, hcase⟩
    exact Or.inr (Or.inr (Or.inr ⟨hβ, T, U, hTB, hTD, hUB, hUD, hTU, hT, hU,
      M, hM, hBM, hnB, hnM, hr, hCiso, hDiso, hTiso, hUiso, hl, hv, hg,
      hfixed, hcard, hcanonical, hedges, Or.inr (Or.inr (Or.inl hcase))⟩))
  case e4 =>
    rcases h with ⟨hβ, T, U, hTB, hTD, hUB, hUD, hTU, hT, hU,
      M, hM, hBM, hnB, hnM, hr, hCiso, hDiso, hTiso, hUiso, hl, hv, hg,
      hfixed, hcard, hcanonical, hedges, hcase⟩
    exact Or.inr (Or.inr (Or.inr ⟨hβ, T, U, hTB, hTD, hUB, hUD, hTU, hT, hU,
      M, hM, hBM, hnB, hnM, hr, hCiso, hDiso, hTiso, hUiso, hl, hv, hg,
      hfixed, hcard, hcanonical, hedges, Or.inr (Or.inr (Or.inr hcase))⟩))

theorem tenForestRows_iff_exists_realized
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ) (coeff : V → ℚ)
    (C B D : V) (β : ℕ) :
    TenForestRows G weight coeff C B D β ↔ ∃ row : TenForestRow, row.Realized G weight coeff C B D β :=
  ⟨TenForestRows.exists_realized G weight coeff C B D β,
    fun ⟨_, h⟩ => h.to_rows⟩

theorem TenForestABCase.values {row : TenForestRow} {G : SimpleGraph V}
    [DecidableRel G.Adj] {weight : V → ℕ} {coeff : V → ℚ} {C B D T : V}
    (h : TenForestABCase row G weight coeff C B D T) :
    1 - dotProduct (threeMarkedSource C B D) coeff = row.length ∧
    -1 + dotProduct (fun i => (weight i : ℚ) - 2) coeff = row.volume ∧
    dotProduct (threeMarkedSource C B D)
      ((graphWeightMatrix G (fun i => (weight i : ℚ)))⁻¹ *ᵥ
        threeMarkedSource C B D) = row.green ∧
    (graphWeightMatrix G (fun i => (weight i : ℚ))).det = row.exceptionalDet ∧
    (borderedGram (graphWeightMatrix G (fun i => (weight i : ℚ)))
      (threeMarkedSource C B D) (-1)).det = row.borderedDet := by
  cases row
  case a1 =>
    rcases h with ⟨_, _, _, hl, hv, hg, hd, hb⟩
    exact ⟨hl, hv, hg, hd, hb⟩
  case a2 =>
    rcases h with ⟨u, v, _, _, _, _, _, _, _, _, hl, hv, hg, hd, hb⟩
    exact ⟨hl, hv, hg, hd, hb⟩
  case b =>
    rcases h with ⟨M, _, _, _, _, _, _, hl, hv, hg, hd, hb⟩
    exact ⟨hl, hv, hg, hd, hb⟩
  all_goals exact h.elim

theorem TenForestDCase.determinants {row : TenForestRow} {G : SimpleGraph V}
    [DecidableRel G.Adj] {weight : V → ℕ} {C M B D T U : V}
    (h : TenForestDCase row G weight C M B D T U) :
    (graphWeightMatrix G (fun i => (weight i : ℚ))).det = row.exceptionalDet ∧
    (borderedGram (graphWeightMatrix G (fun i => (weight i : ℚ)))
      (threeMarkedSource C B D) (-1)).det = row.borderedDet := by
  cases row
  case d1 =>
    rcases h with ⟨_, _, _, hd, hb⟩
    exact ⟨hd, hb⟩
  case d2 =>
    rcases h with ⟨x, y, _, _, _, _, _, _, _, _, hd, hb⟩
    exact ⟨hd, hb⟩
  all_goals exact h.elim

theorem TenForestECase.determinants {row : TenForestRow} {G : SimpleGraph V}
    [DecidableRel G.Adj] {exceptional bordered : ℚ}
    (h : TenForestECase row G exceptional bordered) :
    exceptional = row.exceptionalDet ∧ bordered = row.borderedDet := by
  cases row
  case e1 =>
    rcases h with ⟨_, hd, hb⟩
    exact ⟨hd, hb⟩
  case e2 =>
    rcases h with ⟨x, y, _, _, _, _, hd, hb⟩
    exact ⟨hd, hb⟩
  case e3 =>
    rcases h with ⟨x, y, z, _, _, _, _, _, _, hd, hb⟩
    exact ⟨hd, hb⟩
  case e4 =>
    rcases h with ⟨x, y, z, w, _, _, _, _, _, _, _, _, _, hd, hb⟩
    exact ⟨hd, hb⟩
  all_goals exact h.elim

/-- Every table value belongs to this exact graph and these exact source
coefficients. The signed bordered determinant is retained for E1--E4. -/
theorem TenForestRow.Realized.values
    {row : TenForestRow} {G : SimpleGraph V} [DecidableRel G.Adj]
    {weight : V → ℕ} {coeff : V → ℚ} {C B D : V} {β : ℕ}
    (h : row.Realized G weight coeff C B D β) :
    β = row.beta ∧
    1 - dotProduct (threeMarkedSource C B D) coeff = row.length ∧
    2 - (β : ℚ) + dotProduct (fun i => (weight i : ℚ) - 2) coeff = row.volume ∧
    dotProduct (threeMarkedSource C B D)
      ((graphWeightMatrix G (fun i => (weight i : ℚ)))⁻¹ *ᵥ
        threeMarkedSource C B D) = row.green ∧
    (graphWeightMatrix G (fun i => (weight i : ℚ))).det = row.exceptionalDet ∧
    (borderedGram (graphWeightMatrix G (fun i => (weight i : ℚ)))
      (threeMarkedSource C B D) (-1)).det = row.borderedDet := by
  rcases h with ⟨hβ, h⟩
  refine ⟨hβ, ?_⟩
  rw [hβ]
  have hthree : (2 : ℚ) - 3 = -1 := by norm_num
  have hfour : (2 : ℚ) - 4 = -2 := by norm_num
  cases row
  case a1 =>
    rcases h with ⟨T, _, _, _, _, _, hcase⟩
    simpa only [TenForestRow.beta, Nat.cast_ofNat, hthree] using hcase.values
  case a2 =>
    rcases h with ⟨T, _, _, _, _, _, hcase⟩
    simpa only [TenForestRow.beta, Nat.cast_ofNat, hthree] using hcase.values
  case b =>
    rcases h with ⟨T, _, _, _, _, _, hcase⟩
    simpa only [TenForestRow.beta, Nat.cast_ofNat, hthree] using hcase.values
  case c =>
    rcases h with ⟨T, _, _, _, L, M, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hl, hv, hg, hd, hb⟩
    simpa only [TenForestRow.beta, Nat.cast_ofNat, hthree] using
      (show 1 - dotProduct (threeMarkedSource C B D) coeff = (1 : ℚ) / 5 ∧
        -1 + dotProduct (fun i => (weight i : ℚ) - 2) coeff = (2 : ℚ) / 15 ∧
        dotProduct (threeMarkedSource C B D)
          ((graphWeightMatrix G (fun i => (weight i : ℚ)))⁻¹ *ᵥ
            threeMarkedSource C B D) = (13 : ℚ) / 10 ∧
        (graphWeightMatrix G (fun i => (weight i : ℚ))).det = 2400 ∧
        (borderedGram (graphWeightMatrix G (fun i => (weight i : ℚ)))
          (threeMarkedSource C B D) (-1)).det = 720 from ⟨hl, hv, hg, hd, hb⟩)
  case d1 =>
    rcases h with ⟨T, U, _, _, _, _, _, _, _, M, _, _, _, _, _, _, _, _, _, _,
      hl, hv, hg, hcase⟩
    simpa only [TenForestRow.beta, Nat.cast_ofNat, hthree] using
      (And.intro hl (And.intro hv (And.intro hg hcase.determinants)))
  case d2 =>
    rcases h with ⟨T, U, _, _, _, _, _, _, _, M, _, _, _, _, _, _, _, _, _, _,
      hl, hv, hg, hcase⟩
    simpa only [TenForestRow.beta, Nat.cast_ofNat, hthree] using
      (And.intro hl (And.intro hv (And.intro hg hcase.determinants)))
  case e1 =>
    rcases h with ⟨T, U, _, _, _, _, _, _, _, M, _, _, _, _, _, _, _, _, _,
      hl, hv, hg, _, _, _, _, hcase⟩
    simpa only [TenForestRow.beta, Nat.cast_ofNat, hfour] using
      (And.intro hl (And.intro hv (And.intro hg hcase.determinants)))
  case e2 =>
    rcases h with ⟨T, U, _, _, _, _, _, _, _, M, _, _, _, _, _, _, _, _, _,
      hl, hv, hg, _, _, _, _, hcase⟩
    simpa only [TenForestRow.beta, Nat.cast_ofNat, hfour] using
      (And.intro hl (And.intro hv (And.intro hg hcase.determinants)))
  case e3 =>
    rcases h with ⟨T, U, _, _, _, _, _, _, _, M, _, _, _, _, _, _, _, _, _,
      hl, hv, hg, _, _, _, _, hcase⟩
    simpa only [TenForestRow.beta, Nat.cast_ofNat, hfour] using
      (And.intro hl (And.intro hv (And.intro hg hcase.determinants)))
  case e4 =>
    rcases h with ⟨T, U, _, _, _, _, _, _, _, M, _, _, _, _, _, _, _, _, _,
      hl, hv, hg, _, _, _, _, hcase⟩
    simpa only [TenForestRow.beta, Nat.cast_ofNat, hfour] using
      (And.intro hl (And.intro hv (And.intro hg hcase.determinants)))

theorem TenForestRow.Realized.unique
    {r s : TenForestRow} {G : SimpleGraph V} [DecidableRel G.Adj]
    {weight : V → ℕ} {coeff : V → ℚ} {C B D : V} {β : ℕ}
    (hr : r.Realized G weight coeff C B D β)
    (hs : s.Realized G weight coeff C B D β) : r = s := by
  have hdr := hr.values.2.2.2.2.1
  have hds := hs.values.2.2.2.2.1
  exact TenForestRow.exceptionalDet_injective (hdr.symm.trans hds)

/-- Exactly one of the ten labels realizes the actual classifier output.
The graph witnesses are part of the uniquely labelled conclusion. -/
theorem TenForestRows.existsUnique_realized
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ) (coeff : V → ℚ)
    (C B D : V) (β : ℕ) (h : TenForestRows G weight coeff C B D β) :
    ∃! row : TenForestRow, row.Realized G weight coeff C B D β := by
  apply existsUnique_of_exists_of_unique
    (TenForestRows.exists_realized G weight coeff C B D β h)
  intro r s hr hs
  exact hr.unique hs

/-- The original manuscript hypotheses give a unique actual row label.
No component separation or candidate row is added to those hypotheses. -/
theorem ten_forest_classification_unique
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ) (coeff : V → ℚ)
    (C B D : V) (β : ℕ)
    (hβ : β = 3 ∨ β = 4 ∨ β = 5) (hcard : Fintype.card V = β + 7)
    (hG : G.IsAcyclic)
    (hC : weight C = 2) (hB : weight B = 3) (hD : weight D = β)
    (hother : ∀ v, v ≠ C → v ≠ B → v ≠ D → weight v = 2 ∨ weight v = 3)
    (hextraCard : (candidateExtraVertices weight C B D).card ≤ 2)
    (hnadjCB : ¬ G.Adj C B) (hnadjCD : ¬ G.Adj C D) (hnadjBD : ¬ G.Adj B D)
    (hseparate : ¬ G.Reachable B D)
    (hdegreeC : G.degree C ≤ 1) (hdegree : ∀ v, G.degree v ≤ 3)
    (hedges : G.edgeFinset.card ≤ β - 1)
    (hboundary : ∃ v, G.Adj C v ∨ G.Adj B v ∨ G.Adj D v)
    (hA : (graphWeightMatrix G (fun v => (weight v : ℚ))).PosDef)
    (hsolve : coeff = (graphWeightMatrix G (fun v => (weight v : ℚ)))⁻¹ *ᵥ
      (fun v => (weight v : ℚ) - 2))
    (hcoeffBounds : ∀ v, 0 ≤ coeff v ∧ coeff v < 1)
    (hvolume : 0 < 2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff)
    (hbudget : 2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff ≤
      1 - dotProduct (threeMarkedSource C B D) coeff)
    (hprojection :
      (2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff) *
        (dotProduct (threeMarkedSource C B D)
          ((graphWeightMatrix G (fun v => (weight v : ℚ)))⁻¹ *ᵥ
            threeMarkedSource C B D) - 1) =
        (1 - dotProduct (threeMarkedSource C B D) coeff)^2) :
    ∃! row : TenForestRow, row.Realized G weight coeff C B D β := by
  apply TenForestRows.existsUnique_realized G weight coeff C B D β
  exact ten_forest_classification G weight coeff C B D β hβ hcard hG hC hB hD hother
    hextraCard hnadjCB hnadjCD hnadjBD hseparate hdegreeC hdegree hedges hboundary hA
    hsolve hcoeffBounds hvolume hbudget hprojection

end KltDP.LinearAlgebra

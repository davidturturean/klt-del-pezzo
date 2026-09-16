import KltDP.Support.SmallTableEightTotalRows

/-!
# Isolated vertices and singleton connected components

For any simple graph, its isolated vertices are in bijection with all
connected components having singleton support. Nonemptiness of every
component's support is part of Mathlib's actual connected-component API.
The eight-vertex table therefore counts isolated `A1` components literally.
-/

namespace KltDP.Support.SmallTableEightTotal

open SimpleGraph
open KltDP.Lattices.SmallADEPartitions KltDP.Lattices.SmallADEMatrices
open KltDP.Lattices.SmallADEGraphs

section AnyGraph

variable {V : Type*} (G : SimpleGraph V)

/-- An isolated vertex can be reached only from itself. -/
theorem reachable_from_isolated_iff (v w : V) (hv : v ∉ G.support) :
    G.Reachable v w ↔ w = v := by
  constructor
  · rintro ⟨p⟩
    cases p with
    | nil => rfl
    | cons h p => exact (hv ⟨_, h⟩).elim
  · rintro rfl
    exact .refl _

/-- The connected component containing an isolated vertex has at most one
vertex; its support is nonempty by construction. -/
theorem component_supp_subsingleton_of_isolated (v : V) (hv : v ∉ G.support) :
    (G.connectedComponentMk v).supp.Subsingleton := by
  intro x hx y hy
  have hx' : x = v :=
    (reachable_from_isolated_iff G v x hv).mp (ConnectedComponent.exact hx.symm)
  have hy' : y = v :=
    (reachable_from_isolated_iff G v y hv).mp (ConnectedComponent.exact hy.symm)
  exact hx'.trans hy'.symm

/-- An actual vertex in a singleton component is isolated in the whole graph. -/
theorem isolated_of_component_supp_subsingleton (c : G.ConnectedComponent)
    (hc : c.supp.Subsingleton) (v : V) (hv : v ∈ c.supp) : v ∉ G.support := by
  rintro ⟨w, hadj⟩
  have hw : w ∈ c.supp := (c.mem_supp_congr_adj hadj).mp hv
  exact G.ne_of_adj hadj (hc hv hw)

/-- An isolated vertex determines its actual singleton connected component. -/
def singletonComponentMap (v : {v : V // v ∉ G.support}) :
    {c : G.ConnectedComponent // c.supp.Subsingleton} :=
  ⟨G.connectedComponentMk v.val, component_supp_subsingleton_of_isolated G v.val v.property⟩

/-- Every singleton component contains exactly one isolated vertex, so this
map exhausts all such components and never identifies distinct vertices. -/
theorem singletonComponentMap_bijective : Function.Bijective (singletonComponentMap G) := by
  constructor
  · intro v w h
    have hcomp : G.connectedComponentMk v.val = G.connectedComponentMk w.val :=
      congrArg Subtype.val h
    apply Subtype.ext
    exact ((reachable_from_isolated_iff G v.val w.val v.property).mp
      (ConnectedComponent.exact hcomp)).symm
  · rintro ⟨c, hc⟩
    obtain ⟨v, hv⟩ := c.nonempty_supp
    refine ⟨⟨v, isolated_of_component_supp_subsingleton G c hc v hv⟩, ?_⟩
    exact Subtype.ext hv

/-- Total singleton-component and total isolated-vertex counts agree for
any graph, without a supplied finite enumeration or a chosen subset. -/
theorem total_singleton_components_eq_total_isolated :
    Nat.card {c : G.ConnectedComponent // c.supp.Subsingleton} =
      Nat.card {v : V // v ∉ G.support} :=
  (Nat.card_eq_of_bijective (singletonComponentMap G)
    (singletonComponentMap_bijective G)).symm

end AnyGraph

section ADEGraph

variable {V : Type*} [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The `A1` multiplicity equals the number of all actual singleton
components of any graph with the specified full ADE matrix identification. -/
theorem total_singleton_components_eq_a1 (counts : Counts) (e : V ≃ Vertex counts)
    (hGram : (cartanMatrix counts).submatrix e e = graphCartanMatrix G) :
    Nat.card {c : G.ConnectedComponent // c.supp.Subsingleton} = counts.a1 :=
  (total_singleton_components_eq_total_isolated G).trans
    (total_isolated_card_eq_a1 G counts e hGram)

variable [Fintype V] [Fintype G.ConnectedComponent]
variable [∀ c : G.ConnectedComponent, Fintype c.supp]

/-- The three surviving pairs use the total isolated `A1` component count
of the original forest, as in the manuscript table. -/
theorem eight_vertex_square_total_component_pairs
    (hG : G.IsAcyclic) (hvertices : Fintype.card V = 8)
    (hcomponents : 5 ≤ Fintype.card G.ConnectedComponent)
    (I : ℕ) (hsquare : (graphCartanMatrix G).det.natAbs = I ^ 2) :
    (I = 8 ∧ Nat.card {c : G.ConnectedComponent // c.supp.Subsingleton} = 4) ∨
    (I = 12 ∧ Nat.card {c : G.ConnectedComponent // c.supp.Subsingleton} = 4) ∨
    (I = 16 ∧ Nat.card {c : G.ConnectedComponent // c.supp.Subsingleton} = 8) := by
  rw [total_singleton_components_eq_total_isolated G]
  exact eight_vertex_square_total_node_pairs G hG hvertices hcomponents I hsquare

/-- The actual total isolated `A1` component count exceeds the two-adic
valuation in every square row. -/
theorem eight_vertex_square_factorization_lt_total_components
    (hG : G.IsAcyclic) (hvertices : Fintype.card V = 8)
    (hcomponents : 5 ≤ Fintype.card G.ConnectedComponent)
    (I : ℕ) (hsquare : (graphCartanMatrix G).det.natAbs = I ^ 2) :
    I.factorization 2 < Nat.card {c : G.ConnectedComponent // c.supp.Subsingleton} := by
  rw [total_singleton_components_eq_total_isolated G]
  exact eight_vertex_square_factorization_lt_total G hG hvertices hcomponents I hsquare

end ADEGraph

end KltDP.Support.SmallTableEightTotal

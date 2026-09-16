import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Small connected components of a finite forest

The component count in this module is the cardinality of the graph's actual
`ConnectedComponent` quotient. The component vertex set is its actual support.
No enumeration or partition of components is supplied as an assumption.

For any surjection between finite types, one fiber together with one vertex
for every other fiber cannot exceed the size of the domain. Consequently, a
graph with at most eight vertices and at least five components has at most
four vertices in each component. This bound does not require acyclicity.
If the graph is acyclic, the graph induced on each component support is a tree.

Reuse: the pinned Mathlib supplies `Fintype.card_le_of_surjective`,
`Fintype.card_subtype_compl`, `ConnectedComponent.connected_induce_supp`,
`Embedding.induce`, and `Walk.map_isCycle_iff_of_injective`. The local work is
the finite-complement cardinality adapter and the acyclicity transport adapter.
All imported Mathlib sources are Apache 2.0; the project pins are unchanged.

The official newer Mathlib `Combinatorics/SimpleGraph/Acyclic.lean` also has
`IsAcyclic.induce` and `IsAcyclic.isTree_connectedComponent`; the latter uses
the newer `ConnectedComponent.toSimpleGraph` API. Its inspected toolchain is
Lean 4.34.0-rc2, so importing that file is incompatible with the Lean 4.19.0
pin. The two small pinned-API adapters below supply the relevant statements.
The searched newer cardinality/pigeonhole APIs and the official Lean 3 graph
library supplied no additional compatible finite-fiber result.

Inspected upstream sources (2026-09-06):
* https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Combinatorics/SimpleGraph/Acyclic.lean
* https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Fintype/Card.lean
* https://github.com/leanprover-community/mathlib4/blob/master/lean-toolchain
* https://github.com/leanprover-community/mathlib4/blob/master/LICENSE
* https://github.com/leanprover-community/mathlib/blob/master/src/combinatorics/simple_graph/acyclic.lean
-/

namespace KltDP.Lattices.SmallForestComponents

universe u v

/-- A fiber of a finite surjection leaves at least one domain element for each
of the other codomain elements. -/
theorem card_fiber_add_card_le_card_add_one
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (f : α → β) (hf : Function.Surjective f) (b : β)
    [Fintype {a // f a = b}] :
    Fintype.card {a // f a = b} + Fintype.card β ≤ Fintype.card α + 1 := by
  classical
  let g : {a // f a ≠ b} → {b' : β // b' ≠ b} :=
    fun a => ⟨f a, a.property⟩
  have hg : Function.Surjective g := by
    rintro ⟨b', hb'⟩
    obtain ⟨a, ha⟩ := hf b'
    refine ⟨⟨a, ?_⟩, ?_⟩
    · simpa only [ha] using hb'
    · exact Subtype.ext ha
  have hcomp := Fintype.card_le_of_surjective g hg
  simp only [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at hcomp
  have hfiber := Fintype.card_subtype_le (fun a => f a = b)
  omega

variable {V : Type u} (G : SimpleGraph V)

/-- The support of a component, together with one vertex from each other
actual component, fits inside the vertex type. -/
theorem card_component_add_card_components_le
    [Fintype V] [Fintype G.ConnectedComponent]
    (c : G.ConnectedComponent) [Fintype c.supp] :
    Fintype.card c.supp + Fintype.card G.ConnectedComponent ≤ Fintype.card V + 1 := by
  letI : Fintype {a // G.connectedComponentMk a = c} :=
    inferInstanceAs (Fintype c.supp)
  exact card_fiber_add_card_le_card_add_one G.connectedComponentMk
    (fun d => Quot.exists_rep d) c

/-- Five actual connected components on at most eight vertices force each
component support to have at most four vertices. -/
theorem component_card_le_four
    [Fintype V] [Fintype G.ConnectedComponent]
    (hV : Fintype.card V ≤ 8) (hC : 5 ≤ Fintype.card G.ConnectedComponent)
    (c : G.ConnectedComponent) [Fintype c.supp] :
    Fintype.card c.supp ≤ 4 := by
  have h := card_component_add_card_components_le G c
  omega

/-- The same actual-component bound without chosen `Fintype` instances. -/
theorem component_natCard_le_four [Finite V]
    (hV : Nat.card V ≤ 8) (hC : 5 ≤ Nat.card G.ConnectedComponent)
    (c : G.ConnectedComponent) : Nat.card c.supp ≤ 4 := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite G.ConnectedComponent
  letI : Fintype c.supp := Fintype.ofFinite c.supp
  rw [Nat.card_eq_fintype_card] at hV hC ⊢
  exact component_card_le_four G hV hC c

/-- Acyclicity is preserved by inducing on an arbitrary vertex set. -/
theorem isAcyclic_induce (hG : G.IsAcyclic) (s : Set V) : (G.induce s).IsAcyclic := by
  let e : G.induce s ↪g G := SimpleGraph.Embedding.induce s
  intro x p hp
  exact hG (p.map e.toHom)
    ((SimpleGraph.Walk.map_isCycle_iff_of_injective
      (f := e.toHom) (p := p) e.injective).2 hp)

/-- Each actual connected component of a forest induces a tree. No finiteness
hypothesis is required for this fact. -/
theorem component_isTree (hG : G.IsAcyclic) (c : G.ConnectedComponent) :
    (G.induce c.supp).IsTree :=
  ⟨c.connected_induce_supp, isAcyclic_induce G hG c.supp⟩

end KltDP.Lattices.SmallForestComponents

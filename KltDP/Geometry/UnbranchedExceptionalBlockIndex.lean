import KltDP.Geometry.ExceptionalForestClosedBlocks
import Mathlib.Data.Fintype.Card

/-!
# All unbranched original exceptional blocks and their exact vertex index

A selected isolated exceptional curve is its entire graph block. Therefore
the vertices in all blocks avoiding the selection are exactly all original
exceptional primes outside it. This retains the literal original block and
prime indices before constructing the cover copies.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.UnbranchedExceptionalBlocks

open NormalProjectiveSurface ActualExceptionalIncidence ExceptionalForestClosedBlocks

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (N : Finset S.PrimeCurve)

/-- All original graph blocks whose original primes are outside the selected branch. -/
abbrev Blocks :=
  {b : (graph π).ConnectedComponent // ∀ v ∈ b.supp, v.val ∉ N}

/-- All original vertices retained in all unbranched blocks, with the actual block labels. -/
abbrev BlockVertices := Σ b : Blocks π N, b.val.supp

/-- The original prime vertex underlying a retained block vertex. -/
def vertex (i : BlockVertices π N) : Vertices π := i.2.val

/-- Selected vertices are geometrically isolated from every other actual exceptional prime. -/
def IsolatedSelection : Prop :=
  ∀ A ∈ N, ∀ v : Vertices π, v.val ≠ A → Disjoint (A : Set S.toScheme) (v.val : Set S.toScheme)

variable (hiso : IsolatedSelection π N)

include hiso in
/-- A selected isolated vertex has no edge in the original exceptional graph. -/
theorem selected_not_adj (v : Vertices π) (hv : v.val ∈ N) (w : Vertices π) :
    ¬ (graph π).Adj v w := by
  intro h
  change v ≠ w ∧ ((v.val : Set S.toScheme) ∩ w.val).Nonempty at h
  have hne : w.val ≠ v.val := fun heq => h.1 (Subtype.ext heq.symm)
  have hd := hiso v.val hv w hne
  obtain ⟨x, hxv, hxw⟩ := h.2
  exact Set.disjoint_left.mp hd hxv hxw

include hiso in
/-- A selected isolated vertex is the only vertex in its original graph block. -/
theorem eq_of_selected_component (v w : Vertices π) (hv : v.val ∈ N)
    (h : (graph π).connectedComponentMk v = (graph π).connectedComponentMk w) : v = w := by
  obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.eq.mp h
  cases p with
  | nil => rfl
  | cons h p => exact (selected_not_adj π N hiso v hv _ h).elim

/-- The literal original vertex map is injective on all retained block vertices. -/
theorem vertex_injective : Function.Injective (vertex π N) := by
  rintro ⟨b, v⟩ ⟨c, w⟩ h
  have hbc : b = c := by
    apply Subtype.ext
    exact v.property.symm.trans ((congrArg (graph π).connectedComponentMk h).trans w.property)
  subst c
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext h))

/-- The block-labelled retained vertices are exactly all original exceptional primes outside N. -/
def outsideVertexEquiv : BlockVertices π N ≃ {v : Vertices π // v.val ∉ N} :=
  Equiv.ofBijective
    (fun i => ⟨vertex π N i, i.1.property i.2.val i.2.property⟩)
    ⟨fun i j h => vertex_injective π N (congrArg Subtype.val h), by
      rintro ⟨v, hv⟩
      let b := (graph π).connectedComponentMk v
      have hb : ∀ w ∈ b.supp, w.val ∉ N := by
        intro w hw hN
        have heq : w = v := eq_of_selected_component π N hiso w v hN hw
        exact hv (heq ▸ hN)
      exact ⟨⟨⟨b, hb⟩, ⟨v, rfl⟩⟩, rfl⟩⟩

/-- The selected original exceptional vertices have exactly the original finite selection index. -/
def selectedVertexEquiv (hN : ∀ A ∈ N, IsExceptionalCurve π A) :
    {v : Vertices π // v.val ∈ N} ≃ {A : S.PrimeCurve // A ∈ N} where
  toFun v := ⟨v.val.val, v.property⟩
  invFun A := ⟨⟨A.val, hN A.val A.property⟩, A.property⟩
  left_inv v := rfl
  right_inv A := rfl

include hiso in
/-- All unbranched blocks together retain exactly r minus n original exceptional vertices. -/
theorem card_blockVertices [IsProper π] (hbir : IsBirationalScheme π)
    (hN : ∀ A ∈ N, IsExceptionalCurve π A) :
    Nat.card (BlockVertices π N) = Nat.card (Vertices π) - N.card := by
  classical
  letI : Finite (Vertices π) := finite_vertices π hbir
  letI : Fintype (Vertices π) := Fintype.ofFinite _
  rw [Nat.card_congr (outsideVertexEquiv π N hiso), Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl]
  have hn : Fintype.card {v : Vertices π // v.val ∈ N} = N.card :=
    (Fintype.card_congr (selectedVertexEquiv π N hN)).trans (Fintype.card_coe N)
  rw [hn, Nat.card_eq_fintype_card]

end KltDP.Geometry.UnbranchedExceptionalBlocks

#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.outsideVertexEquiv
#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.card_blockVertices

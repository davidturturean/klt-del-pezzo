import KltDP.Geometry.RationalTreePicardComponentLeaf
import KltDP.Geometry.ActualExceptionalNoTriple

/-!
# An arbitrary component tree with its actual intersection points

The ordinary intersection graph omits loops and has an edge precisely when
two distinct original components meet. If it is a tree and each such
intersection is a subsingleton, then the bipartite graph retaining every
original intersection point is a tree as well.

The proof uses the pinned finite-tree cardinality criterion. Acyclicity of
the ordinary graph excludes triple points. Thus every point-side vertex has
degree two, and uniqueness of each pairwise intersection identifies the
neighbors of a component with its neighbors in the ordinary graph. Walks
lift by inserting their actual intersection points. No chain ordering or
identification of different scheme points is used.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace SimpleGraph
open scoped BigOperators

universe u

namespace KltDP.Geometry.RationalTreePicard

variable (X : Scheme.{u})

/-- Finitely many components with subsingleton pairwise intersections have
only finitely many actual intersection points. -/
theorem componentIntersectionPoints_finite_of_subsingleton [NoetherianSpace X]
    (hinter : ∀ C D : ↥(irreducibleComponents X), C ≠ D →
      (C.1 ∩ D.1).Subsingleton) :
    (componentIntersectionPoints X).Finite := by
  classical
  letI : Fintype ↥(irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.fintype
  choose A B hne hA hB using fun q : ↥(componentIntersectionPoints X) => q.2
  let f : ↥(componentIntersectionPoints X) →
      ↥(irreducibleComponents X) × ↥(irreducibleComponents X) := fun q => (A q, B q)
  have hf : Function.Injective f := by
    intro q r h
    have hAeq : A q = A r := congrArg Prod.fst h
    have hBeq : B q = B r := congrArg Prod.snd h
    apply Subtype.ext
    apply hinter (A q) (B q) (hne q) ⟨hA q, hB q⟩
    simpa only [hAeq, hBeq] using And.intro (hA r) (hB r)
  letI : Finite ↥(componentIntersectionPoints X) := Finite.of_injective f hf
  exact Set.toFinite _

/-- A walk in the ordinary component graph lifts by inserting an actual
intersection point at each edge. -/
theorem componentPointIncidenceGraph_reachable_inl
    {C D : ↥(irreducibleComponents X)}
    (h : (KltDP.Topology.incidenceGraph
      (fun E : ↥(irreducibleComponents X) => E.1)).Reachable C D) :
    (componentPointIncidenceGraph X).Reachable (.inl C) (.inl D) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .rfl
  | @cons C E D hCE p ih =>
    obtain ⟨x, hxC, hxE⟩ := hCE.2
    let q : ↥(componentIntersectionPoints X) := ⟨x, C, E, hCE.1, hxC, hxE⟩
    have hCq : (componentPointIncidenceGraph X).Adj (.inl C) (.inr q) := hxC
    have hqE : (componentPointIncidenceGraph X).Adj (.inr q) (.inl E) := hxE
    exact hCq.reachable.trans (hqE.reachable.trans ih)

/-- Connectedness of the ordinary component graph gives connectedness of
the graph whose extra vertices are the original intersection points. -/
theorem componentPointIncidenceGraph_connected_of_incidence
    (hG : (KltDP.Topology.incidenceGraph
      (fun C : ↥(irreducibleComponents X) => C.1)).Connected) :
    (componentPointIncidenceGraph X).Connected := by
  letI : Nonempty ↥(irreducibleComponents X) := hG.nonempty
  have hto : ∀ v : ↥(irreducibleComponents X) ⊕ ↥(componentIntersectionPoints X),
      ∃ C : ↥(irreducibleComponents X),
        (componentPointIncidenceGraph X).Reachable v (.inl C) := by
    intro v
    rcases v with C | q
    · exact ⟨C, .rfl⟩
    · obtain ⟨C, D, hCD, hqC, hqD⟩ := q.2
      exact ⟨C, (show (componentPointIncidenceGraph X).Adj (.inr q) (.inl C)
        from hqC).reachable⟩
  refine ⟨?_⟩
  intro v w
  obtain ⟨C, hv⟩ := hto v
  obtain ⟨D, hw⟩ := hto w
  exact hv.trans ((componentPointIncidenceGraph_reachable_inl X (hG C D)).trans hw.symm)

/-- An arbitrary ordinary tree of components with subsingleton pairwise
intersections remains a tree after inserting each actual intersection point
as a vertex. In particular, the statement does not require a chain. -/
theorem componentPointIncidenceGraph_isTree_of_incidence [NoetherianSpace X]
    (hTree : (KltDP.Topology.incidenceGraph
      (fun C : ↥(irreducibleComponents X) => C.1)).IsTree)
    (hinter : ∀ C D : ↥(irreducibleComponents X), C ≠ D →
      (C.1 ∩ D.1).Subsingleton) :
    (componentPointIncidenceGraph X).IsTree := by
  classical
  letI : Fintype ↥(irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.fintype
  letI : Fintype ↥(componentIntersectionPoints X) :=
    (componentIntersectionPoints_finite_of_subsingleton X hinter).fintype
  let G := KltDP.Topology.incidenceGraph
    (fun C : ↥(irreducibleComponents X) => C.1)
  let H := componentPointIncidenceGraph X
  have hthree (C D E : ↥(irreducibleComponents X)) (x : X)
      (hxC : x ∈ C.1) (hxD : x ∈ D.1) (hxE : x ∈ E.1) :
      C = D ∨ C = E ∨ D = E :=
    KltDP.Topology.no_three_of_incidence_isAcyclic
      (fun A : ↥(irreducibleComponents X) => A.1) hTree.IsAcyclic
      C D E x hxC hxD hxE
  have hdegQ (q : ↥(componentIntersectionPoints X)) : H.degree (.inr q) = 2 := by
    obtain ⟨C, D, hCD, hqC, hqD⟩ := q.2
    have hn : H.neighborFinset (.inr q) = {.inl C, .inl D} := by
      ext v
      rw [H.mem_neighborFinset]
      rcases v with E | r
      · change q.1 ∈ E.1 ↔ Sum.inl E ∈
          ({Sum.inl C, Sum.inl D} :
            Finset (↥(irreducibleComponents X) ⊕ ↥(componentIntersectionPoints X)))
        simp only [Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq]
        constructor
        · intro hqE
          rcases hthree C D E q.1 hqC hqD hqE with h | h | h
          · exact (hCD h).elim
          · exact Or.inl h.symm
          · exact Or.inr h.symm
        · rintro (rfl | rfl)
          · exact hqC
          · exact hqD
      · simp [H, componentPointIncidenceGraph]
    change (H.neighborFinset (.inr q)).card = 2
    rw [hn]
    simp [hCD]
  have hdegC (C : ↥(irreducibleComponents X)) : H.degree (.inl C) = G.degree C := by
    let q : G.neighborSet C → ↥(componentIntersectionPoints X) := fun D =>
      ⟨D.2.2.choose, C, D.1, D.2.1, D.2.2.choose_spec.1, D.2.2.choose_spec.2⟩
    have hqC (D : G.neighborSet C) : (q D).1 ∈ C.1 := D.2.2.choose_spec.1
    have hqD (D : G.neighborSet C) : (q D).1 ∈ D.1.1 := D.2.2.choose_spec.2
    let f : G.neighborSet C → H.neighborSet (.inl C) :=
      fun D => ⟨.inr (q D), hqC D⟩
    have hf : Function.Injective f := by
      intro D E h
      have hq : q D = q E := Sum.inr.inj (congrArg Subtype.val h)
      have hqE : (q D).1 ∈ E.1.1 := by rw [hq]; exact hqD E
      apply Subtype.ext
      rcases hthree C D.1 E.1 (q D).1 (hqC D) (hqD D) hqE with h | h | h
      · exact (D.2.1 h).elim
      · exact (E.2.1 h).elim
      · exact h
    have hs : Function.Surjective f := by
      rintro ⟨v, hv⟩
      rcases v with E | r
      · exact False.elim hv
      · change r.1 ∈ C.1 at hv
        obtain ⟨A, B, hAB, hrA, hrB⟩ := r.2
        have hex : ∃ D : ↥(irreducibleComponents X), C ≠ D ∧ r.1 ∈ D.1 := by
          by_cases hAC : A = C
          · subst A
            exact ⟨B, hAB, hrB⟩
          · exact ⟨A, Ne.symm hAC, hrA⟩
        obtain ⟨D, hCD, hrD⟩ := hex
        let d : G.neighborSet C := ⟨D, hCD, r.1, hv, hrD⟩
        have hqr : q d = r := Subtype.ext
          (hinter C D hCD ⟨hqC d, hqD d⟩ ⟨hv, hrD⟩)
        refine ⟨d, ?_⟩
        apply Subtype.ext
        change Sum.inr (q d) = Sum.inr r
        exact congrArg Sum.inr hqr
    have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hf, hs⟩)
    rw [G.card_neighborSet_eq_degree, H.card_neighborSet_eq_degree] at hc
    exact hc.symm
  have hsum : (∑ v, H.degree v) =
      (∑ C, G.degree C) + 2 * Fintype.card ↥(componentIntersectionPoints X) := by
    rw [Fintype.sum_sum_type]
    simp_rw [hdegC, hdegQ]
    simp [Nat.mul_comm]
  rw [H.sum_degrees_eq_twice_card_edges, G.sum_degrees_eq_twice_card_edges] at hsum
  have hcardG := hTree.card_edgeFinset
  change G.edgeFinset.card + 1 = Fintype.card ↥(irreducibleComponents X) at hcardG
  apply isTree_iff_connected_and_card.mpr
  refine ⟨componentPointIncidenceGraph_connected_of_incidence X hTree.isConnected, ?_⟩
  change Nat.card H.edgeSet + 1 = Nat.card
    (↥(irreducibleComponents X) ⊕ ↥(componentIntersectionPoints X))
  simp only [Nat.card_eq_fintype_card, ← H.edgeFinset_card, Fintype.card_sum]
  omega

end KltDP.Geometry.RationalTreePicard

#print axioms KltDP.Geometry.RationalTreePicard.componentIntersectionPoints_finite_of_subsingleton
#print axioms KltDP.Geometry.RationalTreePicard.componentPointIncidenceGraph_reachable_inl
#print axioms KltDP.Geometry.RationalTreePicard.componentPointIncidenceGraph_connected_of_incidence
#print axioms KltDP.Geometry.RationalTreePicard.componentPointIncidenceGraph_isTree_of_incidence

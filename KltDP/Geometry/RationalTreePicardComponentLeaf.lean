import KltDP.Geometry.RationalTreePicardComponentPartition
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# A leaf cut retaining the actual intersection points

The graph here has the original irreducible components and the original
points lying on at least two components as vertices. Its edges are literal
membership. In particular, two different intersection points remain two
different vertices and are not merged into a single component edge.

If this actual graph is a finite tree with at least two components, some
component meets the union of the others at exactly one original point.
Every original affine chart through that point has singleton support for
the actual sum of the two component ideals. Reducedness of this sum-ideal
quotient still requires the geometric transversality argument.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace SimpleGraph
open scoped BigOperators

universe u

namespace KltDP.Geometry.RationalTreePicard

variable (X : Scheme.{u})

/-- Original scheme points belonging to two distinct original components. -/
def componentIntersectionPoints : Set X :=
  {x | ∃ C D : ↥(irreducibleComponents X), C ≠ D ∧ x ∈ C.1 ∧ x ∈ D.1}

/-- The incidence graph retains each actual intersection point. -/
def componentPointIncidenceGraph :
    SimpleGraph (↥(irreducibleComponents X) ⊕ ↥(componentIntersectionPoints X)) where
  Adj
    | .inl C, .inr q => q.1 ∈ C.1
    | .inr q, .inl C => q.1 ∈ C.1
    | _, _ => False
  symm := by
    intro v w h
    cases v <;> cases w <;> exact h
  loopless := by
    intro v
    cases v <;> exact fun h => h

variable [NoetherianSpace X] [Nontrivial ↥(irreducibleComponents X)]

/-- A tree of actual component-point incidences has an actual component
whose entire intersection with the other components is one original point.
Point-side vertices cannot be leaves: each belongs to two distinct components. -/
theorem exists_component_leaf_intersection
    (hfinite : (componentIntersectionPoints X).Finite)
    (hTree : (componentPointIncidenceGraph X).IsTree) :
    ∃ (C : ↥(irreducibleComponents X)) (q : ↥(componentIntersectionPoints X)),
      C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) = {q.1} := by
  classical
  letI : Fintype ↥(irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.fintype
  letI : Fintype ↥(componentIntersectionPoints X) := hfinite.fintype
  let G := componentPointIncidenceGraph X
  have hlow : ∃ v, G.degree v ≤ 1 := by
    by_contra h
    have hdeg : ∀ v, 2 ≤ G.degree v := by
      intro v
      have hn : ¬ G.degree v ≤ 1 := fun hv => h ⟨v, hv⟩
      omega
    have hsum : 2 * Fintype.card
        (↥(irreducibleComponents X) ⊕ ↥(componentIntersectionPoints X)) ≤
          ∑ v, G.degree v := by
      calc
        _ = ∑ _v : ↥(irreducibleComponents X) ⊕ ↥(componentIntersectionPoints X),
            (2 : ℕ) := by simp [Nat.mul_comm]
        _ ≤ _ := Finset.sum_le_sum (fun v _ => hdeg v)
    rw [G.sum_degrees_eq_twice_card_edges] at hsum
    have hcard := hTree.card_edgeFinset
    change G.edgeFinset.card + 1 = Fintype.card
      (↥(irreducibleComponents X) ⊕ ↥(componentIntersectionPoints X)) at hcard
    omega
  obtain ⟨v, hv⟩ := hlow
  rcases v with C | q
  · obtain ⟨D, hDC⟩ := exists_ne C
    obtain ⟨p⟩ := hTree.isConnected (.inl C) (.inl D)
    have hp : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne
      (fun h => hDC (Sum.inl.inj h).symm)
    have hpos : 0 < G.degree (.inl C) :=
      (G.degree_pos_iff_exists_adj _).mpr ⟨p.snd, p.adj_snd hp⟩
    have hdegree : (G.neighborFinset (.inl C)).card = 1 := by
      change G.degree (.inl C) = 1
      omega
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hdegree
    have hadj : G.Adj (.inl C) w := by
      apply (G.mem_neighborFinset (.inl C) w).mp
      rw [hw]
      exact Finset.mem_singleton_self w
    rcases w with D | q
    · exact False.elim hadj
    · refine ⟨C, q, ?_⟩
      ext x
      constructor
      · rintro ⟨hxC, hxOther⟩
        obtain ⟨D, hD, hxD⟩ := (mem_componentClosedUnion X ({C}ᶜ) x).mp hxOther
        have hCD : C ≠ D := by
          intro h
          exact hD (Set.mem_singleton_iff.mpr h.symm)
        let p : ↥(componentIntersectionPoints X) := ⟨x, C, D, hCD, hxC, hxD⟩
        have hpAdj : G.Adj (.inl C) (.inr p) := hxC
        have hpMem := (G.mem_neighborFinset (.inl C) (.inr p)).mpr hpAdj
        rw [hw] at hpMem
        have hpq : p = q := Sum.inr.inj (Finset.mem_singleton.mp hpMem)
        exact Set.mem_singleton_iff.mpr (congrArg Subtype.val hpq)
      · intro hx
        have hxq : x = q.1 := Set.mem_singleton_iff.mp hx
        subst x
        refine ⟨hadj, ?_⟩
        obtain ⟨D, E, hDE, hqD, hqE⟩ := q.2
        apply (mem_componentClosedUnion X ({C}ᶜ) q.1).mpr
        by_cases hDC : D = C
        · subst D
          exact ⟨E, fun h => hDE (Set.mem_singleton_iff.mp h).symm, hqE⟩
        · exact ⟨D, fun h => hDC (Set.mem_singleton_iff.mp h), hqD⟩
  · obtain ⟨C, D, hCD, hqC, hqD⟩ := q.2
    have hC : .inl C ∈ G.neighborFinset (.inr q) :=
      (G.mem_neighborFinset (.inr q) (.inl C)).mpr hqC
    have hD : .inl D ∈ G.neighborFinset (.inr q) :=
      (G.mem_neighborFinset (.inr q) (.inl D)).mpr hqD
    have heq := (Finset.card_le_one.mp hv) (.inl C) hC (.inl D) hD
    exact False.elim (hCD (Sum.inl.inj heq))

/-- The actual tree supplies the singleton-support input on every original
affine chart through its leaf's intersection point. -/
theorem exists_component_leaf_chart_support
    (hfinite : (componentIntersectionPoints X).Finite)
    (hTree : (componentPointIncidenceGraph X).IsTree) :
    ∃ (C : ↥(irreducibleComponents X)) (q : X),
      C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) = {q} ∧
      ∀ (U : X.affineOpens) (hq : q ∈ U.1),
        PrimeSpectrum.zeroLocus
            (componentChartIdeal X {C} U ⊔ componentChartIdeal X ({C}ᶜ) U :
              Ideal Γ(X, U.1)) =
          {U.2.primeIdealOf ⟨q, hq⟩} := by
  obtain ⟨C, q, hcut⟩ := exists_component_leaf_intersection X hfinite hTree
  refine ⟨C, q.1, hcut, ?_⟩
  intro U hq
  rw [componentChartIdeal_sup_zeroLocus, coe_componentClosedUnion_singleton, hcut]
  ext p
  change U.2.fromSpec.base p = q.1 ↔ p = U.2.primeIdealOf ⟨q.1, hq⟩
  constructor
  · intro hp
    apply U.2.fromSpec.isOpenEmbedding.injective
    exact hp.trans (U.2.fromSpec_primeIdealOf ⟨q.1, hq⟩).symm
  · rintro rfl
    exact U.2.fromSpec_primeIdealOf ⟨q.1, hq⟩

end KltDP.Geometry.RationalTreePicard

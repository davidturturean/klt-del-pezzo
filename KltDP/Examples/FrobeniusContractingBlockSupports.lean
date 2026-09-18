import KltDP.Examples.FrobeniusGraphFiberDisjointSPn
import KltDP.Examples.FrobeniusMultiCentreFiberContacts
import KltDP.Examples.FrobeniusMultiCentreGraphContacts

/-!
# The disjoint original blocks of the Frobenius contracting support

The graph, each strict special fiber, and each old exceptional chain have
pairwise disjoint original supports. Every statement below follows from
the proved incidence theorems of the original blowups; no contraction,
canonical class, intersection-matrix criterion, or replacement curves enter.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Examples.FrobeniusContractingBlockSupports

open KltDP.Geometry FrobeniusMultiCentreSurface FrobeniusMultiCentreGraphFiber
open FrobeniusMultiCentreExceptional FrobeniusGraphFiberDisjointSPn
open FrobeniusMultiCentreGraphContacts FrobeniusMultiCentreFiberContacts

variable {k : Type u} [Field k]
  (q n : ℕ) (a : Fin n → k)

/-- The graph, strict-fiber, and old-chain block labels. -/
abbrev BlockIndex (n : ℕ) := Option (Fin n ⊕ Fin n)

/-- Original supports of the disjoint blocks, without the newest exceptional curves. -/
def blockSupport : BlockIndex n → Set (multiSurface (q + 1) n a)
  | none => Set.range (graphStrictι (q + 1) n a).base
  | some (.inl i) => Set.range (fiberStrictι (q + 1) n a i).base
  | some (.inr i) => ⋃ j : Fin q, exceptionalSupport q n a i (.inl j)

/-- Each original block support is closed. -/
theorem blockSupport_isClosed (r : BlockIndex n) : IsClosed (blockSupport q n a r) := by
  cases r with
  | none => exact (graphStrictι (q + 1) n a).isClosedEmbedding.isClosed_range
  | some r =>
      cases r with
      | inl i => exact (fiberStrictι (q + 1) n a i).isClosedEmbedding.isClosed_range
      | inr i => exact isClosed_iUnion_of_finite fun j =>
          exceptionalSupport_isClosed q n a i (.inl j)

variable [IsAlgClosed k] [Fact (q + 1).Prime] [CharP k (q + 1)]

private theorem graph_old_disjoint (i : Fin n) :
    Disjoint (blockSupport q n a none) (blockSupport q n a (some (.inr i))) :=
  Set.disjoint_iUnion_right.mpr fun j => graphStrict_disjoint_exceptional_same q n a i j

private theorem fiber_old_disjoint (ha : Function.Injective a) (i i' : Fin n) :
    Disjoint (blockSupport q n a (some (.inl i)))
      (blockSupport q n a (some (.inr i'))) := by
  apply Set.disjoint_iUnion_right.mpr
  intro j
  by_cases h : i = i'
  · subst i'
    exact fiberStrict_disjoint_exceptional_same q n a i j
  · exact fiberStrict_disjoint_exceptional q n a ha h (.inl j)

private theorem old_old_disjoint (ha : Function.Injective a) {i i' : Fin n} (h : i ≠ i') :
    Disjoint (blockSupport q n a (some (.inr i)))
      (blockSupport q n a (some (.inr i'))) :=
  Set.disjoint_iUnion_left.mpr fun j => Set.disjoint_iUnion_right.mpr fun j' =>
    exceptionalSupport_disjoint_of_ne q n a ha h (.inl j) (.inl j')

/-- The graph, strict fibers, and old chains form pairwise disjoint original blocks. -/
theorem blockSupport_pairwise (ha : Function.Injective a) :
    Pairwise (fun r s : BlockIndex n => Disjoint (blockSupport q n a r) (blockSupport q n a s)) := by
  intro r s hrs
  cases r with
  | none =>
      cases s with
      | none => exact (hrs rfl).elim
      | some s =>
          cases s with
          | inl i => exact graphStrict_fiberStrict_disjoint' q n a i
          | inr i => exact graph_old_disjoint q n a i
  | some r =>
      cases r with
      | inl i =>
          cases s with
          | none => exact (graphStrict_fiberStrict_disjoint' q n a i).symm
          | some s =>
              cases s with
              | inl j =>
                  exact fiberStrict_disjoint (q + 1) n a ha
                    (fun h => hrs (congrArg (fun t : Fin n => some (Sum.inl t)) h))
              | inr j => exact fiber_old_disjoint q n a ha i j
      | inr i =>
          cases s with
          | none => exact (graph_old_disjoint q n a i).symm
          | some s =>
              cases s with
              | inl j => exact (fiber_old_disjoint q n a ha j i).symm
              | inr j =>
                  exact old_old_disjoint q n a ha
                    (fun h => hrs (congrArg (fun t : Fin n => some (Sum.inr t)) h))

end KltDP.Examples.FrobeniusContractingBlockSupports

import KltDP.Geometry.UnbranchedExceptionalBlockIndex

/-!
# Actual isolated graph vertices supply geometric branch isolation

The graph uses intersections of the original exceptional prime carriers.
Its absence of edges at the selected original vertices therefore gives
exactly the geometric isolation used by the whole-forest cover producer.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.UnbranchedExceptionalBlocks

open NormalProjectiveSurface ActualExceptionalIncidence

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (N : Finset S.PrimeCurve)

/-- No edge at each selected actual exceptional vertex implies geometric isolation. -/
theorem isolatedSelection_of_no_adj
    (hN : ∀ A ∈ N, IsExceptionalCurve π A)
    (hgraph : ∀ v : Vertices π, v.val ∈ N → ∀ w : Vertices π, ¬ (graph π).Adj v w) :
    IsolatedSelection π N := by
  intro A hA v hv
  apply Set.disjoint_left.mpr
  intro x hxA hxv
  apply hgraph ⟨A, hN A hA⟩ hA v
  change (⟨A, hN A hA⟩ : Vertices π) ≠ v ∧
    ((A : Set S.toScheme) ∩ (v.val : Set S.toScheme)).Nonempty
  refine ⟨?_, x, hxA, hxv⟩
  intro h
  exact hv (congrArg Subtype.val h).symm

/-- For an original exceptional selection, graph and geometric isolation agree. -/
theorem isolatedSelection_iff_no_adj
    (hN : ∀ A ∈ N, IsExceptionalCurve π A) :
    IsolatedSelection π N ↔
      ∀ v : Vertices π, v.val ∈ N → ∀ w : Vertices π, ¬ (graph π).Adj v w :=
  ⟨fun h => selected_not_adj π N h, isolatedSelection_of_no_adj π N hN⟩

end KltDP.Geometry.UnbranchedExceptionalBlocks

#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.isolatedSelection_iff_no_adj

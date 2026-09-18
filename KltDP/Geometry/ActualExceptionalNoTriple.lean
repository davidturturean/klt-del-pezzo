import KltDP.Geometry.ActualExceptionalForest

/-!
# No three distinct actual exceptional curves pass through one point

Three actual common-point incidences give a triangle in the original graph.
Pinned acyclic path uniqueness excludes that triangle: its direct path and
two-edge path have different lengths. The actual canonical-row forest
producer supplies acyclicity, giving the no-triple-point part of the SNC
interface. Transversality at the remaining double points is separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix SimpleGraph

universe u v w

namespace KltDP.Topology

private theorem not_triangle_of_isAcyclic {I : Type u} (G : SimpleGraph I)
    (hG : G.IsAcyclic) {i j l : I}
    (hij : G.Adj i j) (hjl : G.Adj j l) (hli : G.Adj l i) : False := by
  let p : G.Path i j := ⟨Walk.cons hij Walk.nil, by
    simp [Walk.isPath_def, hij.ne]⟩
  let q : G.Path i j := ⟨Walk.cons hli.symm (Walk.cons hjl.symm Walk.nil), by
    simp [Walk.isPath_def, hij.ne, hli.ne, hli.ne.symm, hjl.ne, hjl.ne.symm]⟩
  have hlen := congrArg (fun r : G.Path i j => r.val.length) (hG.path_unique p q)
  simp [p, q] at hlen

/-- In an arbitrary family of sets with acyclic incidence graph, any
three members containing one original point have a repeated index. -/
theorem no_three_of_incidence_isAcyclic {I : Type u} {T : Type v}
    (sets : I → Set T) (hG : (incidenceGraph sets).IsAcyclic)
    (i j l : I) (x : T) (hi : x ∈ sets i) (hj : x ∈ sets j) (hl : x ∈ sets l) :
    i = j ∨ i = l ∨ j = l := by
  classical
  by_cases hij : i = j
  · exact Or.inl hij
  by_cases hil : i = l
  · exact Or.inr (Or.inl hil)
  by_cases hjl : j = l
  · exact Or.inr (Or.inr hjl)
  exact (not_triangle_of_isAcyclic (incidenceGraph sets) hG
    ⟨hij, ⟨x, hi, hj⟩⟩ ⟨hjl, ⟨x, hj, hl⟩⟩ ⟨Ne.symm hil, ⟨x, hl, hi⟩⟩).elim

end KltDP.Topology

namespace KltDP.Geometry.ActualExceptionalNoTriple

/-- For actual contracted primes satisfying the original canonical rows
and klt bounds, no original surface point lies on three distinct members. -/
theorem no_three_mem
    {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π]
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (hbir : IsBirationalScheme π)
    (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)
    {I : Type w} [Fintype I] (C : I → S.PrimeCurve) (hinj : Function.Injective C)
    (hcontracted : ∀ i, IsExceptionalCurve π (C i))
    (d : I → ℚ) (hlower : ∀ i, -1 < d i) (hupper : ∀ i, d i ≤ 0)
    (hrow : NullCurveIntersectionMatrix.intersectionMatrix S hregular C *ᵥ d =
      fun i => -NullCurveIntersectionMatrix.intersectionMatrix S hregular C i i - 2)
    (i j l : I) (x : S.Point)
    (hi : x ∈ (C i : Set S.toScheme)) (hj : x ∈ (C j : Set S.toScheme))
    (hl : x ∈ (C l : Set S.toScheme)) : i = j ∨ i = l ∨ j = l := by
  have hG := (ActualExceptionalForest.forest_and_intersection_le_one
    π hπ hbir hregular C hinj hcontracted d hlower hupper hrow).1
  exact KltDP.Topology.no_three_of_incidence_isAcyclic
    (fun a => (C a : Set S.toScheme)) hG i j l x hi hj hl

end KltDP.Geometry.ActualExceptionalNoTriple

#print axioms KltDP.Topology.no_three_of_incidence_isAcyclic
#print axioms KltDP.Geometry.ActualExceptionalNoTriple.no_three_mem

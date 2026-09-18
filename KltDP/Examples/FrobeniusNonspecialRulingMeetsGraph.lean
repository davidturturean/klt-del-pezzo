import KltDP.Examples.FrobeniusSpecialFiberSPn
import KltDP.Examples.FrobeniusMultiCentreGraphProjectiveLine
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The original nonspecial ruling fibers meet the original strict graph

An actual root of `x^(q+1) = c` gives an original graph point at height `c`.
The original global graph parametrization lifts it to the independently
constructed strict graph. The graph point avoids every selected center,
so injectivity of the original projection on the centers complement
identifies it with the accepted unaffected fiber lift. The accepted
`unaffectedFiberIso` then gives a point of the literal scheme pullback.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusNonspecialRulingMeetsGraph

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusProjectiveMorphism
  FrobeniusGraphClosed FrobeniusGraphRationalPoints FrobeniusGraphPicardClassZeroFiber
  FrobeniusMultiCentreSurface FrobeniusMultiCentreGraphFiber
  FrobeniusMultiCentreGraphProjectiveLine FrobeniusSpecialFiberTower FrobeniusSpecialFiberSPn

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (q n : ℕ) (a : Fin n → k)
variable [Fact (q + 1).Prime] [CharP k (q + 1)]

/-- Every point of the original global parametrization lies in the original strict graph. -/
theorem globalGraphParametrization_mem_graphStrict (z : projectiveSpace k 1) :
    (globalGraphParametrization (q + 1) n a).base z ∈
      Set.range (graphStrictι (q + 1) n a).base := by
  let e := globalGraphIsoProjectiveLine (q + 1) n a
  have he : e.inv ≫ graphStrictι (q + 1) n a =
      globalGraphParametrization (q + 1) n a := by
    rw [← globalGraphIsoProjectiveLine_hom_inclusion, Iso.inv_hom_id_assoc]
  refine ⟨e.inv.base z, ?_⟩
  rw [← Scheme.comp_base_apply, he]

/-- The parametrization carries the original rational coordinate to the original graph point. -/
theorem globalGraphParametrization_point_projection (x : k) :
    (multiProjection (q + 1) n a).base
        ((globalGraphParametrization (q + 1) n a).base (point x)) =
      graphPoint (q + 1) x := by
  rw [← Scheme.comp_base_apply, globalGraphParametrization_projection]
  change fieldMorphismPoint (pointMorphism x ≫ projectiveGraphMorphism (q + 1)) = _
  rw [pointMorphism_projectiveGraphMorphism]
  rfl

/-- The accepted unaffected fiber lift projects to the original horizontal fiber. -/
@[reassoc] theorem unaffectedFiberLift_projection (c : k)
    (hc : ∀ j, c ≠ a j ^ (q + 1)) :
    unaffectedFiberLift q n a c hc ≫ multiProjection (q + 1) n a =
      horizontalFiberMorphism c := by
  simpa only [Category.id_comp] using (unaffectedFiberLift_isPullback q n a c hc).w

/-- The original unaffected ruling line has an actual point on the original strict graph. -/
theorem unaffectedFiberLift_meets_graphStrict (c : k)
    (hc : ∀ j, c ≠ a j ^ (q + 1)) :
    (Set.range (unaffectedFiberLift q n a c hc).base ∩
      Set.range (graphStrictι (q + 1) n a).base).Nonempty := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.succ_pos q)
  have hC : graphPoint (q + 1) x ∈ centersComplement (q + 1) n a := by
    rw [mem_centersComplement_iff]
    intro j hj
    apply hc j
    exact hx.symm.trans (congrArg (fun t : k => t ^ (q + 1))
      (graphPoint_injective (q + 1) hj))
  obtain ⟨y, hy⟩ := graphPoint_mem_horizontalFiber (q + 1) x
  rw [hx] at hy
  let z := (globalGraphParametrization (q + 1) n a).base (point x)
  have hz : (multiProjection (q + 1) n a).base z = graphPoint (q + 1) x :=
    globalGraphParametrization_point_projection q n a x
  have he : (unaffectedFiberLift q n a c hc).base y = z := by
    apply multiProjection_injective_on_complement q n a
    · change (multiProjection (q + 1) n a).base
        ((unaffectedFiberLift q n a c hc).base y) ∈ centersComplement (q + 1) n a
      rw [← Scheme.comp_base_apply, unaffectedFiberLift_projection, hy]
      exact hC
    · change (multiProjection (q + 1) n a).base z ∈ centersComplement (q + 1) n a
      rw [hz]
      exact hC
    · rw [← Scheme.comp_base_apply, unaffectedFiberLift_projection, hy, hz]
  exact ⟨z, ⟨y, he⟩, globalGraphParametrization_mem_graphStrict q n a (point x)⟩

/-- The literal complete scheme fiber over a non-selected height meets the original strict graph. -/
theorem unaffectedFiber_meets_graphStrict (c : k)
    (hc : ∀ j, c ≠ a j ^ (q + 1)) :
    (Set.range (pullback.fst (multiProjection (q + 1) n a)
        (horizontalFiberMorphism c)).base ∩
      Set.range (graphStrictι (q + 1) n a).base).Nonempty := by
  obtain ⟨z, ⟨y, hy⟩, hz⟩ := unaffectedFiberLift_meets_graphStrict q n a c hc
  refine ⟨z, ⟨(unaffectedFiberIso q n a c hc).hom.base y, ?_⟩, hz⟩
  have he : (unaffectedFiberIso q n a c hc).hom ≫
      pullback.fst (multiProjection (q + 1) n a) (horizontalFiberMorphism c) =
      unaffectedFiberLift q n a c hc :=
    (unaffectedFiberLift_isPullback q n a c hc).isoPullback_hom_fst
  rw [← Scheme.comp_base_apply, he]
  exact hy

/-- In particular the two original supports are not disjoint. -/
theorem unaffectedFiber_not_disjoint_graphStrict (c : k)
    (hc : ∀ j, c ≠ a j ^ (q + 1)) :
    ¬ Disjoint (Set.range (pullback.fst (multiProjection (q + 1) n a)
        (horizontalFiberMorphism c)).base)
      (Set.range (graphStrictι (q + 1) n a).base) := by
  intro h
  obtain ⟨z, hz, hB⟩ := unaffectedFiber_meets_graphStrict q n a c hc
  exact Set.disjoint_left.mp h hz hB

end KltDP.Examples.FrobeniusNonspecialRulingMeetsGraph

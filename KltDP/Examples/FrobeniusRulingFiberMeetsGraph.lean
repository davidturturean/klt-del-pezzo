import KltDP.Examples.FrobeniusNonspecialRulingMeetsGraph
import KltDP.Examples.FrobeniusPowerInfinity

/-!
# The literal original ruling fibers meet the original strict graph

These statements use the pullback of the original second ruling at the
actual finite rational section or the actual infinity section. The finite
case transports the proved unaffected-fiber point through the original
projection identity. At infinity the actual graph parametrization provides
a point because the original power morphism fixes the original infinity
point. No graph-meeting point or replacement fiber is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusRulingFiberMeetsGraph

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusProjectiveMorphism
  FrobeniusGraphClosed FrobeniusGraphPicardClassZeroFiber FrobeniusMultiCentreSurface
  FrobeniusMultiCentreGraphFiber FrobeniusMultiCentreGraphProjectiveLine
  FrobeniusSpecialFiberSPn FrobeniusNonspecialRulingMeetsGraph
  ProjectiveLinePointAtInfinity FrobeniusPowerInfinity

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (q n : ℕ) (a : Fin n → k)
variable [Fact (q + 1).Prime] [CharP k (q + 1)]

/-- A nonspecial finite fiber of the original second ruling meets the original strict graph. -/
theorem finiteRulingFiber_meets_graphStrict (c : k)
    (hc : ∀ j, c ≠ a j ^ (q + 1)) :
    (Set.range (pullback.fst (multiProjection (q + 1) n a ≫ secondProjection)
        (pointMorphism c)).base ∩
      Set.range (graphStrictι (q + 1) n a).base).Nonempty := by
  obtain ⟨z, ⟨y, hy⟩, hz⟩ := unaffectedFiberLift_meets_graphStrict q n a c hc
  have hf : unaffectedFiberLift q n a c hc ≫
      (multiProjection (q + 1) n a ≫ secondProjection) =
      projectiveSpaceToSpec k 1 ≫ pointMorphism c := by
    rw [← Category.assoc, unaffectedFiberLift_projection, horizontalFiberMorphism_snd]
  refine ⟨z, ?_, hz⟩
  rw [Scheme.Pullback.range_fst, Set.mem_preimage]
  refine ⟨(projectiveSpaceToSpec k 1).base y, ?_⟩
  change (projectiveSpaceToSpec k 1 ≫ pointMorphism c).base y =
    (multiProjection (q + 1) n a ≫ secondProjection).base z
  rw [← hy, ← Scheme.comp_base_apply, hf]

/-- The original global graph has its original infinity point over infinity in the ruling. -/
theorem globalGraphParametrization_infinity_ruling :
    (multiProjection (q + 1) n a ≫ secondProjection).base
        ((globalGraphParametrization (q + 1) n a).base (infinityPoint (k := k))) =
      infinityPoint := by
  have h : globalGraphParametrization (q + 1) n a ≫
      (multiProjection (q + 1) n a ≫ secondProjection) =
      projectivePowerMorphism (k := k) (q + 1) := by
    rw [← Category.assoc, globalGraphParametrization_projection,
      projectiveGraphMorphism_snd]
  rw [← Scheme.comp_base_apply, h]
  exact projectivePowerMorphism_infinityPoint (q + 1) (Nat.succ_pos q)

/-- The literal original infinity fiber meets the independently defined original strict graph. -/
theorem infinityRulingFiber_meets_graphStrict :
    (Set.range (pullback.fst (multiProjection (q + 1) n a ≫ secondProjection)
        (infinityMorphism (k := k))).base ∩
      Set.range (graphStrictι (q + 1) n a).base).Nonempty := by
  let z := (globalGraphParametrization (q + 1) n a).base (infinityPoint (k := k))
  refine ⟨z, ?_, globalGraphParametrization_mem_graphStrict q n a infinityPoint⟩
  rw [Scheme.Pullback.range_fst, Set.mem_preimage]
  refine ⟨IsLocalRing.closedPoint k, ?_⟩
  change fieldMorphismPoint (infinityMorphism (k := k)) =
    (multiProjection (q + 1) n a ≫ secondProjection).base z
  rw [fieldMorphismPoint_infinityMorphism]
  exact (globalGraphParametrization_infinity_ruling q n a).symm

end KltDP.Examples.FrobeniusRulingFiberMeetsGraph

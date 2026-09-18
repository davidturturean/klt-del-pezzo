import KltDP.Examples.EqualityAppendixSurfaceSmooth
import KltDP.Geometry.DisjointModificationPullbackIntegral

/-!
# Integrality of the original mixed appendix surface

Both original tower projections are isomorphisms on the common complement.
An actual point over that complement lies in both integral pieces of the
two-open cover. Reducedness descends through the original open stalk maps;
the existing two-open irreducibility lemma supplies irreducibility.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.EqualityAppendixSurface

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusMultiCentreSurface
  FrobeniusMultiCentreIntegral FrobeniusContactTowerInfinity
  FrobeniusStageComplement.PlaneChartedScheme
  FrobeniusTowerFunctionField.PlaneChartedScheme

variable {k : Type u} [Field k] [CharP k 3] [IsAlgClosed k]

theorem centersComplement_nonempty : Nonempty (centersComplement (k := k)) := by
  classical
  obtain ⟨c, hc⟩ := Infinite.exists_not_mem_finset
    (Finset.univ.image (finiteParameters (k := k)))
  refine ⟨⟨graphPoint 3 c, ?_, ?_⟩⟩
  · apply (mem_earlierComplement_iff 3 2 finiteParameters (graphPoint 3 c)).2
    intro i hi
    exact hc (Finset.mem_image.mpr
      ⟨i, Finset.mem_univ _, (graphPoint_injective 3 hi).symm⟩)
  · change graphPoint 3 c ≠ infinityCenter k
    exact (infinityCenter_ne_graphPoint 3 c).symm

theorem surface_isIntegral : IsIntegral (surface (k := k)) := by
  letI : IsIntegral (finiteSurface (k := k)) :=
    multiSurface_isIntegral 3 2 finiteParameters finiteParameters_injective
  letI : IsIntegral (infinityInitial k).carrier :=
    FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral
  letI : IsIntegral (infinityStage (k := k) 3) :=
    instStageIsIntegral (infinityInitial k) 3
  letI := finiteProjection_on_finiteComplement_isIso (k := k)
  letI := infinityProjection_on_infinityComplement_isIso (k := k)
  let c : centersComplement (k := k) := Classical.choice centersComplement_nonempty
  letI : Nonempty (infinityComplement ⊓ finiteComplement : (projectiveProduct k).Opens) :=
    ⟨⟨c.val, c.property.2, c.property.1⟩⟩
  exact DisjointModificationPullback.isIntegral finiteProjection (infinityProjection 3)
    infinityComplement finiteComplement complements_cover

end KltDP.Examples.EqualityAppendixSurface

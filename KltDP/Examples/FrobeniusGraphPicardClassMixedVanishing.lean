import KltDP.Examples.FrobeniusGraphPicardClassMixedSections

/-!
# The mixed equation vanishes on the original graph

The original graph over a mixed chart lies entirely in the corresponding
diagonal overlap. The equality of regular sections h=v*g_ii therefore
pulls back to zero under the original graph morphism, since g_ii is in
its actual kernel. Consequently D(h) is disjoint from the original
graph. No replacement closed subscheme or set-theoretic multiplicity
claim is used in this vanishing argument.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassMixedVanishing

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGraphPicardClassAffine FrobeniusGraphPicardClassCharts
open FrobeniusGraphPicardClassPowerCharts FrobeniusGraphPicardClassFrames
open FrobeniusGraphPicardClassMixedCover FrobeniusGraphPicardClassMixedCoordinates
open FrobeniusGraphPicardClassMixedSections

variable {k : Type u} [Field k]

/-- The actual original graph equation is killed on the original diagonal open. -/
theorem diagonalSection_graph_app_zero (p : ℕ) (i : Fin 2) :
    (projectiveGraphMorphism (k := k) p).app (diagonalOpen i) (diagonalSection p i) = 0 := by
  apply RingHom.mem_ker.mp
  change diagonalSection p i ∈
    RingHom.ker ((projectiveGraphMorphism (k := k) p).app
      (diagonalAffineOpen (k := k) i).1).hom
  rw [← Scheme.Hom.ker_apply (projectiveGraphMorphism p) (diagonalAffineOpen i)]
  change diagonalSection p i ∈ (graphIdeal p).ideal (diagonalAffineOpen i)
  rw [diagonalSection_ideal]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- The entire original graph over the mixed image lies over its diagonal overlap. -/
theorem graph_preimage_mixed_le_overlap (p : ℕ) (i : Fin 2) :
    projectiveGraphMorphism (k := k) p ⁻¹ᵁ productOpen i (otherIndex i) ≤
      projectiveGraphMorphism p ⁻¹ᵁ mixedDiagonalOverlap i := by
  intro q hq
  refine ⟨hq, ?_⟩
  have hm : (projectiveGraphMorphism p).base q ∈
      Set.range (productChart i (otherIndex i)).base := by
    simpa only [productOpen, Scheme.Hom.image_top_eq_opensRange] using hq
  have hd := graph_range_productChart_same_first p i (otherIndex i)
    ((projectiveGraphMorphism p).base q) ⟨q, rfl⟩ hm
  simpa only [diagonalOpen, Scheme.Hom.image_top_eq_opensRange] using hd

/-- The displayed mixed section belongs to the actual original graph kernel. -/
theorem mixedAmbientEquation_graph_app_zero (p : ℕ) (i : Fin 2) :
    (projectiveGraphMorphism (k := k) p).app (productOpen i (otherIndex i))
      (mixedAmbientEquation p i) = 0 := by
  let X := projectiveProduct k
  let f := projectiveGraphMorphism (k := k) p
  let M : X.Opens := productOpen i (otherIndex i)
  let U : X.Opens := diagonalOpen i
  let W : X.Opens := mixedDiagonalOverlap i
  let T := f ⁻¹ᵁ M
  have hT : T ≤ f ⁻¹ᵁ W := graph_preimage_mixed_le_overlap p i
  have hU : T ≤ f ⁻¹ᵁ U := fun q hq => (hT hq).2
  have H := congrArg (f.appLE W T hT).hom
    (mixed_equation_regular_factor (k := k) p i)
  have hM := ConcreteCategory.congr_hom
    (f.map_appLE hT (homOfLE (show W ≤ M from inf_le_left)).op)
      (mixedAmbientEquation (k := k) p i)
  simp only [Scheme.Hom.appLE_eq_app] at hM
  have hD := ConcreteCategory.congr_hom
    (f.map_appLE hT (homOfLE (show W ≤ U from inf_le_right)).op)
      (diagonalSection (k := k) p i)
  change f.appLE W T hT (X.presheaf.map (homOfLE (show W ≤ M from inf_le_left)).op
      (mixedAmbientEquation p i)) = f.app M (mixedAmbientEquation p i) at hM
  change f.appLE W T hT (X.presheaf.map (homOfLE (show W ≤ U from inf_le_right)).op
      (diagonalSection p i)) = f.appLE U T hU (diagonalSection p i) at hD
  have hz : f.appLE U T hU (diagonalSection p i) = 0 := by
    have hzero : f.app U (diagonalSection p i) = 0 :=
      diagonalSection_graph_app_zero (k := k) p i
    simp only [Scheme.Hom.appLE, ConcreteCategory.comp_apply, hzero, map_zero]
  rw [map_mul, hM, hD, hz, mul_zero] at H
  exact H

/-- The original graph has empty preimage of the companion mixed basic open D(h). -/
theorem graph_preimage_mixedEquation_basicOpen (p : ℕ) (i : Fin 2) :
    projectiveGraphMorphism (k := k) p ⁻¹ᵁ
      (projectiveProduct k).basicOpen (mixedAmbientEquation p i) = ⊥ := by
  rw [Scheme.preimage_basicOpen, mixedAmbientEquation_graph_app_zero, Scheme.basicOpen_zero]

/-- This actual open contains no point of the original graph, including at the mixed point. -/
theorem mixedEquation_basicOpen_disjoint_graph (p : ℕ) (i : Fin 2) :
    Disjoint ((projectiveProduct k).basicOpen (mixedAmbientEquation p i) : Set (projectiveProduct k))
      (Set.range (projectiveGraphMorphism (k := k) p).base) := by
  apply Set.disjoint_left.mpr
  rintro x hx ⟨q, rfl⟩
  have hq : q ∈ projectiveGraphMorphism p ⁻¹ᵁ
      (projectiveProduct k).basicOpen (mixedAmbientEquation p i) := hx
  rw [graph_preimage_mixedEquation_basicOpen] at hq
  exact hq

end KltDP.Examples.FrobeniusGraphPicardClassMixedVanishing

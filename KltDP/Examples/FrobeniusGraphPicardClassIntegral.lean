import KltDP.Examples.FrobeniusGraphPicardClassCharts
import KltDP.Geometry.ProjectiveSpaceIntegral
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Integrality of the original projective product

The actual four polynomial-domain charts have pairwise nonempty overlaps.
Their ranges are irreducible, and two applications of irreducibility in
those ranges prove that the covered product is irreducible. The original
open-immersion stalk maps transfer reducedness from the polynomial charts.
Thus the actual product has the function field needed for the graph's
Cartier principal relation.

The newer official geometrically-integral pullback theorem was reviewed;
it requires additional general infrastructure and a geometric-integrality
adapter for the original Proj. This proof reuses the pinned point-lifting,
chart-range, irreducible-image and stalk-reducedness results directly.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassIntegral

open KltDP.Geometry ProjectiveLineComparison
open FrobeniusProjectivePoints FrobeniusBlowupContact FrobeniusGraphPicardClassCharts

variable {k : Type u} [Field k]

/-- Each chart range is exactly the indicated pair of original standard opens. -/
theorem productChart_range (i j : Fin 2) :
    Set.range (productChart (k := k) i j).base =
      (pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base ⁻¹'
          (chartOpen k i : Set (projectiveSpace k 1)) ∩
        (pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base ⁻¹'
          (chartOpen k j : Set (projectiveSpace k 1)) := by
  change (((productChartIso (k := k) i j).hom ≫
    pullback.map _ _ _ _ (polynomialChartMap k i) (polynomialChartMap k j) (𝟙 _)
      (Category.comp_id _) (Category.comp_id _)).opensRange :
        Set (projectiveProduct k)) = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  change Set.range
    (pullback.map _ _ _ _ (polynomialChartMap k i) (polynomialChartMap k j) (𝟙 _)
      (Category.comp_id _) (Category.comp_id _)).base = _
  rw [Scheme.Pullback.range_map]
  change (pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base ⁻¹'
      ((polynomialChartMap k i).opensRange : Set (projectiveSpace k 1)) ∩
    (pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base ⁻¹'
      ((polynomialChartMap k j).opensRange : Set (projectiveSpace k 1)) = _
  rw [polynomialChartMap_opensRange, polynomialChartMap_opensRange]

private theorem lineChart_nonempty (i : Fin 2) :
    (chartOpen k i : Set (projectiveSpace k 1)).Nonempty := by
  rw [← polynomialChartMap_opensRange]
  exact ⟨(polynomialChartMap k i).base (Nonempty.some inferInstance),
    ⟨Nonempty.some inferInstance, rfl⟩⟩

/-- Any pair of the four actual chart ranges has a common point. -/
theorem productChart_ranges_inter_nonempty (i j i' j' : Fin 2) :
    (Set.range (productChart (k := k) i j).base ∩
      Set.range (productChart (k := k) i' j').base).Nonempty := by
  letI : IrreducibleSpace (projectiveSpace k 1) := projectiveSpace_irreducibleSpace k 1
  obtain ⟨x, hxi, hxi'⟩ := nonempty_preirreducible_inter
    (chartOpen k i).isOpen (chartOpen k i').isOpen (lineChart_nonempty i) (lineChart_nonempty i')
  obtain ⟨y, hyj, hyj'⟩ := nonempty_preirreducible_inter
    (chartOpen k j).isOpen (chartOpen k j').isOpen (lineChart_nonempty j) (lineChart_nonempty j')
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := projectiveSpaceToSpec k 1) (g := projectiveSpaceToSpec k 1) x y (Subsingleton.elim _ _)
  refine ⟨z, ?_, ?_⟩
  · rw [productChart_range]
    simpa only [Set.mem_inter_iff, Set.mem_preimage, hz₁, hz₂] using And.intro hxi hyj
  · rw [productChart_range]
    simpa only [Set.mem_inter_iff, Set.mem_preimage, hz₁, hz₂] using And.intro hxi' hyj'

/-- The polynomial-domain chart has an irreducible image in the original product. -/
theorem productChart_range_isIrreducible (i j : Fin 2) :
    IsIrreducible (Set.range (productChart (k := k) i j).base) := by
  have h := (IrreducibleSpace.isIrreducible_univ (Spec (CommRingCat.of (planeRing k)))).image
    (productChart (k := k) i j).base (productChart (k := k) i j).continuous.continuousOn
  simpa only [Set.image_univ] using h

/-- The covered product is irreducible, using the actual chart intersections. -/
theorem projectiveProduct_irreducibleSpace : IrreducibleSpace (projectiveProduct k) := by
  apply (irreducibleSpace_def (projectiveProduct k)).mpr
  refine ⟨⟨(productChart 0 0).base (Nonempty.some inferInstance), trivial⟩, ?_⟩
  intro U V hU hV hUn hVn
  obtain ⟨x, _, hxU⟩ := hUn
  obtain ⟨y, _, hyV⟩ := hVn
  obtain ⟨i, j, hxij⟩ := productCharts_cover x
  obtain ⟨i', j', hyij⟩ := productCharts_cover y
  obtain ⟨z, hzij, hzij'⟩ := productChart_ranges_inter_nonempty (k := k) i j i' j'
  obtain ⟨t, _, htU, htij'⟩ := (productChart_range_isIrreducible (k := k) i j).2
    U (Set.range (productChart i' j').base) hU (productChart i' j').opensRange.isOpen
      ⟨x, hxij, hxU⟩ ⟨z, hzij, hzij'⟩
  obtain ⟨w, _, hwU, hwV⟩ := (productChart_range_isIrreducible (k := k) i' j').2
    U V hU hV ⟨t, htij', htU⟩ ⟨y, hyij, hyV⟩
  exact ⟨w, trivial, hwU, hwV⟩

/-- Original open-immersion stalk isomorphisms transfer reducedness from the charts. -/
theorem projectiveProduct_isReduced : IsReduced (projectiveProduct k) := by
  haveI (x : projectiveProduct k) : _root_.IsReduced ((projectiveProduct k).presheaf.stalk x) := by
    obtain ⟨i, j, z, hz⟩ := productCharts_cover x
    subst x
    exact isReduced_of_injective ((productChart i j).stalkMap z).hom
      (asIso ((productChart i j).stalkMap z)).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk (projectiveProduct k)

/-- The original projective product is integral over every field. -/
theorem projectiveProduct_isIntegral : IsIntegral (projectiveProduct k) := by
  letI := projectiveProduct_irreducibleSpace (k := k)
  letI := projectiveProduct_isReduced (k := k)
  exact isIntegral_of_irreducibleSpace_of_isReduced (projectiveProduct k)

end KltDP.Examples.FrobeniusGraphPicardClassIntegral

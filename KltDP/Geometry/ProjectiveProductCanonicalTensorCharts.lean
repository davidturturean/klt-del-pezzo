import KltDP.Geometry.AffineProductKaehlerProjectionMaps
import KltDP.Examples.FrobeniusGraphPicardClassCharts

/-!
# Tensor coordinates on the original projective product

This is a coordinate copy of the existing four-chart cover of the original
scheme fiber product. The chart source is the tensor product of the two
original polynomial coordinate rings, so its projections are literally the
ones used by the affine product differential comparison. Joint surjectivity
and open immersion are transported from the existing cover by actual
scheme isomorphisms.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace KltDP.Geometry.ProjectiveProductCanonicalTensorCharts

open ProjectiveLineComparison
open KltDP.Examples.FrobeniusProjectivePoints
open KltDP.Examples.FrobeniusGraphPicardClassCharts

variable (k : Type u) [Field k]

/-- The original tensor product of the two affine-line coordinate rings. -/
abbrev chartRing := Polynomial k ⊗[k] Polynomial k

/-- The affine-product theorem followed by the proved projective-chart
structure-map equalities. -/
def chartIso (i j : Fin 2) :
    Spec (CommRingCat.of (chartRing k)) ≅
      pullback (polynomialChartMap k i ≫ projectiveSpaceToSpec k 1)
        (polynomialChartMap k j ≫ projectiveSpaceToSpec k 1) :=
  (pullbackSpecIso k (Polynomial k) (Polynomial k)).symm ≪≫
    pullback.congrHom (polynomialChartMap_structureMap k i).symm
      (polynomialChartMap_structureMap k j).symm

/-- The original product chart, expressed in tensor coordinates. -/
def chart (i j : Fin 2) :
    Spec (CommRingCat.of (chartRing k)) ⟶ projectiveProduct k :=
  (chartIso k i j).hom ≫
    pullback.map _ _ _ _ (polynomialChartMap k i) (polynomialChartMap k j) (𝟙 _)
      (Category.comp_id _) (Category.comp_id _)

instance chart_isOpenImmersion (i j : Fin 2) :
    IsOpenImmersion (chart k i j) := by
  unfold chart
  infer_instance

/-- The same four original covering maps, with their sources transported
through the actual affine-product isomorphisms. -/
def cover : Scheme.OpenCover.{0} (projectiveProduct k) :=
  (originalProductCover (k := k)).copy (Fin 2 × Fin 2)
    (fun _ => Spec (CommRingCat.of (chartRing k)))
    (fun ij => chart k ij.1 ij.2)
    (Equiv.prodCongr Equiv.ulift.symm Equiv.ulift.symm)
    (fun ij => chartIso k ij.1 ij.2) (fun _ => rfl)

/-- Every point of the original product belongs to an original tensor chart. -/
theorem charts_cover (x : projectiveProduct k) :
    ∃ i j : Fin 2, x ∈ Set.range (chart k i j).base := by
  obtain ⟨z, hz⟩ := (cover k).covers x
  exact ⟨((cover k).f x).1, ((cover k).f x).2, z, hz⟩

private theorem chartIso_fst (i j : Fin 2) :
    (chartIso k i j).hom ≫
      pullback.fst (polynomialChartMap k i ≫ projectiveSpaceToSpec k 1)
        (polynomialChartMap k j ≫ projectiveSpaceToSpec k 1) =
      AffineProductKaehler.firstProjection k (Polynomial k) (Polynomial k) := by
  simp only [chartIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.map, pullback.lift_fst, Category.comp_id]
  exact pullbackSpecIso_inv_fst k (Polynomial k) (Polynomial k)

private theorem chartIso_snd (i j : Fin 2) :
    (chartIso k i j).hom ≫
      pullback.snd (polynomialChartMap k i ≫ projectiveSpaceToSpec k 1)
        (polynomialChartMap k j ≫ projectiveSpaceToSpec k 1) =
      AffineProductKaehler.secondProjection k (Polynomial k) (Polynomial k) := by
  simp only [chartIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id]
  exact pullbackSpecIso_inv_snd k (Polynomial k) (Polynomial k)

/-- The first original projection restricts to the first tensor projection. -/
@[reassoc]
theorem chart_fst (i j : Fin 2) :
    chart k i j ≫
      pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) =
      AffineProductKaehler.firstProjection k (Polynomial k) (Polynomial k) ≫
        polynomialChartMap k i := by
  rw [chart, Category.assoc]
  change (chartIso k i j).hom ≫
    (pullback.map _ _ _ _ (polynomialChartMap k i) (polynomialChartMap k j) (𝟙 _)
      (Category.comp_id _) (Category.comp_id _) ≫ pullback.fst _ _) = _
  rw [pullback.map, pullback.lift_fst, ← Category.assoc, chartIso_fst]

/-- The second original projection restricts to the second tensor projection. -/
@[reassoc]
theorem chart_snd (i j : Fin 2) :
    chart k i j ≫
      pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) =
      AffineProductKaehler.secondProjection k (Polynomial k) (Polynomial k) ≫
        polynomialChartMap k j := by
  rw [chart, Category.assoc]
  change (chartIso k i j).hom ≫
    (pullback.map _ _ _ _ (polynomialChartMap k i) (polynomialChartMap k j) (𝟙 _)
      (Category.comp_id _) (Category.comp_id _) ≫ pullback.snd _ _) = _
  rw [pullback.map, pullback.lift_snd, ← Category.assoc, chartIso_snd]

/-- The tensor chart has the original coefficient-field structure map. -/
@[reassoc]
theorem chart_structure (i j : Fin 2) :
    chart k i j ≫ projectiveProductToSpec =
      Spec.map (CommRingCat.ofHom (algebraMap k (chartRing k))) := by
  rw [projectiveProductToSpec, ← Category.assoc, chart_fst,
    Category.assoc, polynomialChartMap_structureMap]
  exact AffineProductKaehler.firstProjection_comp k (Polynomial k) (Polynomial k)

end KltDP.Geometry.ProjectiveProductCanonicalTensorCharts

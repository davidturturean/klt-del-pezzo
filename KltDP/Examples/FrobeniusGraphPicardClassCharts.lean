import KltDP.Examples.FrobeniusProductPlaneChart

/-!
# Four polynomial charts on the original projective product

The existing polynomial charts of P¹ give a four-chart cover of the actual
fiber product over k. Each source is the existing polynomial plane, through
its proved tensor-product comparison. The projection identities specify
which reciprocal coordinate each polynomial variable represents.

Reuse: pinned `Scheme.Pullback.openCoverOfLeftRight`, `Scheme.Cover.copy`,
`pullback.congrHom`, and the existing `planeProductIso`. No new product,
covering axiom, or prescribed divisor class is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassCharts

open KltDP.Geometry ProjectiveLineComparison
open FrobeniusProjectivePoints FrobeniusBlowupContact FrobeniusProductPlaneChart

variable {k : Type u} [Field k]

/-- Lift only the finite index universe to the one required by the pinned
scheme pullback-cover construction. All chart objects and maps are unchanged. -/
def originalLineCover : Scheme.OpenCover.{u} (projectiveSpace k 1) where
  J := ULift.{u} (Fin 2)
  obj _ := Spec (CommRingCat.of (Polynomial k))
  map i := polynomialChartMap k i.down
  f x := ⟨(polynomialAffineCover k).f x⟩
  covers x := (polynomialAffineCover k).covers x

/-- The library's actual product cover, before polynomial coordinate transport. -/
def originalProductCover : Scheme.OpenCover.{u} (projectiveProduct k) :=
  Scheme.Pullback.openCoverOfLeftRight (originalLineCover (k := k))
    (originalLineCover (k := k)) (projectiveSpaceToSpec k 1)
    (projectiveSpaceToSpec k 1)

/-- Both chart structure maps are the previously specified map to Spec k. -/
def productChartIso (i j : Fin 2) :
    Spec (CommRingCat.of (planeRing k)) ≅
      pullback (polynomialChartMap k i ≫ projectiveSpaceToSpec k 1)
        (polynomialChartMap k j ≫ projectiveSpaceToSpec k 1) :=
  planeProductIso ≪≫ pullback.congrHom
    (polynomialChartMap_structureMap k i).symm
    (polynomialChartMap_structureMap k j).symm

/-- The actual polynomial chart with denominators X_i and Y_j. -/
def productChart (i j : Fin 2) :
    Spec (CommRingCat.of (planeRing k)) ⟶ projectiveProduct k :=
  (productChartIso i j).hom ≫
    pullback.map _ _ _ _ (polynomialChartMap k i) (polynomialChartMap k j) (𝟙 _)
      (Category.comp_id _) (Category.comp_id _)

instance productChart_isOpenImmersion (i j : Fin 2) :
    IsOpenImmersion (productChart (k := k) i j) := by
  unfold productChart
  infer_instance

/-- Coordinate transport retains the library-proved joint surjectivity. -/
def productCover : Scheme.OpenCover.{0} (projectiveProduct k) :=
  (originalProductCover (k := k)).copy (Fin 2 × Fin 2)
    (fun _ => Spec (CommRingCat.of (planeRing k)))
    (fun ij => productChart ij.1 ij.2) (Equiv.prodCongr Equiv.ulift.symm Equiv.ulift.symm)
    (fun ij => productChartIso ij.1 ij.2) (fun _ => rfl)

/-- Every point of the original product lies in one of these four planes. -/
theorem productCharts_cover (x : projectiveProduct k) :
    ∃ i j : Fin 2, x ∈ Set.range (productChart (k := k) i j).base := by
  obtain ⟨z, hz⟩ := (productCover (k := k)).covers x
  exact ⟨((productCover (k := k)).f x).1, ((productCover (k := k)).f x).2, z, hz⟩

private theorem productChartIso_fst (i j : Fin 2) :
    (productChartIso (k := k) i j).hom ≫
      pullback.fst (polynomialChartMap k i ≫ projectiveSpaceToSpec k 1)
        (polynomialChartMap k j ≫ projectiveSpaceToSpec k 1) =
      Spec.map (CommRingCat.ofHom firstCoordinateMap) := by
  simp only [productChartIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.map, pullback.lift_fst,
    Category.comp_id]
  exact planeProductIso_hom_fst (k := k)

private theorem productChartIso_snd (i j : Fin 2) :
    (productChartIso (k := k) i j).hom ≫
      pullback.snd (polynomialChartMap k i ≫ projectiveSpaceToSpec k 1)
        (polynomialChartMap k j ≫ projectiveSpaceToSpec k 1) =
      Spec.map (CommRingCat.ofHom secondCoordinateMap) := by
  simp only [productChartIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.map, pullback.lift_snd,
    Category.comp_id]
  exact planeProductIso_hom_snd (k := k)

/-- The first coordinate is the first polynomial variable on chart i. -/
@[reassoc]
theorem productChart_fst (i j : Fin 2) :
    productChart (k := k) i j ≫
      pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) =
      Spec.map (CommRingCat.ofHom firstCoordinateMap) ≫ polynomialChartMap k i := by
  rw [productChart, Category.assoc]
  change (productChartIso i j).hom ≫
    (pullback.map _ _ _ _ (polynomialChartMap k i) (polynomialChartMap k j) (𝟙 _)
      (Category.comp_id _) (Category.comp_id _) ≫ pullback.fst _ _) = _
  rw [pullback.map, pullback.lift_fst, ← Category.assoc, productChartIso_fst]

/-- The second coordinate is the second polynomial variable on chart j. -/
@[reassoc]
theorem productChart_snd (i j : Fin 2) :
    productChart (k := k) i j ≫
      pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) =
      Spec.map (CommRingCat.ofHom secondCoordinateMap) ≫ polynomialChartMap k j := by
  rw [productChart, Category.assoc]
  change (productChartIso i j).hom ≫
    (pullback.map _ _ _ _ (polynomialChartMap k i) (polynomialChartMap k j) (𝟙 _)
      (Category.comp_id _) (Category.comp_id _) ≫ pullback.snd _ _) = _
  rw [pullback.map, pullback.lift_snd, ← Category.assoc, productChartIso_snd]

/-- The (0,0) chart is literally the previously constructed affine plane map. -/
theorem productChart_zero_zero : productChart (k := k) 0 0 = planeChart := by
  apply pullback.hom_ext
  · rw [productChart_fst, planeChart_fst]
  · rw [productChart_snd, planeChart_snd]

end KltDP.Examples.FrobeniusGraphPicardClassCharts

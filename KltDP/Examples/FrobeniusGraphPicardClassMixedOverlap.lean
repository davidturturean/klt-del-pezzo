import KltDP.Examples.FrobeniusGraphPicardClassMixedCover
import KltDP.Examples.FrobeniusGraphPicardClassIntegral

/-!
# The actual mixed-to-diagonal overlap is the outer-coordinate basic open

The pinned Proj prime-membership theorem identifies the opposite standard
open on each original polynomial chart with D(X). The original product
projection identities then identify the mixed-to-diagonal overlap with
D(v). Thus every point of the original graph in a mixed plane belongs to
this explicit basic open. No replacement graph scheme is introduced.

The short Proj normalization proof follows the existing actual-chart
calculation in AffineBlowupLiftUniqueness; its private name is not imported.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassMixedOverlap

open KltDP.Geometry ProjectiveLineComparison
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusGraphClosed
open FrobeniusBlowupContact FrobeniusProductPlaneChart
open FrobeniusGraphPicardClassCharts FrobeniusGraphPicardClassPowerCharts
open FrobeniusGraphPicardClassIntegral FrobeniusGraphPicardClassMixedCover

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

private def homogeneousChartIso (i : Fin 2) :
    (chartOpen k i).toScheme ≅ Spec (CommRingCat.of (chartRing k i)) :=
  Proj.basicOpenIsoSpec (grading k) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X k i) (by decide)

private theorem homogeneousChartIso_hom_toLRSHom (i : Fin 2) :
    (homogeneousChartIso (k := k) i).hom.toLRSHom =
      ProjectiveSpectrum.Proj.toSpec (grading k) (MvPolynomial.X i) := by
  change (Proj.basicOpenToSpec (grading k) (MvPolynomial.X i)).toLRSHom = _
  refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
  dsimp [Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
  simp only [eqToHom_op, Category.assoc, ← Spec.map_comp]
  rfl

private theorem coordinate_mem_prime_iff (i j : Fin 2) (q : PrimeSpectrum (chartRing k i)) :
    coordinate k i j ∈ q.asIdeal ↔
      MvPolynomial.X j ∈ ((chartImmersion k i).base q).asHomogeneousIdeal := by
  let x := (homogeneousChartIso (k := k) i).inv.base q
  have he : (homogeneousChartIso (k := k) i).hom.base x = q := by
    have h := congrArg (fun f : Spec (CommRingCat.of (chartRing k i)) ⟶
      Spec (CommRingCat.of (chartRing k i)) => f.base q)
      (homogeneousChartIso (k := k) i).inv_hom_id
    simpa only [Scheme.comp_base_apply] using h
  have h : coordinate k i j ∈
      ((ProjectiveSpectrum.Proj.toSpec (grading k) (MvPolynomial.X i)).base x).asIdeal ↔
        MvPolynomial.X j ∈ x.val.asHomogeneousIdeal := by
    unfold coordinate HomogeneousLocalization.Away.mk
    exact ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply (grading k) x _
  rw [← homogeneousChartIso_hom_toLRSHom i] at h
  change coordinate k i j ∈ ((homogeneousChartIso (k := k) i).hom.base x).asIdeal ↔
    MvPolynomial.X j ∈ x.val.asHomogeneousIdeal at h
  rw [he] at h
  exact h

theorem homogeneousChart_mem_other_iff (i j : Fin 2) (q : PrimeSpectrum (chartRing k i)) :
    (chartImmersion k i).base q ∈ chartOpen k j ↔ coordinate k i j ∉ q.asIdeal :=
  (coordinate_mem_prime_iff i j q).not.symm

/-- Opposite-chart membership is the original polynomial coordinate's nonvanishing. -/
theorem polynomialChart_mem_other_iff (i : Fin 2) (q : PrimeSpectrum (Polynomial k)) :
    (polynomialChartMap k i).base q ∈ chartOpen k (otherIndex i) ↔
      Polynomial.X ∉ q.asIdeal := by
  change (chartImmersion k i).base ((chartPolynomialIso k i).inv.base q) ∈
    chartOpen k (otherIndex i) ↔ _
  rw [homogeneousChart_mem_other_iff]
  change chartPolynomialEquiv k i (coordinate k i (otherIndex i)) ∉ q.asIdeal ↔ _
  rw [chartPolynomialEquiv_otherCoordinate]

theorem polynomialChart_preimage_other (i : Fin 2) :
    polynomialChartMap k i ⁻¹ᵁ chartOpen k (otherIndex i) =
      PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) := by
  ext q
  exact polynomialChart_mem_other_iff i q

/-- On either original mixed plane, the matching diagonal is exactly D(v). -/
theorem mixedChart_preimage_diagonal (i : Fin 2) :
    productChart (k := k) i (otherIndex i) ⁻¹ᵁ (productChart i i).opensRange =
      PrimeSpectrum.basicOpen (vCoord : planeRing k) := by
  ext z
  have hf : firstProjection.base ((productChart i (otherIndex i)).base z) ∈ chartOpen k i := by
    have he := congrArg (fun f : Spec (CommRingCat.of (planeRing k)) ⟶
      projectiveSpace k 1 => f.base z) (productChart_fst (k := k) i (otherIndex i))
    simp only [Scheme.comp_base_apply] at he
    rw [he, ← polynomialChartMap_opensRange]
    exact ⟨(Spec.map (CommRingCat.ofHom firstCoordinateMap)).base z, rfl⟩
  change (productChart i (otherIndex i)).base z ∈ Set.range (productChart i i).base ↔ _
  rw [productChart_range]
  change (firstProjection.base ((productChart i (otherIndex i)).base z) ∈ chartOpen k i ∧
    secondProjection.base ((productChart i (otherIndex i)).base z) ∈ chartOpen k i) ↔ _
  simp only [hf, true_and]
  have he := congrArg (fun f : Spec (CommRingCat.of (planeRing k)) ⟶
    projectiveSpace k 1 => f.base z) (productChart_snd (k := k) i (otherIndex i))
  simp only [Scheme.comp_base_apply] at he
  rw [he]
  have hi : otherIndex (otherIndex i) = i := Equiv.swap_apply_self 0 1 i
  have hm := polynomialChart_mem_other_iff (k := k) (otherIndex i)
    ((Spec.map (CommRingCat.ofHom secondCoordinateMap)).base z)
  rw [hi] at hm
  change _ ↔ secondCoordinateMap (Polynomial.X : Polynomial k) ∉ z.asIdeal at hm
  rw [secondCoordinateMap_X] at hm
  exact hm

/-- A point of the original graph in either mixed plane has nonzero outer coordinate. -/
theorem graph_in_mixed_outer_nonzero (p : ℕ) (i : Fin 2)
    (z : Spec (CommRingCat.of (planeRing k)))
    (hgraph : (productChart i (otherIndex i)).base z ∈
      Set.range (projectiveGraphMorphism (k := k) p).base) : vCoord ∉ z.asIdeal := by
  have h := graph_range_productChart_same_first p i (otherIndex i)
    ((productChart i (otherIndex i)).base z) hgraph ⟨z, rfl⟩
  change z ∈ productChart i (otherIndex i) ⁻¹ᵁ (productChart i i).opensRange at h
  rw [mixedChart_preimage_diagonal] at h
  exact h

end KltDP.Examples.FrobeniusGraphPicardClassMixedOverlap

import KltDP.Geometry.ProjectiveSegreMorphism
import KltDP.Geometry.ProjectiveSpaceChartRange

/-!
# The range identity for the Segre morphism, and projectivity of `P¹ ×_k P¹`

The product chart `(i, j)` of `projectiveProduct k` is exactly the preimage under the Segre
morphism `σ : P¹ ×_k P¹ ⟶ P³` of the coordinate chart `D(z_{ij})` of `P³`
(`range_productChart_eq_preimage`): a point of a product chart `(a, b)` whose Segre image lies in
`D(z_{ij})` has `u^{[i ≠ a]} v^{[j ≠ b]}` invertible (`coordinateChartMorphism_mem_range_iff` on
`P³`, `specMap_base_mem_basicOpen_iff`), hence its two projections lie in the charts `D(x_i)`,
`D(y_j)` of `P¹` (the same lemma on `P¹`, through the accepted polynomial charts), hence it lies
in the product chart `(i, j)` (pinned `Scheme.Pullback.range_map`).

With the range identity the closed-immersion criterion of `ProjectiveSegreMorphism` applies:
**`segreMorphism k` is a closed immersion** (`isClosedImmersion_segreMorphism`) and
**`projectiveProduct_isProjectiveOverField : IsProjectiveOverField projectiveProductToSpec`**
(the Segre embedding `P¹ ×_k P¹ ↪ P³` over `k`, no hypothesis beyond `k` a field).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.ProjectiveSegreCover

open ProjectiveChart ProjectiveLineComparison
open KltDP.Examples.FrobeniusBlowupContact KltDP.Examples.FrobeniusBlowupSmooth
open KltDP.Examples.FrobeniusProjectivePoints KltDP.Examples.FrobeniusProductPlaneChart
open KltDP.Examples.FrobeniusGraphPicardClassCharts

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

section Line

/-- The accepted chart immersions of `P¹` are the coordinate charts of `projectiveSpace k 1`. -/
theorem chartImmersion_eq_coordinateChartMorphism (i : Fin 2) :
    chartImmersion k i = coordinateChartMorphism k 1 i := rfl

/-- The accepted polynomial identification of the chart `a` of `P¹`, on the chart ring of
`projectiveSpace k 1`. -/
def lineChartEquiv (a : Fin 2) : coordinateChartRing k 1 a ≃+* Polynomial k :=
  chartPolynomialEquiv k a

/-- The accepted polynomial chart of `P¹` through the coordinate chart of `projectiveSpace k 1`. -/
theorem polynomialChartMap_eq (a : Fin 2) :
    polynomialChartMap k a =
      Spec.map (CommRingCat.ofHom (lineChartEquiv k a).toRingHom) ≫
        coordinateChartMorphism k 1 a := rfl

/-- The fraction `x_i/x_a` of `projectiveSpace k 1` is the accepted coordinate. -/
theorem chartFraction_one_eq_coordinate (a i : Fin 2) :
    chartFraction k 1 a i = coordinate k a i :=
  (chartFraction_eq k 1 a i).trans rfl

/-- For `a ≠ i` the coordinate `x_i/x_a` is the polynomial variable of the chart `a`. -/
theorem chartPolynomialEquiv_coordinate_of_ne (a i : Fin 2) (h : a ≠ i) :
    (chartPolynomialEquiv k a).toRingHom (coordinate k a i) = Polynomial.X := by
  fin_cases a <;> fin_cases i
  · exact absurd rfl h
  · exact chartPolynomialEquiv_zero_coordinate' k
  · exact chartPolynomialEquiv_one_coordinate' k
  · exact absurd rfl h

theorem lineChartEquiv_chartFraction_of_ne (a i : Fin 2) (h : a ≠ i) :
    (lineChartEquiv k a).toRingHom (chartFraction k 1 a i) = Polynomial.X :=
  (congrArg (lineChartEquiv k a).toRingHom (chartFraction_one_eq_coordinate k a i)).trans
    (chartPolynomialEquiv_coordinate_of_ne k a i h)

/-- A point of the polynomial chart `a` of `P¹` lies in the other chart `i ≠ a` iff its
coordinate is invertible there. -/
theorem polynomialChartMap_mem_range_iff (a i : Fin 2) (h : a ≠ i)
    (y : Spec (CommRingCat.of (Polynomial k))) :
    (polynomialChartMap k a).base y ∈ Set.range (polynomialChartMap k i).base ↔
      y ∈ PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) := by
  have h2 : Set.range (polynomialChartMap k i).base =
      Set.range (coordinateChartMorphism k 1 i).base :=
    range_comp_base_of_isIso (chartPolynomialIso k i).inv (chartImmersion k i)
  rw [h2, polynomialChartMap_eq k a, Scheme.comp_base_apply, coordinateChartMorphism_mem_range_iff,
    specMap_base_mem_basicOpen_iff, lineChartEquiv_chartFraction_of_ne k a i h]

end Line

section Product

/-- Membership in the range of a product chart: both projections lie in the factor charts. -/
theorem mem_range_productChart_iff (i j : Fin 2) (x : projectiveProduct k) :
    x ∈ Set.range (productChart (k := k) i j).base ↔
      (pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base x ∈
          Set.range (polynomialChartMap k i).base ∧
        (pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base x ∈
          Set.range (polynomialChartMap k j).base := by
  rw [productChart, range_comp_base_of_isIso, Scheme.Pullback.range_map]
  exact Iff.rfl

/-- The Segre chart ring map sends the fraction `z/z_{ab}` to the image of `z`. -/
theorem segreChartHom_chartFraction (a b : Fin 2) (z : Fin (3 + 1)) :
    segreChartHom k a b (chartFraction k 3 (segreIndex (a, b)) z) = segreImage k a b z := by
  rw [chartFraction_eq, segreChartHom_mk, segrePolynomialHom_X]

/-- A point of the product chart `(a, b)` whose Segre image lies in `D(z_{ij})` lies in the
product chart `(i, j)`. -/
theorem mem_range_productChart_of_segre (a b i j : Fin 2)
    (y : Spec (CommRingCat.of (planeRing k)))
    (hy : (segreMorphism k).base ((productChart (k := k) a b).base y) ∈
      Set.range (coordinateChartMorphism k 3 (segreIndex (i, j))).base) :
    (productChart (k := k) a b).base y ∈ Set.range (productChart (k := k) i j).base := by
  have h1 : y ∈ PrimeSpectrum.basicOpen (segreImage k a b (segreIndex (i, j))) := by
    rw [← Scheme.comp_base_apply, productChart_segreMorphism k a b, segreChart,
      Scheme.comp_base_apply, coordinateChartMorphism_mem_range_iff, segreChartSpec,
      specMap_base_mem_basicOpen_iff, segreChartHom_chartFraction] at hy
    exact hy
  have hu : i ≠ a → y ∈ PrimeSpectrum.basicOpen (uCoord : planeRing k) := by
    intro h
    rw [segreImage_index, if_neg h] at h1
    exact SetLike.le_def.mp (PrimeSpectrum.basicOpen_mul_le_left _ _) h1
  have hv : j ≠ b → y ∈ PrimeSpectrum.basicOpen (vCoord : planeRing k) := by
    intro h
    rw [segreImage_index, if_neg h] at h1
    exact SetLike.le_def.mp (PrimeSpectrum.basicOpen_mul_le_right _ _) h1
  rw [mem_range_productChart_iff]
  constructor
  · rw [← Scheme.comp_base_apply, productChart_fst, Scheme.comp_base_apply]
    by_cases hai : a = i
    · subst hai
      exact ⟨_, rfl⟩
    · rw [polynomialChartMap_mem_range_iff k a i hai, specMap_base_mem_basicOpen_iff,
        firstCoordinateMap_X]
      exact hu (Ne.symm hai)
  · rw [← Scheme.comp_base_apply, productChart_snd, Scheme.comp_base_apply]
    by_cases hbj : b = j
    · subst hbj
      exact ⟨_, rfl⟩
    · rw [polynomialChartMap_mem_range_iff k b j hbj, specMap_base_mem_basicOpen_iff,
        secondCoordinateMap_X]
      exact hv (Ne.symm hbj)

/-- **The range identity**: the product chart `(i, j)` is the preimage under the Segre morphism
of the chart `D(z_{ij})` of `P³`. -/
theorem range_productChart_eq_preimage (i j : Fin 2) :
    Set.range (productChart (k := k) i j).base =
      (segreMorphism k).base ⁻¹'
        Set.range (coordinateChartMorphism k 3 (segreIndex (i, j))).base := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [Set.mem_preimage, ← Scheme.comp_base_apply, productChart_segreMorphism k i j, segreChart,
      Scheme.comp_base_apply]
    exact ⟨_, rfl⟩
  · intro hx
    obtain ⟨a, b, y, rfl⟩ := productCharts_cover (k := k) x
    exact mem_range_productChart_of_segre k a b i j y hx

end Product

/-- **The Segre morphism `P¹ ×_k P¹ ⟶ P³` is a closed immersion.** -/
instance isClosedImmersion_segreMorphism : IsClosedImmersion (segreMorphism k) :=
  segreMorphism_isClosedImmersion k (range_productChart_eq_preimage k)

/-- **`P¹ ×_k P¹` is projective over `k`** (accepted `IsProjectiveOverField`: a closed immersion
into `projectiveSpace k 3` over `k`). -/
theorem projectiveProduct_isProjectiveOverField :
    IsProjectiveOverField (projectiveProductToSpec (k := k)) :=
  projectiveProduct_isProjectiveOverField_of_range k (range_productChart_eq_preimage k)

end KltDP.Geometry.ProjectiveSegreCover

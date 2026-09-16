import KltDP.Geometry.ProjectiveLineComparison
import KltDP.Geometry.SpecHomRingHom

/-!
# The affine coordinate of `P¹` on a scheme mapping into two charts

For a scheme `W` with two morphisms `g₀ g₁ : W ⟶ Spec k[X]` such that `g₀` followed by the accepted
polynomial chart `D(x_i)` equals `g₁` followed by the chart `D(x_{i'})`, the pulled-back coordinate
functions `X ∘ g₀`, `X ∘ g₁ ∈ Γ(W, ⊤)` are equal when `i = i'` (the chart is a monomorphism) and are
mutually inverse when `i ≠ i'` (`chart_function_relation`): the pair factors through the accepted
overlap `Spec (overlapRing k)` (`overlapPullbackIso`), where the two restricted coordinates multiply
to one (`overlap_coordinates_mul`). This is the transition rule `u ↦ u⁻¹` of `P¹`, expressed on
functions of an arbitrary `W`, as used for the overlaps of the product charts of `P¹ ×_k P¹`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.ProjectiveLineComparison

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] {W : Scheme.{u}}

theorem chartPolynomialIso_inv (i : Fin 2) :
    (chartPolynomialIso k i).inv =
      Spec.map (CommRingCat.ofHom (chartPolynomialEquiv k i).toRingHom) := rfl

theorem chartPolynomialEquiv_zero_coordinate :
    chartPolynomialEquiv k 0 (coordinate k 0 1) = Polynomial.X :=
  firstChartPolynomialEquiv_coordinate k

theorem chartPolynomialEquiv_one_coordinate :
    chartPolynomialEquiv k 1 (coordinate k 1 0) = Polynomial.X :=
  secondChartPolynomialEquiv_coordinate k

theorem chartPolynomialEquiv_zero_coordinate' :
    (chartPolynomialEquiv k 0).toRingHom (coordinate k 0 1) = Polynomial.X :=
  firstChartPolynomialEquiv_coordinate k

theorem chartPolynomialEquiv_one_coordinate' :
    (chartPolynomialEquiv k 1).toRingHom (coordinate k 1 0) = Polynomial.X :=
  secondChartPolynomialEquiv_coordinate k

/-- The coordinate functions of a scheme mapping into both charts are mutually inverse. -/
theorem overlap_function_mul (g₀ g₁ : W ⟶ Spec (CommRingCat.of (Polynomial k)))
    (h : g₀ ≫ polynomialChartMap k 0 = g₁ ≫ polynomialChartMap k 1) :
    (specHomRingHom g₀).hom Polynomial.X * (specHomRingHom g₁).hom Polynomial.X = 1 := by
  have h' : (g₀ ≫ (chartPolynomialIso k 0).inv) ≫ chartImmersion k 0 =
      (g₁ ≫ (chartPolynomialIso k 1).inv) ≫ chartImmersion k 1 := by
    simpa only [polynomialChartMap, Category.assoc] using h
  let θ : W ⟶ Spec (CommRingCat.of (overlapRing k)) :=
    pullback.lift _ _ h' ≫ (overlapPullbackIso k).hom
  have hθ₀ : θ ≫ Spec.map (CommRingCat.ofHom (toOverlapLeft k)) =
      g₀ ≫ Spec.map (CommRingCat.ofHom (chartPolynomialEquiv k 0).toRingHom) := by
    rw [← chartPolynomialIso_inv]
    simp only [θ, Category.assoc, overlapPullbackIso_hom_left, pullback.lift_fst]
  have hθ₁ : θ ≫ Spec.map (CommRingCat.ofHom (toOverlapRight k)) =
      g₁ ≫ Spec.map (CommRingCat.ofHom (chartPolynomialEquiv k 1).toRingHom) := by
    rw [← chartPolynomialIso_inv]
    simp only [θ, Category.assoc, overlapPullbackIso_hom_right, pullback.lift_snd]
  have e₀ := specHomRingHom_congr hθ₀
  have e₁ := specHomRingHom_congr hθ₁
  have v₀ := congrArg (fun φ : CommRingCat.of (chartRing k 0) ⟶ Γ(W, ⊤) =>
    φ.hom (coordinate k 0 1)) e₀
  have v₁ := congrArg (fun φ : CommRingCat.of (chartRing k 1) ⟶ Γ(W, ⊤) =>
    φ.hom (coordinate k 1 0)) e₁
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at v₀ v₁
  rw [chartPolynomialEquiv_zero_coordinate'] at v₀
  rw [chartPolynomialEquiv_one_coordinate'] at v₁
  rw [← v₀, ← v₁, ← map_mul, overlap_coordinates_mul, map_one]

/-- The relation between the coordinate functions of two chart factorizations: equal for the same
chart, mutually inverse for different charts. -/
theorem chart_function_relation (g₀ g₁ : W ⟶ Spec (CommRingCat.of (Polynomial k))) (i i' : Fin 2)
    (h : g₀ ≫ polynomialChartMap k i = g₁ ≫ polynomialChartMap k i') :
    (i = i' → (specHomRingHom g₀).hom Polynomial.X = (specHomRingHom g₁).hom Polynomial.X) ∧
      (i ≠ i' → (specHomRingHom g₀).hom Polynomial.X *
        (specHomRingHom g₁).hom Polynomial.X = 1) := by
  fin_cases i <;> fin_cases i'
  · refine ⟨fun _ => ?_, fun hne => absurd rfl hne⟩
    rw [(cancel_mono (polynomialChartMap k 0)).mp h]
  · exact ⟨fun h01 => absurd h01 (by decide), fun _ => overlap_function_mul k g₀ g₁ h⟩
  · refine ⟨fun h10 => absurd h10 (by decide), fun _ => ?_⟩
    rw [mul_comm]
    exact overlap_function_mul k g₁ g₀ h.symm
  · refine ⟨fun _ => ?_, fun hne => absurd rfl hne⟩
    rw [(cancel_mono (polynomialChartMap k 1)).mp h]

end KltDP.Geometry.ProjectiveLineComparison

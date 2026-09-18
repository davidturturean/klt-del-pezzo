import KltDP.Geometry.ProjectiveImageHomogeneousFractions
import KltDP.Geometry.HomogeneousCommonDenominator

/-!
# A common positive homogeneous denominator for actual birational coordinates

Every finite family in the original source function field is represented
by homogeneous polynomials of one positive degree, divided by one actual
nonzero homogeneous polynomial. The coordinates are pulled along the
original composite morphism; its coefficient map is the original scalar
map by `fieldConstants_eq_originalScalar`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v

namespace KltDP.Geometry.ProjectiveImageChartFieldGeneration

open ProjectiveChart ProjectiveCoordinateSectionBasicOpen

variable {k : Type u} [Field k] {n : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [IsIntegral Y]
  (e : Y ⟶ projectiveSpace k n) (j : Fin (n + 1))
  [IsClosedImmersion e] [Nonempty (e ⁻¹ᵁ standardOpen k n j)]
  (g : X ⟶ Y) [GenericPointPreserving g] (hg : IsBirationalScheme g)

include hg in
/-- Finite actual rational functions have one common positive homogeneous
degree and one common nonzero denominator in the original coordinates. -/
theorem exists_common_homogeneous_fractions {ι : Type v} [Fintype ι]
    (z : ι → X.functionField) :
    ∃ (d : ℕ) (p : ι → homogeneousRing k n) (q : homogeneousRing k n),
      0 < d ∧ (∀ i, (p i).IsHomogeneous d) ∧ q.IsHomogeneous d ∧
      MvPolynomial.eval₂ (fieldConstants (g ≫ e) j) (fieldCoordinate (g ≫ e) j) q ≠ 0 ∧
      ∀ i, MvPolynomial.eval₂ (fieldConstants (g ≫ e) j) (fieldCoordinate (g ≫ e) j) (p i) /
        MvPolynomial.eval₂ (fieldConstants (g ≫ e) j) (fieldCoordinate (g ≫ e) j) q = z i := by
  classical
  choose d p q hd hp hq hq0 hpq using
    (fun i => exists_homogeneous_quotient_of_birational e j g hg (z i))
  let φ := MvPolynomial.eval₂Hom (fieldConstants (g ≫ e) j) (fieldCoordinate (g ≫ e) j)
  have hj : φ (MvPolynomial.X j) = 1 := by
    simpa only [φ, MvPolynomial.eval₂Hom_X'] using fieldCoordinate_self (g ≫ e) j
  obtain ⟨D, P, Q, hD, hP, hQ, hQ0, hPQ⟩ :=
    HomogeneousCommonDenominator.exists_common φ j hj d p q hp hq hq0
  exact ⟨D, P, Q, hD, hP, hQ, hQ0, fun i => (hPQ i).trans (hpq i)⟩

end KltDP.Geometry.ProjectiveImageChartFieldGeneration

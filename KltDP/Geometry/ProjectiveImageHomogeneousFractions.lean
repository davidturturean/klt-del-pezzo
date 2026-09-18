import KltDP.Geometry.BirationalProjectiveChartFieldGeneration
import KltDP.Geometry.ProjectiveSegreGeneralCharts

/-!
# Positive equal-degree homogeneous fractions in the original function field

The homogeneous-away representation of each actual chart section already
provides a homogeneous numerator. Multiplication by powers of the selected
coordinate makes both degrees equal and positive. Its actual coordinate
fraction is one, so this normalization preserves both field values and
the nonzero denominator. Birational transport uses the original field map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ProjectiveImageChartFieldGeneration

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] MvPolynomial.gradedAlgebra

open ProjectiveChart ProjectiveCoordinateSectionBasicOpen

variable {k : Type u} [Field k] {n : ℕ} {Y : Scheme.{u}}
  (e : Y ⟶ projectiveSpace k n) (j : Fin (n + 1))

/-- The actual image-chart section comes from a homogeneous polynomial
of some degree, using the original homogeneous localization. -/
theorem exists_homogeneous_section [IsClosedImmersion e]
    (s : Γ(Y, e ⁻¹ᵁ standardOpen k n j)) :
    ∃ (d : ℕ) (p : homogeneousRing k n), p.IsHomogeneous d ∧
      MvPolynomial.eval₂ (sectionConstants e j) (sectionCoordinate e j) p = s := by
  obtain ⟨a, ha⟩ := chartSectionMap_surjective e j s
  obtain ⟨d, p, hp, hpa⟩ :=
    HomogeneousLocalization.Away.mk_surjective (grading k n) (coordinate_mem k n j) a
  have hhom : p.IsHomogeneous d := by
    simpa only [smul_eq_mul, mul_one] using
      (MvPolynomial.mem_homogeneousSubmodule _ _).mp hp
  refine ⟨d, p, hhom, ?_⟩
  rw [← hpa, mk_eq_eval_chartFraction, MvPolynomial.eval₂_comp_left] at ha
  exact ha

variable [IsIntegral Y] [Nonempty (e ⁻¹ᵁ standardOpen k n j)]

/-- The selected coordinate fraction is one in the actual function field. -/
theorem fieldCoordinate_self : fieldCoordinate e j j = 1 := by
  change (Y.germToFunctionField (e ⁻¹ᵁ standardOpen k n j)).hom
    (chartSectionMap e j (chartFraction k n j j)) = 1
  rw [ProjectiveSegreGeneral.chartFraction_self, map_one, map_one]

/-- Every actual rational function is a quotient of two homogeneous
polynomials of one positive degree, with actual nonzero denominator. -/
theorem exists_homogeneous_quotient [IsClosedImmersion e] (z : Y.functionField) :
    ∃ (d : ℕ) (p q : homogeneousRing k n), 0 < d ∧
      p.IsHomogeneous d ∧ q.IsHomogeneous d ∧
      MvPolynomial.eval₂ (fieldConstants e j) (fieldCoordinate e j) q ≠ 0 ∧
      MvPolynomial.eval₂ (fieldConstants e j) (fieldCoordinate e j) p /
        MvPolynomial.eval₂ (fieldConstants e j) (fieldCoordinate e j) q = z := by
  letI := functionField_isFractionRing_of_isAffineOpen Y
    (e ⁻¹ᵁ standardOpen k n j)
    ((Proj.isAffineOpen_basicOpen (grading k n) (MvPolynomial.X j)
      (coordinate_mem k n j) Nat.one_pos).preimage e)
  obtain ⟨a, b, hb, hz⟩ :=
    IsFractionRing.div_surjective (A := Γ(Y, e ⁻¹ᵁ standardOpen k n j)) z
  obtain ⟨d, p, hp, hpa⟩ := exists_homogeneous_section e j a
  obtain ⟨r, q, hq, hqb⟩ := exists_homogeneous_section e j b
  have hp' : MvPolynomial.eval₂ (fieldConstants e j) (fieldCoordinate e j) p =
      algebraMap Γ(Y, e ⁻¹ᵁ standardOpen k n j) Y.functionField a := by
    calc
      _ = Y.germToFunctionField (e ⁻¹ᵁ standardOpen k n j)
          (MvPolynomial.eval₂ (sectionConstants e j) (sectionCoordinate e j) p) :=
        (polynomial_germ e j p).symm
      _ = _ := congrArg (Y.germToFunctionField (e ⁻¹ᵁ standardOpen k n j)) hpa
  have hq' : MvPolynomial.eval₂ (fieldConstants e j) (fieldCoordinate e j) q =
      algebraMap Γ(Y, e ⁻¹ᵁ standardOpen k n j) Y.functionField b := by
    calc
      _ = Y.germToFunctionField (e ⁻¹ᵁ standardOpen k n j)
          (MvPolynomial.eval₂ (sectionConstants e j) (sectionCoordinate e j) q) :=
        (polynomial_germ e j q).symm
      _ = _ := congrArg (Y.germToFunctionField (e ⁻¹ᵁ standardOpen k n j)) hqb
  refine ⟨d + r + 1, p * MvPolynomial.X j ^ (r + 1),
    q * MvPolynomial.X j ^ (d + 1), Nat.zero_lt_succ _, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using hp.mul (MvPolynomial.isHomogeneous_X_pow j (r + 1))
  · simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      hq.mul (MvPolynomial.isHomogeneous_X_pow j (d + 1))
  · simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X,
      fieldCoordinate_self, one_pow, mul_one, hq']
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  · simpa only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X,
      fieldCoordinate_self, one_pow, mul_one, hp', hq'] using hz

/-- The original birational function-field map preserves the same
positive homogeneous degree and the actual nonzero denominator. -/
theorem exists_homogeneous_quotient_of_birational [IsClosedImmersion e]
    {X : Scheme.{u}} [IsIntegral X] (g : X ⟶ Y) [GenericPointPreserving g]
    (hg : IsBirationalScheme g) (z : X.functionField) :
    ∃ (d : ℕ) (p q : homogeneousRing k n), 0 < d ∧
      p.IsHomogeneous d ∧ q.IsHomogeneous d ∧
      MvPolynomial.eval₂ (fieldConstants (g ≫ e) j) (fieldCoordinate (g ≫ e) j) q ≠ 0 ∧
      MvPolynomial.eval₂ (fieldConstants (g ≫ e) j) (fieldCoordinate (g ≫ e) j) p /
        MvPolynomial.eval₂ (fieldConstants (g ≫ e) j) (fieldCoordinate (g ≫ e) j) q = z := by
  letI := (BirationalFunctionField.isBirationalScheme_iff_functionFieldMap_isIso g).mp hg
  obtain ⟨w, hw⟩ := (ConcreteCategory.bijective_of_isIso (functionFieldMap g)).2 z
  obtain ⟨d, p, q, hd, hp, hq, hq0, hpq⟩ := exists_homogeneous_quotient e j w
  refine ⟨d, p, q, hd, hp, hq, ?_, ?_⟩
  · rw [← functionFieldMap_polynomial e j g]
    intro hzero
    apply hq0
    exact (functionFieldMap g).hom.injective (by simpa only [map_zero] using hzero)
  · have h := congrArg (functionFieldMap g).hom hpq
    rw [map_div₀, functionFieldMap_polynomial, functionFieldMap_polynomial, hw] at h
    exact h

end KltDP.Geometry.ProjectiveImageChartFieldGeneration

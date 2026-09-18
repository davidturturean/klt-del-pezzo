import KltDP.Geometry.ProjectiveImageChartScalars
import KltDP.Geometry.BirationalFunctionField

/-!
# Actual projective coordinate fractions under a birational map

The original function-field map transports the original chart constants
and coordinates to the germs obtained from the composite scheme map.
Birationality therefore gives polynomial-quotient generation in the
original source function field, over its original structure-map scalars.

`GenericPointPreserving` supplies the existing function-field map; its
field is already contained in `IsBirationalScheme.map_genericPoint`.
No rational-function generation or section-ratio witness is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ProjectiveImageChartFieldGeneration

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open ProjectiveChart ProjectiveCoordinateSectionBasicOpen

variable {k : Type u} [Field k] {n : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [IsIntegral Y]
  (e : Y ⟶ projectiveSpace k n) (j : Fin (n + 1))
  [Nonempty (e ⁻¹ᵁ standardOpen k n j)]
  (g : X ⟶ Y) [GenericPointPreserving g]

/-- Nonemptiness for the literal composite-preimage open is derived
from generic-point preservation and the actual nonempty target chart. -/
instance composite_chart_nonempty :
    Nonempty ((g ≫ e) ⁻¹ᵁ standardOpen k n j) := by
  rw [Scheme.preimage_comp]
  exact preimage_nonempty g (e ⁻¹ᵁ standardOpen k n j)

/-- Actual coordinate coefficients commute with the existing generic
stalk map of the original scheme morphism. -/
theorem functionFieldMap_constants :
    (functionFieldMap g).hom.comp (fieldConstants e j) =
      fieldConstants (g ≫ e) j := by
  ext a
  exact functionFieldMap_germ g (e ⁻¹ᵁ standardOpen k n j)
    (sectionConstants e j a)

/-- The transported coordinate is the actual generic germ of the
coordinate pulled back along the composite scheme morphism. -/
theorem functionFieldMap_coordinate (i : Fin (n + 1)) :
    functionFieldMap g (fieldCoordinate e j i) =
      fieldCoordinate (g ≫ e) j i :=
  functionFieldMap_germ g (e ⁻¹ᵁ standardOpen k n j) (sectionCoordinate e j i)

theorem functionFieldMap_polynomial (p : homogeneousRing k n) :
    (functionFieldMap g).hom
        (MvPolynomial.eval₂ (fieldConstants e j) (fieldCoordinate e j) p) =
      MvPolynomial.eval₂ (fieldConstants (g ≫ e) j) (fieldCoordinate (g ≫ e) j) p := by
  rw [MvPolynomial.eval₂_comp_left, functionFieldMap_constants]
  congr 1
  funext i
  exact functionFieldMap_coordinate e j g i

/-- Birationality transports quotient generation to the original source
function field, with the actual composite map's coordinates. -/
theorem exists_polynomial_quotient_of_birational [IsClosedImmersion e]
    (hg : IsBirationalScheme g) (z : X.functionField) :
    ∃ p q : homogeneousRing k n,
      MvPolynomial.eval₂ (fieldConstants (g ≫ e) j) (fieldCoordinate (g ≫ e) j) q ≠ 0 ∧
      MvPolynomial.eval₂ (fieldConstants (g ≫ e) j) (fieldCoordinate (g ≫ e) j) p /
        MvPolynomial.eval₂ (fieldConstants (g ≫ e) j) (fieldCoordinate (g ≫ e) j) q = z := by
  letI := (BirationalFunctionField.isBirationalScheme_iff_functionFieldMap_isIso g).mp hg
  obtain ⟨w, hw⟩ := (ConcreteCategory.bijective_of_isIso (functionFieldMap g)).2 z
  obtain ⟨p, q, hq, hpq⟩ := exists_polynomial_quotient e j w
  refine ⟨p, q, ?_, ?_⟩
  · rw [← functionFieldMap_polynomial e j g]
    intro hzero
    apply hq
    exact (functionFieldMap g).hom.injective (by simpa only [map_zero] using hzero)
  · have h := congrArg (functionFieldMap g).hom hpq
    rw [map_div₀, functionFieldMap_polynomial, functionFieldMap_polynomial, hw] at h
    exact h

/-- The same conclusion over the original field, through the original
composite structure morphism and its original global-section germ. -/
theorem exists_polynomial_quotient_of_birational_originalScalar [IsClosedImmersion e]
    (hg : IsBirationalScheme g) (z : X.functionField) :
    ∃ p q : homogeneousRing k n,
      MvPolynomial.eval₂
        ((algebraMap Γ(X, ⊤) X.functionField).comp
          (baseFieldToGlobalSections ((g ≫ e) ≫ projectiveSpaceToSpec k n)))
        (fieldCoordinate (g ≫ e) j) q ≠ 0 ∧
      MvPolynomial.eval₂
        ((algebraMap Γ(X, ⊤) X.functionField).comp
          (baseFieldToGlobalSections ((g ≫ e) ≫ projectiveSpaceToSpec k n)))
        (fieldCoordinate (g ≫ e) j) p /
      MvPolynomial.eval₂
        ((algebraMap Γ(X, ⊤) X.functionField).comp
          (baseFieldToGlobalSections ((g ≫ e) ≫ projectiveSpaceToSpec k n)))
        (fieldCoordinate (g ≫ e) j) q = z := by
  simpa only [fieldConstants_eq_originalScalar] using
    exists_polynomial_quotient_of_birational e j g hg z

end KltDP.Geometry.ProjectiveImageChartFieldGeneration

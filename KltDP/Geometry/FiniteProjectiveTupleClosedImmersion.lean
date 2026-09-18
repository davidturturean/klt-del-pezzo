import KltDP.Geometry.ClosedImmersionAffineRestriction
import KltDP.Geometry.FiniteProjectiveTupleChartSurjectivity
import KltDP.Geometry.ProperClosedImmersionLocal
import KltDP.Geometry.ProjectiveProper

/-!
# An actual projective embedding of a finite cover

The derived common-power tuple has surjective original section maps on
standard charts whose preimages are the original finite affine charts.
Its original field triangle proves properness, so those charts suffice
to prove that the tuple morphism is a closed immersion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.FiniteProjectiveTupleClosedImmersion

attribute [local instance] MvPolynomial.gradedAlgebra

open FiniteProjectiveChartGenerators FiniteProjectivePowerGenerators
  FiniteProjectiveSectionTuple InvertibleSheafSectionPowers
  ProjectiveCoordinateSectionBasicOpen

variable {k : Type u} [Field k] {n : ℕ} {Y Z : Scheme.{u}}
  (π : Z ⟶ Y) (i : Y ⟶ projectiveSpace k n)
  [IsFinite π] [IsClosedImmersion i]

variable (q : ℕ) (r : Fin (n + 1) → ℕ)
  (t : ∀ j, Fin (r j) → (power (line π i) q).obj.sections) (hq : 0 < q)

/-- The original tuple map is proper by its actual field triangle. -/
theorem morphism_isProper :
    IsProper (FiniteProjectiveSectionTuple.morphism r π i q t hq) := by
  letI : IsProper (structureMap π i) := by
    dsimp only [structureMap]
    infer_instance
  letI : IsProper (FiniteProjectiveSectionTuple.morphism r π i q t hq ≫
      projectiveSpaceToSpec k (Fintype.card (SectionIndex r))) := by
    rw [FiniteProjectiveSectionTuple.morphism_structure]
    infer_instance
  exact IsProper.of_comp_of_isSeparated
    (FiniteProjectiveSectionTuple.morphism r π i q t hq)
    (projectiveSpaceToSpec k (Fintype.card (SectionIndex r)))

/-- The original tuple morphism is a closed immersion when its selected
original chart apps are surjective. -/
theorem morphism_isClosedImmersion
    (hs : ∀ j, Function.Surjective
      ((FiniteProjectiveSectionTuple.morphism r π i q t hq).app
        (standardOpen k (Fintype.card (SectionIndex r)) (denominatorIndex r j))).hom) :
    IsClosedImmersion (FiniteProjectiveSectionTuple.morphism r π i q t hq) := by
  letI := morphism_isProper π i q r t hq
  apply ProperClosedImmersionLocal.of_preimage_iSup_eq_top
    (FiniteProjectiveSectionTuple.morphism r π i q t hq)
    (fun j => standardOpen k (Fintype.card (SectionIndex r)) (denominatorIndex r j))
  · calc
      (⨆ j, FiniteProjectiveSectionTuple.morphism r π i q t hq ⁻¹ᵁ
          standardOpen k (Fintype.card (SectionIndex r)) (denominatorIndex r j)) =
          ⨆ j, chartOpen π i j :=
        iSup_congr (FiniteProjectiveSectionTuple.morphism_preimage_denominator r π i q t hq)
      _ = (π ≫ i) ⁻¹ᵁ (⨆ j, standardOpen k n j) :=
        ((π ≫ i).preimage_iSup (standardOpen k n)).symm
      _ = ⊤ := by rw [ProjectiveChart.iSup_coordinateStandardOpen]; rfl
  · intro j
    apply ClosedImmersionAffineRestriction.of_app_surjective
    · rw [FiniteProjectiveSectionTuple.morphism_preimage_denominator]
      exact chartOpen_isAffine π i j
    · exact Proj.isAffineOpen_basicOpen (ProjectiveChart.grading k (Fintype.card (SectionIndex r)))
        (MvPolynomial.X (denominatorIndex r j))
        (ProjectiveChart.coordinate_mem k (Fintype.card (SectionIndex r))
          (denominatorIndex r j)) Nat.one_pos
    · exact hs j

/-- Every original finite cover of an original closed projective subscheme
is projective over the same field, witnessed by its actual tuple morphism.
All tuple, cover, and chart-surjectivity data are derived internally. -/
theorem isProjectiveOverField :
    IsProjectiveOverField (π ≫ i ≫ projectiveSpaceToSpec k n) := by
  obtain ⟨q, hq, r, t, hs⟩ :=
    FiniteProjectiveSectionTuple.exists_tuple_with_surjective_chartMaps π i
  exact ⟨Fintype.card (SectionIndex r),
    FiniteProjectiveSectionTuple.morphism r π i q t hq,
    morphism_isClosedImmersion π i q r t hq hs,
    FiniteProjectiveSectionTuple.morphism_structure r π i q t hq⟩

end KltDP.Geometry.FiniteProjectiveTupleClosedImmersion

import KltDP.Geometry.ProjectiveSpaceChartRange
import KltDP.Geometry.ProjectiveLineCanonicalFrame

/-!
# Original coordinate-section basic opens

The ordinary section z_j/z_i on the original projective coordinate chart
D_+(z_i) has intrinsic basic open D_+(z_i) intersect D_+(z_j). The proof
uses the accepted original chart range, localization, and appLE formulas.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ProjectiveCoordinateSectionBasicOpen

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] MvPolynomial.gradedAlgebra

open ProjectiveChart

variable (k : Type u) [Field k] (n : ℕ)

abbrev standardOpen (i : Fin (n + 1)) : (projectiveSpace k n).Opens :=
  Proj.basicOpen (grading k n) (MvPolynomial.X i)

/-- The original homogeneous fraction as an ordinary chart section. -/
def coordinateSection (i j : Fin (n + 1)) :
    Γ(projectiveSpace k n, standardOpen k n i) :=
  (Proj.awayToSection (grading k n) (MvPolynomial.X i)).hom (chartFraction k n i j)

private theorem preimage_basicOpen_coordinateSection (i j : Fin (n + 1)) :
    coordinateChartMorphism k n i ⁻¹ᵁ
        (projectiveSpace k n).basicOpen (coordinateSection k n i j) =
      PrimeSpectrum.basicOpen (chartFraction k n i j) := by
  let f := coordinateChartMorphism k n i
  have hf : (⊤ : (Spec (.of (coordinateChartRing k n i))).Opens) ≤
      f ⁻¹ᵁ standardOpen k n i := by
    intro x _
    change f.base x ∈ Proj.basicOpen (grading k n) (MvPolynomial.X i)
    rw [← coordinateChartMorphism_opensRange k n i]
    exact Set.mem_range_self x
  have happ : f.appLE (standardOpen k n i) ⊤ hf (coordinateSection k n i j) =
      (Scheme.ΓSpecIso (.of (coordinateChartRing k n i))).inv
        (chartFraction k n i j) :=
    ConcreteCategory.congr_hom
      (ProjectiveLineCanonicalFrame.awayToSection_awayι_appLE
        (grading k n) (coordinate_mem k n i) Nat.one_pos hf)
      (chartFraction k n i j)
  have h := Scheme.basicOpen_appLE f ⊤ (standardOpen k n i) hf
    (coordinateSection k n i j)
  rw [happ, basicOpen_eq_of_affine] at h
  exact (inf_eq_right.mpr le_top).symm.trans h.symm

/-- The intrinsic nonvanishing of the original coordinate fraction is
the original intersection of the two projective coordinate charts. -/
theorem basicOpen_coordinateSection (i j : Fin (n + 1)) :
    (projectiveSpace k n).basicOpen (coordinateSection k n i j) =
      standardOpen k n i ⊓ standardOpen k n j := by
  have hpoint (q : Spec (.of (coordinateChartRing k n i))) :
      (coordinateChartMorphism k n i).base q ∈
          (projectiveSpace k n).basicOpen (coordinateSection k n i j) ↔
        (coordinateChartMorphism k n i).base q ∈ standardOpen k n j := by
    change q ∈ coordinateChartMorphism k n i ⁻¹ᵁ
      (projectiveSpace k n).basicOpen (coordinateSection k n i j) ↔ _
    rw [preimage_basicOpen_coordinateSection]
    change q ∈ PrimeSpectrum.basicOpen (chartFraction k n i j) ↔
      (coordinateChartMorphism k n i).base q ∈
        Proj.basicOpen (grading k n) (MvPolynomial.X j)
    rw [← coordinateChartMorphism_opensRange k n j]
    exact (coordinateChartMorphism_mem_range_iff k n i j q).symm
  apply le_antisymm
  · intro x hx
    have hxi := (projectiveSpace k n).basicOpen_le (coordinateSection k n i j) hx
    refine ⟨hxi, ?_⟩
    have hxrange : x ∈ Set.range (coordinateChartMorphism k n i).base := by
      change x ∈ (coordinateChartMorphism k n i).opensRange
      rw [coordinateChartMorphism_opensRange]
      exact hxi
    obtain ⟨q, rfl⟩ := hxrange
    exact (hpoint q).mp hx
  · intro x hx
    have hxrange : x ∈ Set.range (coordinateChartMorphism k n i).base := by
      change x ∈ (coordinateChartMorphism k n i).opensRange
      rw [coordinateChartMorphism_opensRange]
      exact hx.1
    obtain ⟨q, rfl⟩ := hxrange
    exact (hpoint q).mpr hx.2

end KltDP.Geometry.ProjectiveCoordinateSectionBasicOpen

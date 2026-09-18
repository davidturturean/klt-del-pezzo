import KltDP.Geometry.ProjectiveImageChartFieldGeneration
import KltDP.Geometry.LinearSystemCoordinateEvaluation

/-!
# Actual projective coordinate germs on original linear-system charts

Restriction to a nonempty source subopen preserves the original generic
germ. The original linear-system chart formula therefore computes the
field coordinates used by polynomial generation. Every selected nonempty
section open has a nonempty original affine chart with that same index.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.ProjectiveImageChartFieldGeneration

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open ProjectiveChart ProjectiveCoordinateSectionBasicOpen

/-- The original coordinate germ is unchanged on a nonempty original
subopen of its actual inverse-image chart. -/
theorem fieldCoordinate_eq_appLE_germ {k : Type u} [Field k] {n : ℕ}
    {X : Scheme.{u}} [IsIntegral X] (e : X ⟶ projectiveSpace k n) (j : Fin (n + 1))
    [Nonempty (e ⁻¹ᵁ standardOpen k n j)]
    (U : X.Opens) [Nonempty U] (hU : U ≤ e ⁻¹ᵁ standardOpen k n j)
    (i : Fin (n + 1)) :
    fieldCoordinate e j i =
      X.germToFunctionField U
        (e.appLE (standardOpen k n j) U hU (coordinateSection k n j i)) := by
  change X.germToFunctionField (e ⁻¹ᵁ standardOpen k n j)
      (e.app (standardOpen k n j) (coordinateSection k n j i)) =
    X.germToFunctionField U (X.presheaf.map (homOfLE hU).op
      (e.app (standardOpen k n j) (coordinateSection k n j i)))
  exact (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hU)
    (genericPoint X) _ _).symm

end KltDP.Geometry.ProjectiveImageChartFieldGeneration

namespace KltDP.Geometry.LinearSystemMorphism

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSectionNonvanishingOpen ProjectiveCoordinateSectionBasicOpen

variable {X : Scheme.{u}} (L : InvertibleSheaf X) {n : ℕ}
  (s : Fin (n + 1) → L.obj.sections)

/-- Any nonempty selected section open has an original nonempty affine
chart whose selected index is exactly the specified one. -/
theorem exists_nonempty_chart_at_index (j : Fin (n + 1))
    [Nonempty (nonvanishingOpen X L (s j))] :
    ∃ c : Chart L s, c.index = j ∧ Nonempty c.affineOpen.1 := by
  let x : (nonvanishingOpen X L (s j)).toScheme := Classical.choice inferInstance
  have ht : x.val ∈ ⨆ i, L.localTrivializations.X i := by
    rw [TransitionUnitExtraction.chartOpens_cover]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp ht
  have hx : x.val ∈ L.localTrivializations.X i ⊓ nonvanishingOpen X L (s j) :=
    ⟨hi, x.property⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    (isBasis_affine_open X).exists_subset_of_mem_open hx
      (L.localTrivializations.X i ⊓ nonvanishingOpen X L (s j)).2
  exact ⟨⟨⟨U, hU⟩, i, hUV.trans inf_le_left, j, hUV.trans inf_le_right⟩,
    rfl, ⟨⟨x.val, hxU⟩⟩⟩

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))
  (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤)

/-- The actual selected projective inverse-image chart is nonempty
because it contains the specified actual nonempty source chart. -/
theorem chart_preimage_nonempty (c : Chart L s) [Nonempty c.affineOpen.1] :
    Nonempty (morphism L s f hcover ⁻¹ᵁ standardOpen k n c.index) := by
  let x : c.affineOpen.1.toScheme := Classical.choice inferInstance
  exact ⟨⟨x.val, chart_le_preimage_standardOpen L s f hcover c x.property⟩⟩

/-- The polynomial generator's original field coordinate is precisely
the generic germ of the original normalized coefficient. -/
theorem fieldCoordinate_eq_coordinate_germ [IsIntegral X]
    (c : Chart L s) [Nonempty c.affineOpen.1] (j : Fin (n + 1)) :
    letI := chart_preimage_nonempty L s f hcover c
    ProjectiveImageChartFieldGeneration.fieldCoordinate (morphism L s f hcover) c.index j =
      X.germToFunctionField c.affineOpen.1
        (coordinates L s c.frame c.inFrame c.index c.nonvanishing j) := by
  letI := chart_preimage_nonempty L s f hcover c
  rw [ProjectiveImageChartFieldGeneration.fieldCoordinate_eq_appLE_germ
    (morphism L s f hcover) c.index c.affineOpen.1
      (chart_le_preimage_standardOpen L s f hcover c),
    morphism_appLE_coordinateSection]

end KltDP.Geometry.LinearSystemMorphism

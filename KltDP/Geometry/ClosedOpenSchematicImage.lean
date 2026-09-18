import KltDP.Geometry.ReducedClosedImageChart
import KltDP.Geometry.SchematicImageGlued
import KltDP.Geometry.SchematicImageDenseOpen

/-!
# The original closed-in-open source is open in its actual schematic image

The accepted reduced-closed-image chart theorem applies directly to the
original quotient-glued schematic image. Its factorization and support
premises are supplied by the proved original image construction. No chart
comparison, completion, or compatibility witness is a caller hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ClosedOpenSchematicImage

/-- The actual source embedded closed in an open chart embeds openly in
its actual schematic closure. -/
theorem toImage_isOpenImmersion {W A P : Scheme.{u}} [IsReduced W]
    (i : W ⟶ A) [IsClosedImmersion i] (j : A ⟶ P) [IsOpenImmersion j]
    [QuasiCompact (i ≫ j)] : IsOpenImmersion (SchematicImageGlued.toImage (i ≫ j)) := by
  letI : IsReduced (SchematicImageGlued.image (i ≫ j)) :=
    SchematicImageDenseOpen.image_glued_isReduced (i ≫ j)
  apply ReducedClosedImageChart.isOpenImmersion_of_reduced_closed_image i j
    (SchematicImageGlued.inclusion (i ≫ j)) (SchematicImageGlued.toImage (i ≫ j))
  · exact SchematicImageGlued.toImage_inclusion (i ≫ j)
  · rw [Scheme.IdealSheafData.range_gluedTo, Scheme.Hom.support_ker]

end KltDP.Geometry.ClosedOpenSchematicImage

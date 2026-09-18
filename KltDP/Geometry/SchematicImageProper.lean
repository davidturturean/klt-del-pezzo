import KltDP.Geometry.SchematicImageToImageIso
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper maps to their original schematic images

The existing factor through the quotient-glued kernel subscheme is proper
by the proper-composite lemma. Its surjectivity is the accepted closed-range
image theorem. An integral source gives an irreducible image by continuous
surjectivity and a reduced image by the accepted radical-kernel theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.SchematicImageProper

variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsProper g]

/-- The original factor map to the original schematic image of a proper map is proper. -/
instance toImage_isProper : IsProper (SchematicImageGlued.toImage g) := by
  haveI : IsProper (SchematicImageGlued.toImage g ≫ SchematicImageGlued.inclusion g) := by
    rw [SchematicImageGlued.toImage_inclusion g]
    infer_instance
  exact IsProper.of_comp_of_isSeparated (SchematicImageGlued.toImage g)
    (SchematicImageGlued.inclusion g)

/-- Closedness of the original range makes the original schematic-image factor surjective. -/
instance toImage_surjective : Surjective (SchematicImageGlued.toImage g) :=
  SchematicImageToImageIso.toImage_surjective g g.isClosedMap.isClosed_range

/-- The original image inclusion has exactly the original proper morphism's range. -/
theorem range_inclusion : Set.range (SchematicImageGlued.inclusion g).base = Set.range g.base := by
  rw [Scheme.IdealSheafData.range_gluedTo, Scheme.Hom.support_ker,
    g.isClosedMap.isClosed_range.closure_eq]

/-- The original schematic image of a proper map from an integral scheme is integral. -/
instance image_isIntegral [IsIntegral X] : IsIntegral (SchematicImageGlued.image g) := by
  letI : IsReduced (SchematicImageGlued.image g) :=
    SchematicImageDenseOpen.image_glued_isReduced g
  haveI : IrreducibleSpace (SchematicImageGlued.image g) := by
    apply (irreducibleSpace_def (SchematicImageGlued.image g)).mpr
    have h := (IrreducibleSpace.isIrreducible_univ X).image
      (SchematicImageGlued.toImage g).base (SchematicImageGlued.toImage g).continuous.continuousOn
    simpa only [Set.image_univ, (SchematicImageGlued.toImage g).surjective.range_eq] using h
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end KltDP.Geometry.SchematicImageProper

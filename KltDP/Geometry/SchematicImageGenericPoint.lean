import KltDP.Geometry.SchematicImageIntegral
import KltDP.Geometry.CartierDivisorPullback

/-!
# The original generic point and function-field map of a schematic image

The original factor to the actual schematic image sends the source generic
point to the image generic point. Both map under the closed inclusion to
the unique generic point of the original range closure. This supplies the
existing generic-point-preserving interface and its actual function-field
map; no birationality or field-map surjectivity is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.SchematicImageIntegral

variable {X Y : Scheme.{u}} [IsIntegral X] (g : X ⟶ Y) [QuasiCompact g]

local instance integralImage : IsIntegral (SchematicImageGlued.image g) := image_isIntegral g

/-- The original factor sends the original generic point to the actual image's generic point. -/
theorem toImage_map_genericPoint :
    (SchematicImageGlued.toImage g).base (genericPoint X) =
      genericPoint (SchematicImageGlued.image g) := by
  apply (SchematicImageGlued.inclusion g).isClosedEmbedding.injective
  change (SchematicImageGlued.toImage g ≫ SchematicImageGlued.inclusion g).base
      (genericPoint X) = _
  rw [SchematicImageGlued.toImage_inclusion]
  have hsource : IsGenericPoint (g.base (genericPoint X)) (closure (Set.range g.base)) := by
    simpa only [Set.image_univ] using (genericPoint_spec X).image g.continuous
  have himage := (genericPoint_spec (SchematicImageGlued.image g)).image
    (SchematicImageGlued.inclusion g).continuous
  have himage' : IsGenericPoint
      ((SchematicImageGlued.inclusion g).base (genericPoint (SchematicImageGlued.image g)))
      (closure (Set.range g.base)) := by
    simpa only [Set.image_univ, range_inclusion g, closure_closure] using himage
  exact hsource.eq himage'

/-- The actual image factor satisfies the existing generic-point interface. -/
instance toImage_genericPointPreserving :
    GenericPointPreserving (SchematicImageGlued.toImage g) :=
  ⟨toImage_map_genericPoint g⟩

/-- The existing actual function-field map of this factor is injective. -/
theorem toImage_functionFieldMap_injective :
    Function.Injective (functionFieldMap (SchematicImageGlued.toImage g)).hom :=
  (functionFieldMap (SchematicImageGlued.toImage g)).hom.injective

end KltDP.Geometry.SchematicImageIntegral

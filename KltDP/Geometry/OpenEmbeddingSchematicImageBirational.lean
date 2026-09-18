import KltDP.Geometry.ImmersionBirational
import KltDP.Geometry.SchematicImageOpenImmersion
import KltDP.Geometry.SchematicImageToImageIso

/-!
# A nonempty open in an original closed embedding is birational onto its schematic image

The original nonempty open immersion leaves the kernel ideal unchanged.
The accepted closed embedding is its own actual schematic image, and the
unchanged kernel gives an actual image isomorphism. Consequently the
original factor from the open source to its schematic image is exactly
the original open immersion followed by this constructed isomorphism.
Its openness, integral target, and birationality are all derived.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.OpenEmbeddingSchematicImageBirational

variable {S X Y : Scheme.{u}} [IsIntegral X]
  (j : S ⟶ X) [IsOpenImmersion j] [Nonempty S]
  (i : X ⟶ Y) [IsClosedImmersion i]

/-- The original complete closed source is isomorphic to the actual image of its nonempty open. -/
def imageIso : X ≅ SchematicImageGlued.image (j ≫ i) :=
  SchematicImageToImageIso.toImageIso i ≪≫
    SchematicImageOpenBaseChange.imageIsoOfKerEq i (j ≫ i)
      (SchematicImageOpenImmersion.ker_precompose_openImmersion j i).symm

/-- The constructed image isomorphism retains the original closed embedding. -/
@[reassoc]
theorem imageIso_hom_inclusion :
    (imageIso j i).hom ≫ SchematicImageGlued.inclusion (j ≫ i) = i := by
  dsimp only [imageIso, Iso.trans_hom]
  rw [Category.assoc, SchematicImageOpenBaseChange.imageIsoOfKerEq_hom_inclusion,
    SchematicImageToImageIso.toImageIso_hom_inclusion]

/-- The factor map is the actual original open immersion followed by the constructed image iso. -/
theorem toImage_eq :
    SchematicImageGlued.toImage (j ≫ i) = j ≫ (imageIso j i).hom := by
  apply (cancel_mono (SchematicImageGlued.inclusion (j ≫ i))).mp
  rw [SchematicImageGlued.toImage_inclusion, Category.assoc, imageIso_hom_inclusion]

/-- The actual factor to the schematic image is an open immersion. -/
theorem toImage_isOpenImmersion : IsOpenImmersion (SchematicImageGlued.toImage (j ≫ i)) := by
  rw [toImage_eq j i]
  infer_instance

/-- Integrality belongs to the actual image scheme, by the constructed source isomorphism. -/
theorem image_isIntegral : IsIntegral (SchematicImageGlued.image (j ≫ i)) := by
  let e := imageIso j i
  letI : Nonempty (SchematicImageGlued.image (j ≫ i)) := ⟨e.hom.base (genericPoint X)⟩
  exact isIntegral_of_isOpenImmersion e.inv

/-- The original restricted embedding is birational onto its actual integral schematic image. -/
theorem toImage_isBirationalScheme :
    letI : IsIntegral S := isIntegral_of_isOpenImmersion j
    letI : IsIntegral (SchematicImageGlued.image (j ≫ i)) := image_isIntegral j i
    IsBirationalScheme (SchematicImageGlued.toImage (j ≫ i)) := by
  letI : IsIntegral S := isIntegral_of_isOpenImmersion j
  letI : IsIntegral (SchematicImageGlued.image (j ≫ i)) := image_isIntegral j i
  letI := toImage_isOpenImmersion j i
  exact ImmersionBirational.isBirationalScheme_of_isOpenImmersion
    (SchematicImageGlued.toImage (j ≫ i))

end KltDP.Geometry.OpenEmbeddingSchematicImageBirational

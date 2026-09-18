import KltDP.Geometry.LinearSystemProper
import KltDP.Geometry.SchematicImageProper

/-!
# The original projective schematic image of a linear system

The target remains the existing SchematicImageGlued.image of the actual
linear-system morphism. Its existing closed inclusion into the original
projective space supplies the projective embedding over the original field.
The original factor is proper and surjective for a proper source, and the
actual image is integral when that source is integral.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.LinearSystemMorphism

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSectionNonvanishingOpen

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (L : InvertibleSheaf X) {n : ℕ} (s : Fin (n + 1) → L.obj.sections)
  (f : X ⟶ Spec (CommRingCat.of k))
  (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤)

/-- The actual schematic image, equipped with its original structure map to the original field. -/
def imageStructure : SchematicImageGlued.image (morphism L s f hcover) ⟶ Spec (CommRingCat.of k) :=
  SchematicImageGlued.inclusion (morphism L s f hcover) ≫ projectiveSpaceToSpec k n

/-- The actual image has its defining closed projective embedding over the original field. -/
theorem imageStructure_isProjective : IsProjectiveOverField (imageStructure L s f hcover) :=
  ⟨n, SchematicImageGlued.inclusion (morphism L s f hcover), inferInstance, rfl⟩

instance imageStructure_isProper : IsProper (imageStructure L s f hcover) := by
  unfold imageStructure
  infer_instance

/-- The original factor to the image is a morphism over the original structure map f. -/
@[reassoc] theorem toImage_structure :
    SchematicImageGlued.toImage (morphism L s f hcover) ≫ imageStructure L s f hcover = f := by
  rw [imageStructure, ← Category.assoc, SchematicImageGlued.toImage_inclusion,
    morphism_structure L s f hcover]

variable [IsProper f]

/-- The actual linear-system factor to its original schematic image is proper. -/
theorem toImage_isProper : IsProper (SchematicImageGlued.toImage (morphism L s f hcover)) :=
  SchematicImageProper.toImage_isProper (morphism L s f hcover)

/-- The actual linear-system factor covers every point of its original schematic image. -/
theorem toImage_surjective : Surjective (SchematicImageGlued.toImage (morphism L s f hcover)) :=
  SchematicImageProper.toImage_surjective (morphism L s f hcover)

/-- An integral original proper source gives an integral original linear-system image. -/
theorem image_isIntegral [IsIntegral X] : IsIntegral (SchematicImageGlued.image (morphism L s f hcover)) :=
  SchematicImageProper.image_isIntegral (morphism L s f hcover)

end KltDP.Geometry.LinearSystemMorphism

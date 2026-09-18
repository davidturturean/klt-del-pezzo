import KltDP.Geometry.BirationalComposition
import KltDP.Geometry.GenericPointPreservingTriangle
import KltDP.Geometry.ImmersionBirational
import KltDP.Geometry.SchematicImageGenericPrecomposition
import KltDP.Geometry.SchematicImageOpenImmersion
import KltDP.Geometry.SchematicImageToImageIso

/-!
# Birationality from an original open and closed immersion triangle

Generic-point-preserving precomposition and a nonempty open immersion
preserve the actual kernel ideal. The given triangle therefore identifies
the actual schematic image of its second map with the original closed
source. Its original factor gives a comparison map whose composite with
the first map is the original open immersion. Evaluating this equation at
the original generic point proves generic-point preservation of the
comparison; birationality of the open immersion then proves birationality
of the first map. No image identification or quasi-compactness is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.SchematicBirationalComparison

variable {T X Y Z : Scheme.{u}} [IsIntegral T] [IsIntegral X] [IsIntegral Y]
  (a : T ⟶ Y) [GenericPointPreserving a] (b : Y ⟶ Z)
  (j : T ⟶ X) [IsOpenImmersion j] (i : X ⟶ Z) [IsClosedImmersion i]

/-- The exact triangle identifies the actual kernel ideals. -/
theorem ker_eq (h : a ≫ b = j ≫ i) : b.ker = i.ker := by
  calc
    b.ker = (a ≫ b).ker := (SchematicImageGenericPrecomposition.ker_precompose a b).symm
    _ = (j ≫ i).ker := congrArg Scheme.Hom.ker h
    _ = i.ker := SchematicImageOpenImmersion.ker_precompose_openImmersion j i

/-- The original closed source is the actual schematic image of the second map. -/
def imageIso (h : a ≫ b = j ≫ i) : SchematicImageGlued.image b ≅ X :=
  SchematicImageOpenBaseChange.imageIsoOfKerEq b i (ker_eq a b j i h) ≪≫
    (SchematicImageToImageIso.toImageIso i).symm

/-- The constructed image isomorphism respects the original closed inclusion. -/
@[reassoc]
theorem imageIso_hom_inclusion (h : a ≫ b = j ≫ i) :
    (imageIso a b j i h).hom ≫ i = SchematicImageGlued.inclusion b := by
  dsimp only [imageIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, SchematicImageToImageIso.toImageIso_inv_comp,
    SchematicImageOpenBaseChange.imageIsoOfKerEq_hom_inclusion]

/-- The comparison uses the original factor into the actual schematic image. -/
def comparison (h : a ≫ b = j ≫ i) : Y ⟶ X :=
  SchematicImageGlued.toImage b ≫ (imageIso a b j i h).hom

/-- The comparison factors the original second map through the original closed embedding. -/
@[reassoc]
theorem comparison_comp_inclusion (h : a ≫ b = j ≫ i) :
    comparison a b j i h ≫ i = b := by
  dsimp only [comparison]
  rw [Category.assoc, imageIso_hom_inclusion, SchematicImageGlued.toImage_inclusion]

/-- Monicity of the original closed embedding recovers the original open immersion. -/
theorem precompose_comparison (h : a ≫ b = j ≫ i) :
    a ≫ comparison a b j i h = j := by
  apply (cancel_mono i).mp
  rw [Category.assoc, comparison_comp_inclusion, h]

/-- The triangle itself proves that the comparison preserves the original generic point. -/
theorem comparison_genericPointPreserving (h : a ≫ b = j ≫ i) :
    GenericPointPreserving (comparison a b j i h) := by
  letI : GenericPointPreserving j := ⟨genericPoint_eq_of_isOpenImmersion j⟩
  exact GenericPointPreservingTriangle.right_of_comp_eq a (comparison a b j i h) j
    (precompose_comparison a b j i h)

/-- The original first map is birational, with no assumed image identification. -/
theorem isBirationalScheme_of_open_closed_triangle (h : a ≫ b = j ≫ i) :
    IsBirationalScheme a := by
  letI := comparison_genericPointPreserving a b j i h
  apply BirationalComposition.isBirationalScheme_left_of_comp a (comparison a b j i h)
  rw [precompose_comparison]
  exact ImmersionBirational.isBirationalScheme_of_isOpenImmersion j

end KltDP.Geometry.SchematicBirationalComparison

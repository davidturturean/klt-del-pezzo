import KltDP.Geometry.SchematicImageOpenBaseChange

/-!
# A closed immersion with reduced source is its own schematic image

For `f : X ⟶ Y`, the accepted `SchematicImageGlued.toImage f : X ⟶ image f` factors `f` through the glued
closed subscheme of `f.ker`. If `f` is a closed immersion, `toImage f` is a closed immersion
(`of_comp_isClosedImmersion`) and, the range of `f` being closed, surjective (`toImage_surjective`, from
`range_gluedTo`, `support_ker`, `gluedTo_injective`). If moreover `X` is reduced, so is `image f`
(accepted `image_glued_isReduced`), and the pinned `isIso_of_isClosedImmersion_of_surjective` makes
`toImage f` an isomorphism (`toImage_isIso`, `toImageIso`): a closed immersion with reduced source is the
glued closed subscheme of its own kernel. Combined with `imageIsoOfKerEq`, two closed immersions with
reduced sources and equal kernels have isomorphic sources over the target
(`isoOfKerEq`, `isoOfKerEq_hom`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace KltDP.Geometry.SchematicImageToImageIso

open SchematicImageOpenBaseChange

variable {X X' Y : Scheme.{u}} (f : X ⟶ Y)

/-- `toImage f` is a closed immersion when `f` is. -/
theorem toImage_isClosedImmersion [IsClosedImmersion f] : IsClosedImmersion (SchematicImageGlued.toImage f) := by
  haveI : IsClosedImmersion (SchematicImageGlued.toImage f ≫ SchematicImageGlued.inclusion f) := by
    rw [SchematicImageGlued.toImage_inclusion]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion (SchematicImageGlued.toImage f)
    (SchematicImageGlued.inclusion f)

/-- `toImage f` is surjective when the range of `f` is closed. -/
theorem toImage_surjective [QuasiCompact f] (hf : IsClosed (Set.range f.base)) :
    Surjective (SchematicImageGlued.toImage f) := by
  constructor
  intro z
  have hz : (SchematicImageGlued.inclusion f).base z ∈ Set.range (SchematicImageGlued.inclusion f).base := ⟨z, rfl⟩
  rw [Scheme.IdealSheafData.range_gluedTo, Scheme.Hom.support_ker, hf.closure_eq] at hz
  obtain ⟨x, hx⟩ := hz
  refine ⟨x, Scheme.IdealSheafData.gluedTo_injective f.ker ?_⟩
  change (SchematicImageGlued.toImage f ≫ SchematicImageGlued.inclusion f).base x = (SchematicImageGlued.inclusion f).base z
  rw [SchematicImageGlued.toImage_inclusion]
  exact hx

/-- **A closed immersion with reduced source is its own schematic image.** -/
theorem toImage_isIso [IsClosedImmersion f] [IsReduced X] : IsIso (SchematicImageGlued.toImage f) := by
  haveI := toImage_isClosedImmersion f
  haveI : IsReduced (SchematicImageGlued.image f) := SchematicImageDenseOpen.image_glued_isReduced f
  haveI := toImage_surjective f f.isClosedEmbedding.isClosed_range
  exact isIso_of_isClosedImmersion_of_surjective _

/-- The isomorphism of a closed immersion's source with its glued image. -/
def toImageIso [IsClosedImmersion f] [IsReduced X] : X ≅ SchematicImageGlued.image f :=
  letI := toImage_isIso f
  asIso (SchematicImageGlued.toImage f)

@[reassoc] theorem toImageIso_hom_inclusion [IsClosedImmersion f] [IsReduced X] :
    (toImageIso f).hom ≫ SchematicImageGlued.inclusion f = f :=
  SchematicImageGlued.toImage_inclusion f

theorem toImageIso_inv_comp [IsClosedImmersion f] [IsReduced X] :
    (toImageIso f).inv ≫ f = SchematicImageGlued.inclusion f := by
  rw [Iso.inv_comp_eq, toImageIso_hom_inclusion]

/-- Two closed immersions with reduced sources and equal kernels have isomorphic sources. -/
def isoOfKerEq (g : X' ⟶ Y) [IsClosedImmersion f] [IsClosedImmersion g] [IsReduced X] [IsReduced X']
    (h : f.ker = g.ker) : X ≅ X' :=
  toImageIso f ≪≫ imageIsoOfKerEq f g h ≪≫ (toImageIso g).symm

/-- The isomorphism is compatible with the closed immersions. -/
@[reassoc] theorem isoOfKerEq_hom (g : X' ⟶ Y) [IsClosedImmersion f] [IsClosedImmersion g]
    [IsReduced X] [IsReduced X'] (h : f.ker = g.ker) : (isoOfKerEq f g h).hom ≫ g = f := by
  simp only [isoOfKerEq, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [toImageIso_inv_comp, imageIsoOfKerEq_hom_inclusion, toImageIso_hom_inclusion]

end KltDP.Geometry.SchematicImageToImageIso

import KltDP.Geometry.KeelCompleteSystemBirational
import KltDP.Geometry.CompleteLinearSystemBaseLocus
import KltDP.Geometry.SchematicImageProper
import KltDP.Geometry.BirationalComposition
import KltDP.Geometry.ImmersionBirational
import KltDP.Geometry.RationalTreePicardPullbackEquivalence

/-!
The actual complete-system image of a globally generated line. Its original
non-base open is the whole source, so the original image factor extends by
the inverse of that open inclusion. Properness, surjectivity, birationality,
and the original ample image line are transported through this isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CompleteLinearSystemMap

open CompleteLinearSystemSections

attribute [local instance] KeelCompleteSystem.completeSystemDomain_isIntegral
  KeelCompleteSystem.completeSystemImage_isIntegral

private theorem isIso_iota_of_eq_top {X : Scheme.{u}} (U : X.Opens)
    (hU : U = ⊤) : IsIso U.ι := by
  subst U
  change IsIso X.topIso.hom
  infer_instance

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (L : InvertibleSheaf X)
  [IsProper f] [IsIntegral X] (hpos : 0 < dimension f L)
  (hG : Positivity.IsGloballyGenerated L.obj)

include hG

/-- Global generation makes the original whole-basis non-base open the whole scheme. -/
theorem nonBaseOpen_eq_top_of_globallyGenerated : nonBaseOpen f L hpos = ⊤ :=
  CompleteLinearSystemExpansion.basis_cover_of_globallyGenerated f L hpos hG

/-- The actual non-base-open inclusion, now an isomorphism to the original source. -/
def generatedNonBaseIso : (nonBaseOpen f L hpos).toScheme ≅ X := by
  letI := isIso_iota_of_eq_top (nonBaseOpen f L hpos)
    (nonBaseOpen_eq_top_of_globallyGenerated f L hpos hG)
  exact asIso (nonBaseOpen f L hpos).ι

@[simp] theorem generatedNonBaseIso_hom :
    (generatedNonBaseIso f L hpos hG).hom = (nonBaseOpen f L hpos).ι := rfl

/-- The complete-system morphism is proper when its whole basis generates everywhere. -/
theorem morphism_isProper_of_globallyGenerated : IsProper (morphism f L hpos) := by
  letI : IsIso (nonBaseOpen f L hpos).ι := isIso_iota_of_eq_top _
    (nonBaseOpen_eq_top_of_globallyGenerated f L hpos hG)
  letI : IsProper (morphism f L hpos ≫ projectiveSpaceToSpec k (dimension f L - 1)) := by
    rw [morphism_structure]
    infer_instance
  exact IsProper.of_comp_of_isSeparated (morphism f L hpos)
    (projectiveSpaceToSpec k (dimension f L - 1))

/-- The original complete-system image factor, extended to the original whole scheme. -/
def generatedToImage : X ⟶ SchematicImageGlued.image (morphism f L hpos) :=
  (generatedNonBaseIso f L hpos hG).inv ≫ SchematicImageGlued.toImage (morphism f L hpos)

/-- This extension preserves the original field structure. -/
@[reassoc] theorem generatedToImage_structure :
    generatedToImage f L hpos hG ≫ imageStructure f L hpos = f := by
  rw [generatedToImage, Category.assoc, toImage_structure,
    ← generatedNonBaseIso_hom f L hpos hG,
    Iso.inv_hom_id_assoc]

/-- The actual extension to the original complete-system image is proper. -/
theorem generatedToImage_isProper : IsProper (generatedToImage f L hpos hG) := by
  letI := morphism_isProper_of_globallyGenerated f L hpos hG
  unfold generatedToImage
  infer_instance

/-- The actual extension is surjective onto that same schematic image. -/
theorem generatedToImage_surjective : Surjective (generatedToImage f L hpos hG) := by
  letI := morphism_isProper_of_globallyGenerated f L hpos hG
  unfold generatedToImage
  infer_instance

/-- Birationality of the original complete system gives birationality of its whole-source map. -/
theorem generatedToImage_isBirationalScheme
    (hbir : IsBirationalScheme (SchematicImageGlued.toImage (morphism f L hpos))) :
    IsBirationalScheme (generatedToImage f L hpos hG) := by
  let e := generatedNonBaseIso f L hpos hG
  letI : GenericPointPreserving e.inv := ⟨genericPoint_eq_of_isOpenImmersion e.inv⟩
  letI : GenericPointPreserving (SchematicImageGlued.toImage (morphism f L hpos)) :=
    ⟨hbir.map_genericPoint⟩
  exact (BirationalComposition.isBirationalScheme_comp_iff e.inv
    (SchematicImageGlued.toImage (morphism f L hpos))).mpr
      ⟨ImmersionBirational.isBirationalScheme_of_isOpenImmersion e.inv, hbir⟩

/-- The actual ample image line pulls back to the original whole-source line. -/
def generatedToImage_pullbackImageLineIso :
    (pullbackInvertibleSheaf (generatedToImage f L hpos hG)
      (imageLine f L hpos)).obj ≅ L.obj :=
  ((schemeModulePullbackCompIso (generatedNonBaseIso f L hpos hG).inv
    (SchematicImageGlued.toImage (morphism f L hpos))).app (imageLine f L hpos).obj).symm ≪≫
    (schemeModulePullback (generatedNonBaseIso f L hpos hG).inv).mapIso
      (toImage_pullbackImageLineIso f L hpos) ≪≫
    ((schemeModulePullbackEquivalenceOfIsIso (generatedNonBaseIso f L hpos hG).hom).unitIso.app
      L.obj).symm

end KltDP.Geometry.CompleteLinearSystemMap

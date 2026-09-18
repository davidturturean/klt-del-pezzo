import KltDP.Geometry.CompleteLinearSystemMap
import KltDP.Geometry.SchematicImageIntegral
import KltDP.Geometry.LinearSystemImageAmple
import KltDP.Geometry.LocallyOfFiniteTypeNoetherian

/-!
# The original projective image of the complete linear system

The actual morphism on the dense non-base open factors through the
quotient-glued kernel subscheme in its original projective space. The
original proper source is Noetherian, so that morphism is quasi-compact
and its actual image is integral. Its closed projective embedding gives
an ample line whose pullback is the original line on the non-base open.
No properness or birationality of the non-base-open map is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.CompleteLinearSystemMap

open CompleteLinearSystemSections

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (L : InvertibleSheaf X)
  [IsProper f] [IsIntegral X] (hpos : 0 < dimension f L)

/-- The original complete-system morphism is quasi-compact by Noetherianity of its domain. -/
instance morphism_quasiCompact : QuasiCompact (morphism f L hpos) := by
  letI : NoetherianSpace X := noetherianSpace_of_locallyOfFiniteType_quasiCompact_spec f
  letI : NoetherianSpace (nonBaseOpen f L hpos).toScheme :=
    (nonBaseOpen f L hpos).ι.isOpenEmbedding.isEmbedding.toIsInducing.noetherianSpace
  infer_instance

/-- The actual scheme-theoretic image of the complete system is integral. -/
theorem image_isIntegral : IsIntegral (SchematicImageGlued.image (morphism f L hpos)) := by
  letI : Nonempty (nonBaseOpen f L hpos) := (nonBaseOpen_nonempty f L hpos).to_subtype
  letI : IsIntegral (nonBaseOpen f L hpos).toScheme := inferInstance
  exact SchematicImageIntegral.image_isIntegral (morphism f L hpos)

/-- The original closed image carries its original field structure. -/
def imageStructure : SchematicImageGlued.image (morphism f L hpos) ⟶ Spec (CommRingCat.of k) :=
  SchematicImageGlued.inclusion (morphism f L hpos) ≫ projectiveSpaceToSpec k (dimension f L - 1)

/-- Its defining original closed embedding is a projective embedding. -/
theorem imageStructure_isProjective : IsProjectiveOverField (imageStructure f L hpos) :=
  ⟨dimension f L - 1, SchematicImageGlued.inclusion (morphism f L hpos), inferInstance, rfl⟩

instance imageStructure_isProper : IsProper (imageStructure f L hpos) := by
  unfold imageStructure
  infer_instance

/-- The original factor on the non-base open respects the original field structure. -/
@[reassoc] theorem toImage_structure :
    SchematicImageGlued.toImage (morphism f L hpos) ≫ imageStructure f L hpos =
      (nonBaseOpen f L hpos).ι ≫ f := by
  rw [imageStructure, ← Category.assoc, SchematicImageGlued.toImage_inclusion,
    morphism_structure]

/-- The actual degree-one sheaf restricted to the original complete-system image. -/
def imageLine : InvertibleSheaf (SchematicImageGlued.image (morphism f L hpos)) :=
  pullbackInvertibleSheaf (SchematicImageGlued.inclusion (morphism f L hpos))
    (ProjectiveSpaceDegreeOneSheaf.degreeOne k (dimension f L - 1))

/-- This original image line is ample by its defining closed projective embedding. -/
theorem imageLine_isAmple : AmpleSerre.IsAmple (imageLine f L hpos) :=
  projectiveSpaceDegreeOne_pullback_isAmple k (dimension f L - 1)
    (SchematicImageGlued.inclusion (morphism f L hpos))

/-- Its actual pullback to the non-base open is the original restricted line. -/
def toImage_pullbackImageLineIso :
    (pullbackInvertibleSheaf (SchematicImageGlued.toImage (morphism f L hpos))
      (imageLine f L hpos)).obj ≅
        (pullbackInvertibleSheaf (nonBaseOpen f L hpos).ι L).obj :=
  (schemeModulePullbackCompIso (SchematicImageGlued.toImage (morphism f L hpos))
    (SchematicImageGlued.inclusion (morphism f L hpos))).app
      (ProjectiveSpaceDegreeOneSheaf.degreeOne k (dimension f L - 1)).obj ≪≫
    eqToIso (congrArg (fun h => (schemeModulePullback h).obj
      (ProjectiveSpaceDegreeOneSheaf.degreeOne k (dimension f L - 1)).obj)
        (SchematicImageGlued.toImage_inclusion (morphism f L hpos))) ≪≫
      pullbackDegreeOneIso f L hpos

/-- The complete-system rational map with its actual schematic image as target. -/
def partialMapToImage : X.PartialMap (SchematicImageGlued.image (morphism f L hpos)) where
  domain := nonBaseOpen f L hpos
  dense_domain := nonBaseOpen_dense f L hpos
  hom := SchematicImageGlued.toImage (morphism f L hpos)

/-- The same original complete-system factor as an existing rational-map class. -/
def rationalMapToImage : X ⤏ SchematicImageGlued.image (morphism f L hpos) :=
  (partialMapToImage f L hpos).toRationalMap

end KltDP.Geometry.CompleteLinearSystemMap

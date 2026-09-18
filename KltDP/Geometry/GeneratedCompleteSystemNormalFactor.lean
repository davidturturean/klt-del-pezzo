import KltDP.Geometry.GeneratedCompleteSystemImage
import KltDP.Geometry.PushforwardRelativeSpecFinite
import KltDP.Geometry.PushforwardRelativeSpecBirational

/-!
The normal factor of the original generated complete-system map. Its
underlying target is the constructed relative spectrum of that map's
actual pushforward structure sheaf. The source and image maps are the
original `fromSource` and `toBase`, and the target line is the actual
pullback of the original image line. The field and line-bundle triangles
are proved from the original factorization; no chosen factorization,
normal target, or compatible line is an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.GeneratedCompleteSystemNormalFactor

open CompleteLinearSystemSections CompleteLinearSystemMap

attribute [local instance] KeelCompleteSystem.completeSystemDomain_isIntegral
  KeelCompleteSystem.completeSystemImage_isIntegral

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (L : InvertibleSheaf X)
  [IsProper f] [IsIntegral X] (hpos : 0 < dimension f L)
  (hG : Positivity.IsGloballyGenerated L.obj)

local instance generatedMap_isProper : IsProper (generatedToImage f L hpos hG) :=
  generatedToImage_isProper f L hpos hG

local instance image_isLocallyNoetherian :
    IsLocallyNoetherian (SchematicImageGlued.image (morphism f L hpos)) :=
  isLocallyNoetherian_of_locallyOfFiniteType_spec (imageStructure f L hpos)

/-- The actual pushforward relative spectrum of the original generated map. -/
abbrev target : Scheme.{u} :=
  PushforwardRelativeSpec.relativeSpec (generatedToImage f L hpos hG)

/-- The original canonical map from the whole source to that relative spectrum. -/
def fromSource : X ⟶ target f L hpos hG :=
  PushforwardRelativeSpec.fromSource (generatedToImage f L hpos hG)

/-- The original relative-spectrum map to the same complete-system image. -/
def toImage : target f L hpos hG ⟶ SchematicImageGlued.image (morphism f L hpos) :=
  PushforwardRelativeSpec.toBase (generatedToImage f L hpos hG)

/-- The target carries the field structure of the original complete-system image. -/
def structureMorphism : target f L hpos hG ⟶ Spec (CommRingCat.of k) :=
  toImage f L hpos hG ≫ imageStructure f L hpos

/-- The actual line pulled back from the original ample image line. -/
def line : InvertibleSheaf (target f L hpos hG) :=
  pullbackInvertibleSheaf (toImage f L hpos hG) (imageLine f L hpos)

/-- The exact triangle to the original complete-system image. -/
@[reassoc] theorem fromSource_toImage :
    fromSource f L hpos hG ≫ toImage f L hpos hG = generatedToImage f L hpos hG :=
  PushforwardRelativeSpec.fromSource_toBase (generatedToImage f L hpos hG)

/-- The exact triangle over the original field. -/
@[reassoc] theorem fromSource_structure :
    fromSource f L hpos hG ≫ structureMorphism f L hpos hG = f := by
  rw [structureMorphism, ← Category.assoc, fromSource_toImage,
    generatedToImage_structure]

/-- Integrality of this target is derived from the original integral source. -/
local instance target_isIntegral : IsIntegral (target f L hpos hG) :=
  PushforwardRelativeSpec.relativeSpec_isIntegral (generatedToImage f L hpos hG)

/-- Normality is derived through the original structure-sheaf comparison. -/
theorem target_isNormal (hnormal : IsNormalScheme X) :
    IsNormalScheme (target f L hpos hG) :=
  PushforwardRelativeSpec.relativeSpec_isNormal (generatedToImage f L hpos hG) hnormal

/-- The actual map from the normal factor to the original image is finite. -/
theorem toImage_isFinite : IsFinite (toImage f L hpos hG) :=
  PushforwardRelativeSpec.toBase_isFinite (generatedToImage f L hpos hG)

/-- The actual source map in this factorization is proper. -/
theorem fromSource_isProper : IsProper (fromSource f L hpos hG) :=
  PushforwardRelativeSpec.fromSource_isProper (generatedToImage f L hpos hG)

/-- The actual source map is surjective onto this same target. -/
theorem fromSource_surjective : Surjective (fromSource f L hpos hG) :=
  PushforwardRelativeSpec.fromSource_surjective (generatedToImage f L hpos hG)

/-- Its original canonical structure-sheaf map is an isomorphism. -/
theorem fromSource_c_isIso : IsIso (fromSource f L hpos hG).c :=
  PushforwardRelativeSpec.fromSource_c_isIso (generatedToImage f L hpos hG)

/-- The target is proper over the original field by its actual finite image map. -/
theorem structureMorphism_isProper : IsProper (structureMorphism f L hpos hG) := by
  letI : IsFinite (toImage f L hpos hG) := toImage_isFinite f L hpos hG
  unfold structureMorphism
  infer_instance

/-- Original complete-system birationality gives birationality of the source factor. -/
theorem fromSource_isBirationalScheme
    (hbir : IsBirationalScheme (SchematicImageGlued.toImage (morphism f L hpos))) :
    IsBirationalScheme (fromSource f L hpos hG) :=
  (PushforwardRelativeSpec.fromSource_and_toBase_isBirational
    (generatedToImage f L hpos hG)
    (generatedToImage_isBirationalScheme f L hpos hG hbir)).1

/-- The same argument preserves birationality of the actual finite image map. -/
theorem toImage_isBirationalScheme
    (hbir : IsBirationalScheme (SchematicImageGlued.toImage (morphism f L hpos))) :
    IsBirationalScheme (toImage f L hpos hG) :=
  (PushforwardRelativeSpec.fromSource_and_toBase_isBirational
    (generatedToImage f L hpos hG)
    (generatedToImage_isBirationalScheme f L hpos hG hbir)).2

/-- The pulled image line pulls back along the original source map to the
original line, using the actual factorization and generated-system recovery iso. -/
def fromSource_pullbackLineIso :
    (pullbackInvertibleSheaf (fromSource f L hpos hG) (line f L hpos hG)).obj ≅ L.obj :=
  (schemeModulePullbackCompIso (fromSource f L hpos hG)
    (toImage f L hpos hG)).app (imageLine f L hpos).obj ≪≫
      eqToIso (congrArg (fun g => (schemeModulePullback g).obj (imageLine f L hpos).obj)
        (fromSource_toImage f L hpos hG)) ≪≫
          generatedToImage_pullbackImageLineIso f L hpos hG

end KltDP.Geometry.GeneratedCompleteSystemNormalFactor

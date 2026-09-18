import KltDP.Geometry.LinearSystemImage
import KltDP.Geometry.LinearSystemDegreeOnePullback
import KltDP.Geometry.ProjectiveAmpleWitness

/-!
# The original projective image carries an ample line pulling back to L

Restrict the original degree-one sheaf through the existing schematic-image
closed inclusion. The already proved closed-embedding ample restriction
theorem proves ampleness of this actual image line. The original pullback
composition and the actual linear-system degree-one comparison identify
its pullback through the original image factor with the original sheaf L.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.LinearSystemMorphism

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSectionNonvanishingOpen ProjectiveSpaceDegreeOneSheaf

private def imagePullbackIso {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules) :
    (schemeModulePullback (SchematicImageGlued.toImage g)).obj
        ((schemeModulePullback (SchematicImageGlued.inclusion g)).obj M) ≅
      (schemeModulePullback g).obj M :=
  (schemeModulePullbackCompIso
    (SchematicImageGlued.toImage g) (SchematicImageGlued.inclusion g)).app M ≪≫
    eqToIso (congrArg (fun h : X ⟶ Y => (schemeModulePullback h).obj M)
      (SchematicImageGlued.toImage_inclusion g))

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (L : InvertibleSheaf X) {n : ℕ} (s : Fin (n + 1) → L.obj.sections)
  (f : X ⟶ Spec (CommRingCat.of k))
  (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤)

/-- The original degree-one sheaf restricted to the actual schematic image. -/
def imageLine : InvertibleSheaf (SchematicImageGlued.image (morphism L s f hcover)) :=
  pullbackInvertibleSheaf (SchematicImageGlued.inclusion (morphism L s f hcover)) (degreeOne k n)

/-- This actual image line is ample in the original coherent-sheaf Serre sense. -/
theorem imageLine_isAmple : AmpleSerre.IsAmple (imageLine L s f hcover) :=
  projectiveSpaceDegreeOne_pullback_isAmple k n
    (SchematicImageGlued.inclusion (morphism L s f hcover))

/-- The actual image factor pulls the actual ample image line back to the original line sheaf. -/
def toImage_pullbackImageLineIso :
    (pullbackInvertibleSheaf (SchematicImageGlued.toImage (morphism L s f hcover))
      (imageLine L s f hcover)).obj ≅ L.obj :=
  imagePullbackIso (morphism L s f hcover) (degreeOne k n).obj ≪≫
    LinearSystemPullback.pullbackDegreeOneIso L s f hcover

end KltDP.Geometry.LinearSystemMorphism

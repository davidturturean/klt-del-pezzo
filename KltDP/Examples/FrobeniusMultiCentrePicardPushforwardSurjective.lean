import KltDP.Geometry.BirationalWeilClassSurjectivity
import KltDP.Geometry.PicardWeilClassHom
import KltDP.Geometry.SmoothSurfaceDivisorPicard
import KltDP.Examples.FrobeniusMultiCentreCanonicalWeilRepresentatives
import KltDP.Examples.FrobeniusProjectivityProved

/-!
# Actual source Picard classes surject onto original target Weil classes

The original source is regular, so each source Weil divisor has its existing
actual Cartier representative. Its actual O(D) Picard class has the required
Weil image. The original birational class pushforward is surjective, hence so
is this composite from the actual source Picard group. No target regularity,
source coordinate generation, Picard rank or class-group splitting is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentrePicardPushforwardSurjective

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreGraphExceptionalPairing
open FrobeniusMultiCentreCanonicalWeilRepresentatives FrobeniusProjectivityProved

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))
    {Y : NormalProjectiveSurface k}
    (π : (sourceSurface q n a ha hproj).toScheme ⟶ Y.toScheme) [IsProper π]
    (hbir : IsBirationalScheme π)

/-- The existing one-way class map followed by the original birational pushforward. -/
def sourcePicardPushforward : Additive (multiSurface (q + 1) n a).Pic →+ Y.WeilClassGroup :=
  (BirationalWeilClassPushforward.pushforward
    (S := sourceSurface q n a ha hproj) (X := Y) π hbir).comp
    (sourceSurface q n a ha hproj).picardToWeilClassHom

/-- Every original target Weil class comes from an actual original source Picard class. -/
theorem sourcePicardPushforward_surjective :
    Function.Surjective (sourcePicardPushforward q n a ha hproj π hbir) := by
  intro c
  obtain ⟨w, hw⟩ := BirationalWeilClassSurjectivity.pushforward_surjective
    (S := sourceSurface q n a ha hproj) (X := Y) π hbir c
  obtain ⟨D, hD⟩ := (sourceSurface q n a ha hproj).weilClassMap_surjective w
  let E : CartierDivisor (sourceSurface q n a ha hproj).toScheme :=
    ((sourceSurface q n a ha hproj).regularCartierWeilEquiv
      (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)).symm D
  have hE : (sourceSurface q n a ha hproj).cartierToWeilHom E = D :=
    ((sourceSurface q n a ha hproj).regularCartierWeilEquiv
      (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)).apply_symm_apply D
  have hclass : (sourceSurface q n a ha hproj).picardToWeilClassHom
      (cartierPicardHom (sourceSurface q n a ha hproj).toScheme E) = w :=
    ((sourceSurface q n a ha hproj).picardToWeilClassHom_cartierPicardHom E).trans
      ((congrArg (sourceSurface q n a ha hproj).weilClassMap hE).trans hD)
  refine ⟨cartierPicardHom (sourceSurface q n a ha hproj).toScheme E, ?_⟩
  exact (congrArg (BirationalWeilClassPushforward.pushforward
    (S := sourceSurface q n a ha hproj) (X := Y) π hbir) hclass).trans hw

/-- Original source projectivity is supplied by its existing producer. -/
theorem original_sourcePicardPushforward_surjective
    {Y : NormalProjectiveSurface k}
    (π : (sourceSurface q n a ha
      (originalMultiStructureProjective k (q + 1) n a)).toScheme ⟶ Y.toScheme)
    [IsProper π] (hbir : IsBirationalScheme π) :
    Function.Surjective (sourcePicardPushforward q n a ha
      (originalMultiStructureProjective k (q + 1) n a) π hbir) :=
  sourcePicardPushforward_surjective q n a ha
    (originalMultiStructureProjective k (q + 1) n a) π hbir

end KltDP.Examples.FrobeniusMultiCentrePicardPushforwardSurjective

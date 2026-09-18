import KltDP.Examples.FrobeniusMultiCentrePicardGenerationOverBase
import KltDP.Examples.FrobeniusMultiCentrePicardRulingPullback
import KltDP.Examples.ProjectiveLineProductPicardGeneration
import KltDP.Examples.FrobeniusMultiCentrePicardCoordinates

/-!
# Generation and the actual Picard-coordinate equivalence of the original source

The original multi-centre global support theorem reduces an arbitrary
class to the original product plus actual exceptional classes. The proved
two-ruling generation of that product and the original pullback identities
then prove surjectivity of the original realization. The accepted original
intersection coordinates become its two-sided inverse. No Picard generation,
rank, or numerical replacement is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentrePicardGeneration

open KltDP.Geometry
open FrobeniusMultiCentreSurface FrobeniusProjectivityProved
open FrobeniusMultiCentrePicardRealization FrobeniusMultiCentrePicardCoordinates
open FrobeniusMultiCentrePicardGenerationOverBase FrobeniusMultiCentrePicardRulingPullback

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)

include ha in
/-- Every actual source Picard class is realized by the original integral vector map. -/
theorem realization_surjective : Function.Surjective (realization q n a) := by
  intro c
  obtain ⟨b, v, hc⟩ := exists_base_and_realization q n a ha c
  obtain ⟨x, y, hb⟩ := ProjectiveLineProductPicardGeneration.picardClass_eq_zsmul_fibers b
  have hbase : (schemePicardPullbackHom (multiProjection (q + 1) n a)).toAdditive b =
      realization q n a (x • FrobeniusPicard.a + y • FrobeniusPicard.b) := by
    simp only [hb, map_add, map_zsmul, firstFiberClass_pullback q n a,
      secondFiberClass_pullback q n a]
  refine ⟨x • FrobeniusPicard.a + y • FrobeniusPicard.b + v, ?_⟩
  calc
    realization q n a (x • FrobeniusPicard.a + y • FrobeniusPicard.b + v) =
        realization q n a (x • FrobeniusPicard.a + y • FrobeniusPicard.b) +
          realization q n a v := map_add (realization q n a) _ _
    _ = (schemePicardPullbackHom (multiProjection (q + 1) n a)).toAdditive b +
        realization q n a v := congrArg (fun z => z + realization q n a v) hbase.symm
    _ = c := hc.symm

variable [Fact (q + 1).Prime] [CharP k (q + 1)]
    (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The original intersection coordinates now recover every original source Picard class. -/
theorem realization_coordinates (c : Additive (multiSurface (q + 1) n a).Pic) :
    realization q n a (coordinates q n a ha hproj c) = c := by
  obtain ⟨v, rfl⟩ := realization_surjective q n a ha c
  rw [coordinates_realization]

/-- The equivalence uses exactly the existing realization and intersection-coordinate maps. -/
def realizationEquiv : FrobeniusPicard.PicardVector (q + 1) n ≃+
    Additive (multiSurface (q + 1) n a).Pic where
  toFun := realization q n a
  invFun := coordinates q n a ha hproj
  left_inv := coordinates_realization q n a ha hproj
  right_inv := realization_coordinates q n a ha hproj
  map_add' := map_add (realization q n a)

/-- Original projectivity is supplied in the actual Picard-coordinate equivalence. -/
def originalPicardEquiv : FrobeniusPicard.PicardVector (q + 1) n ≃+
    Additive (multiSurface (q + 1) n a).Pic :=
  realizationEquiv q n a ha (originalMultiStructureProjective k (q + 1) n a)

end KltDP.Examples.FrobeniusMultiCentrePicardGeneration

import KltDP.Examples.FrobeniusNormalFactorBlockData
import KltDP.Geometry.GeneratedCompleteSystemNormalFactorPoints

/-!
# Actual field points for every original contracting block

Fix the original chosen generated power, with its actual positive section
dimension and global generation. Every original graph, strict fiber and
reduced old chain factors through a field point of that same actual normal
factor, retaining the original field triangle.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusNormalFactorBlockPoints

open KltDP.Geometry FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusProjectivityProved FrobeniusMultiCentreSemiampleConstruction
  FrobeniusContractingNullRestriction FrobeniusContractingBlockSupports
  InvertibleSheafSectionPowers CompleteLinearSystemSections

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)

local instance normalFactorSource_isProper : IsProper (multiStructure (q + 1) n a) :=
  (originalMultiStructureProjective k (q + 1) n a).isProper

/-- Each original block has a genuine point factorization for the actual
normal map of the same chosen generated power. -/
theorem exists_block_point (m : ℕ)
    (hpos : 0 < dimension (multiStructure (q + 1) n a) (power (originalLine q n a ha) m))
    (hG : Positivity.IsGloballyGenerated (power (originalLine q n a ha) m).obj)
    (r : BlockIndex n) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    ∃ z : Spec (CommRingCat.of k) ⟶ GeneratedCompleteSystemNormalFactor.target
        (multiStructure (q + 1) n a) (power (originalLine q n a ha) m) hpos hG,
      blockMorphism q n a ha r ≫ GeneratedCompleteSystemNormalFactor.fromSource
          (multiStructure (q + 1) n a) (power (originalLine q n a ha) m) hpos hG =
        blockStructure q n a ha r ≫ z ∧
      z ≫ GeneratedCompleteSystemNormalFactor.structureMorphism
          (multiStructure (q + 1) n a) (power (originalLine q n a ha) m) hpos hG = 𝟙 _ := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  exact GeneratedCompleteSystemNormalFactor.exists_point_of_trivial_pullback
    (multiStructure (q + 1) n a) (power (originalLine q n a ha) m) hpos hG
    (blockStructure q n a ha r) (blockMorphism q n a ha r) rfl
    (blockPowerRestrictionUnitIso q n a ha m r)

end KltDP.Examples.FrobeniusNormalFactorBlockPoints

import KltDP.Examples.FrobeniusContractingNullPowers
import KltDP.Examples.FrobeniusContractingConnectedBlocks
import KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

/-!
# Original block maps and frames for the normal-factor point construction

The sources are the existing graph, strict fibers, and reduced old chains.
Their actual inclusions, field structures, and power-restriction frames
are assembled without replacing a reducible chain by a prime curve.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusNormalFactorBlockPoints

open KltDP.Geometry FrobeniusMultiCentreSurface FrobeniusMultiCentreGraphFiber
  FrobeniusMultiCentreOldChain FrobeniusContractingNullRestriction
  FrobeniusContractingBlockSupports FrobeniusContractingLocusPieces
  FrobeniusContractingNullPowers FrobeniusProjectivityProved
  FrobeniusMultiCentreSemiampleConstruction InvertibleSheafSectionPowers

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)

/-- The actual original inclusions, indexed by the original block labels. -/
def blockMorphism : (r : BlockIndex n) →
    blockScheme q n a ha r ⟶ multiSurface (q + 1) n a
  | none => graphStrictι (q + 1) n a
  | some (.inl i) => fiberStrictι (q + 1) n a i
  | some (.inr i) => oldChainInclusion q n a ha i

instance blockMorphism_isClosedImmersion (r : BlockIndex n) :
    IsClosedImmersion (blockMorphism q n a ha r) := by
  cases r with
  | none =>
      change IsClosedImmersion (graphStrictι (q + 1) n a)
      infer_instance
  | some r =>
      cases r with
      | inl i =>
          change IsClosedImmersion (fiberStrictι (q + 1) n a i)
          infer_instance
      | inr i =>
          change IsClosedImmersion (oldChainInclusion q n a ha i)
          infer_instance

/-- These maps have exactly the independently defined original block supports. -/
theorem range_blockMorphism (r : BlockIndex n) :
    Set.range (blockMorphism q n a ha r).base = blockSupport q n a r := by
  cases r with
  | none => rfl
  | some r =>
      cases r with
      | inl i => rfl
      | inr i => exact range_oldChainInclusion q n a ha i

private theorem blockScheme_reduced_connected (r : BlockIndex n) :
    IsReduced (blockScheme q n a ha r) ∧ ConnectedSpace (blockScheme q n a ha r) := by
  cases r with
  | none =>
      change IsReduced (graphStrict (q + 1) n a) ∧ ConnectedSpace (graphStrict (q + 1) n a)
      letI := graphStrict_isIntegral (q + 1) n a
      exact ⟨inferInstance, inferInstance⟩
  | some r =>
      cases r with
      | inl i =>
          change IsReduced (fiberStrict (q + 1) n a i) ∧
            ConnectedSpace (fiberStrict (q + 1) n a i)
          letI := fiberStrict_isIntegral (q + 1) n a i
          exact ⟨inferInstance, inferInstance⟩
      | inr i =>
          change IsReduced (oldChain q n a ha i) ∧ ConnectedSpace (oldChain q n a ha i)
          exact ⟨inferInstance, inferInstance⟩

instance blockScheme_isReduced (r : BlockIndex n) : IsReduced (blockScheme q n a ha r) :=
  (blockScheme_reduced_connected q n a ha r).1

instance blockScheme_connectedSpace (r : BlockIndex n) :
    ConnectedSpace (blockScheme q n a ha r) :=
  (blockScheme_reduced_connected q n a ha r).2

/-- The original field structure induced by the actual block inclusion. -/
def blockStructure (r : BlockIndex n) : blockScheme q n a ha r ⟶ Spec (CommRingCat.of k) :=
  blockMorphism q n a ha r ≫ multiStructure (q + 1) n a

instance blockStructure_isProper (r : BlockIndex n) : IsProper (blockStructure q n a ha r) := by
  letI : IsProper (multiStructure (q + 1) n a) :=
    (originalMultiStructureProjective k (q + 1) n a).isProper
  dsimp only [blockStructure]
  infer_instance

/-- Every chosen original power has an actual unit frame on each original block. -/
def blockPowerRestrictionUnitIso (m : ℕ) : (r : BlockIndex n) →
    (pullbackInvertibleSheaf (blockMorphism q n a ha r)
      (power (originalLine q n a ha) m)).obj ≅
        _root_.SheafOfModules.unit (blockScheme q n a ha r).ringCatSheaf
  | none => graphPowerRestrictionUnitIso q n a ha
      (originalMultiStructureProjective k (q + 1) n a) m
  | some (.inl i) => fiberPowerRestrictionUnitIso q n a ha
      (originalMultiStructureProjective k (q + 1) n a) i m
  | some (.inr i) => oldChainPowerRestrictionUnitIso q n a ha
      (originalMultiStructureProjective k (q + 1) n a) i m

/-- The existing null-locus factor recovers exactly the same original inclusion. -/
@[reassoc] theorem blockToNullLocus_comp (hn : 2 < n) (r : BlockIndex n) :
    blockToNullLocus q n a ha (originalMultiStructureProjective k (q + 1) n a) hn r ≫
      Positivity.nullLocusInclusion (multiStructure (q + 1) n a) (originalLine q n a ha) =
        blockMorphism q n a ha r := by
  cases r with
  | none =>
      exact graphToNullLocus_comp q n a ha
        (originalMultiStructureProjective k (q + 1) n a) hn
  | some r =>
      cases r with
      | inl i =>
          exact fiberToNullLocus_comp q n a ha
            (originalMultiStructureProjective k (q + 1) n a) hn i
      | inr i =>
          exact oldChainToNullLocus_comp q n a ha
            (originalMultiStructureProjective k (q + 1) n a) hn i

end KltDP.Examples.FrobeniusNormalFactorBlockPoints

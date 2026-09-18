import KltDP.Examples.FrobeniusContractingLocusPieces
import KltDP.Examples.FrobeniusContractingBlockCover
import KltDP.Examples.FrobeniusContractingOldChainRestriction
import KltDP.Geometry.ClosedPartitionUnitTriviality

/-!
# The actual contracting line is trivial on its entire reduced null locus

The graph, strict special fibers and reduced old exceptional chains are
actual closed subschemes of the independently defined null locus. Their
proved disjointness and covering property give a finite closed partition.
The original restriction frames therefore glue to a frame on the whole
null locus. This constructs that frame without assuming a contraction or
semiampleness of the line on the ambient surface.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Examples.FrobeniusContractingNullRestriction

open KltDP.Geometry FrobeniusMultiCentreSurface FrobeniusMultiCentreGraphFiber
open FrobeniusMultiCentreContractingNef FrobeniusMultiCentreContractingRestrictions
open FrobeniusMultiCentreOldChain FrobeniusContractingOldChainRestriction
open FrobeniusContractingLocusPieces FrobeniusContractingBlockSupports
open FrobeniusContractingBlockCover

private def unitIso_of_factor {X Y Z : Scheme.{u}}
    (i : Y ⟶ Z) (j : Z ⟶ X) (g : Y ⟶ X) (h : i ≫ j = g)
    (M : X.Modules)
    (e : (schemeModulePullback g).obj M ≅ _root_.SheafOfModules.unit Y.ringCatSheaf) :
    (schemeModulePullback i).obj ((schemeModulePullback j).obj M) ≅
      _root_.SheafOfModules.unit Y.ringCatSheaf :=
  (schemeModulePullbackCompIso i j).app M ≪≫
    eqToIso (congrArg (fun f => (schemeModulePullback f).obj M) h) ≪≫ e

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))
  (hn : 2 < n)

/-- The original schemes constituting the contracting blocks. -/
def blockScheme : BlockIndex n → Scheme.{u}
  | none => graphStrict (q + 1) n a
  | some (.inl i) => fiberStrict (q + 1) n a i
  | some (.inr i) => oldChain q n a ha i

/-- The original block maps into the independently defined reduced null locus. -/
def blockToNullLocus : (r : BlockIndex n) → blockScheme q n a ha r ⟶
    Positivity.nullLocusScheme (multiStructure (q + 1) n a) (contractingLine q n a ha hproj)
  | none => graphToNullLocus q n a ha hproj hn
  | some (.inl i) => fiberToNullLocus q n a ha hproj hn i
  | some (.inr i) => oldChainToNullLocus q n a ha hproj hn i

instance blockToNullLocus_isClosedImmersion (r : BlockIndex n) :
    IsClosedImmersion (blockToNullLocus q n a ha hproj hn r) := by
  cases r with
  | none =>
      change IsClosedImmersion (graphToNullLocus q n a ha hproj hn)
      infer_instance
  | some r =>
      cases r with
      | inl i =>
          change IsClosedImmersion (fiberToNullLocus q n a ha hproj hn i)
          infer_instance
      | inr i =>
          change IsClosedImmersion (oldChainToNullLocus q n a ha hproj hn i)
          infer_instance

/-- Each block has exactly the original support inside the actual null locus. -/
theorem range_blockToNullLocus (r : BlockIndex n) :
    Set.range (blockToNullLocus q n a ha hproj hn r).base =
      (Positivity.nullLocusInclusion (multiStructure (q + 1) n a)
        (contractingLine q n a ha hproj)).base ⁻¹' blockSupport q n a r := by
  cases r with
  | none => exact range_graphToNullLocus q n a ha hproj hn
  | some r =>
      cases r with
      | inl i => exact range_fiberToNullLocus q n a ha hproj hn i
      | inr i => exact range_oldChainToNullLocus q n a ha hproj hn i

/-- The original frames, transported through the proved original factorizations. -/
def blockRestrictionUnitIso : (r : BlockIndex n) →
    (schemeModulePullback (blockToNullLocus q n a ha hproj hn r)).obj
      (pullbackInvertibleSheaf
        (Positivity.nullLocusInclusion (multiStructure (q + 1) n a)
          (contractingLine q n a ha hproj)) (contractingLine q n a ha hproj)).obj ≅
            _root_.SheafOfModules.unit (blockScheme q n a ha r).ringCatSheaf
  | none => unitIso_of_factor _ _ _ (graphToNullLocus_comp q n a ha hproj hn) _
      (graphRestrictionUnitIso q n a ha hproj)
  | some (.inl i) => unitIso_of_factor _ _ _ (fiberToNullLocus_comp q n a ha hproj hn i) _
      (fiberRestrictionUnitIso q n a ha hproj i)
  | some (.inr i) => unitIso_of_factor _ _ _ (oldChainToNullLocus_comp q n a ha hproj hn i) _
      (oldChainRestrictionUnitIso q n a ha hproj i)

/-- The actual contracting line has an actual unit frame on its entire
independently defined reduced null-locus scheme. -/
def contractingNullRestrictionUnitIso :
    (pullbackInvertibleSheaf
      (Positivity.nullLocusInclusion (multiStructure (q + 1) n a)
        (contractingLine q n a ha hproj)) (contractingLine q n a ha hproj)).obj ≅
          _root_.SheafOfModules.unit
            (Positivity.nullLocusScheme (multiStructure (q + 1) n a)
              (contractingLine q n a ha hproj)).ringCatSheaf := by
  classical
  let Y : ULift.{u} (BlockIndex n) → Scheme.{u} := fun r => blockScheme q n a ha r.down
  let i := fun r : ULift.{u} (BlockIndex n) => blockToNullLocus q n a ha hproj hn r.down
  have hdisj : ∀ r s, r ≠ s → Disjoint (Set.range (i r).base) (Set.range (i s).base) := by
    intro r s hrs
    have hrs' : r.down ≠ s.down := fun h => hrs (ULift.ext r s h)
    have h := blockSupport_pairwise q n a ha hrs'
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hx' := (congrArg (fun T => x ∈ T)
      (range_blockToNullLocus q n a ha hproj hn r.down)).mp hx
    have hy' := (congrArg (fun T => x ∈ T)
      (range_blockToNullLocus q n a ha hproj hn s.down)).mp hy
    exact (Set.disjoint_left.mp h) hx' hy'
  have hcover : ∀ x, ∃ r, x ∈ Set.range (i r).base := by
    intro x
    obtain ⟨r, hr⟩ := nullLocus_point_mem_block q n a ha hproj hn x
    refine ⟨ULift.up r, ?_⟩
    exact (congrArg (fun T => x ∈ T)
      (range_blockToNullLocus q n a ha hproj hn r)).mpr hr
  exact ClosedPartitionUnitTriviality.unitIsoOfClosedPartition Y i hdisj hcover
    (pullbackInvertibleSheaf
      (Positivity.nullLocusInclusion (multiStructure (q + 1) n a)
        (contractingLine q n a ha hproj)) (contractingLine q n a ha hproj))
    (fun r => blockRestrictionUnitIso q n a ha hproj hn r.down)

end KltDP.Examples.FrobeniusContractingNullRestriction

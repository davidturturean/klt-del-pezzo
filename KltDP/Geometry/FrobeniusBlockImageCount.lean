import KltDP.Examples.FrobeniusNormalFactorBlockData
import KltDP.Examples.FrobeniusContractingConnectedComponentCount
import KltDP.Geometry.PrimeCurvePointFiberFactorization
import KltDP.Geometry.ClosedImmersionFiberConnected
import KltDP.Topology.ConnectedPartitionImages

/-!
The actual graph, strict-fiber and old-chain blocks give exactly 2n+1
distinct image points once their original point factorizations and the
original fiber exhaustion are supplied. Connectedness is transported to
the actual reduced null-locus scheme through its original closed immersion.
The image is proved finite before its natural cardinality is evaluated.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.FrobeniusBlockImageCount

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusProjectivityProved
  FrobeniusMultiCentreSemiampleConstruction FrobeniusNormalFactorBlockPoints
  FrobeniusContractingNullRestriction FrobeniusContractingBlockSupports
  FrobeniusContractingConnectedBlocks

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)

/-- Count the original distinct image points from the actual closed blocks
and the original point fibers, without assuming any image-point bijection. -/
theorem image_nullLocus_finite_card (hn : 2 < n) {Y : Scheme.{u}}
    (π : multiSurface (q + 1) n a ⟶ Y)
    (point : BlockIndex n → (Spec (CommRingCat.of k) ⟶ Y))
    (hpoint : ∀ r, blockMorphism q n a ha r ≫ π = blockStructure q n a ha r ≫ point r)
    (hsaturated : π.base ⁻¹' (π.base '' Positivity.nullLocus
        (multiStructure (q + 1) n a) (originalLine q n a ha)) =
      Positivity.nullLocus (multiStructure (q + 1) n a) (originalLine q n a ha))
    (hconnected : ∀ y : Y, IsConnected (π.base ⁻¹' {y})) :
    (π.base '' Positivity.nullLocus (multiStructure (q + 1) n a)
      (originalLine q n a ha)).Finite ∧
    Nat.card (π.base '' Positivity.nullLocus (multiStructure (q + 1) n a)
      (originalLine q n a ha)) = 2 * n + 1 := by
  let H := originalMultiStructureProjective k (q + 1) n a
  let E := Positivity.nullLocusScheme (multiStructure (q + 1) n a) (originalLine q n a ha)
  let ι : E ⟶ multiSurface (q + 1) n a :=
    Positivity.nullLocusInclusion (multiStructure (q + 1) n a) (originalLine q n a ha)
  let fE : E ⟶ Y := ι ≫ π
  let Z : BlockIndex n → Set E := fun r => Set.range (blockToNullLocus q n a ha H hn r).base
  have hclosed : ∀ r, IsClosed (Z r) := blockRange_isClosed q n a ha H hn
  have hne : ∀ r, (Z r).Nonempty := fun r => (blockRange_isConnected q n a ha H hn r).nonempty
  have hdisj : Pairwise (fun r s => Disjoint (Z r) (Z s)) :=
    blockRange_pairwise q n a ha H hn
  have hcover : ⋃ r, Z r = Set.univ := iUnion_blockRange q n a ha H hn
  have hι : Set.range ι.base = Positivity.nullLocus
      (multiStructure (q + 1) n a) (originalLine q n a ha) :=
    (Scheme.IdealSheafData.vanishingIdeal (Positivity.nullLocusClosed
      (multiStructure (q + 1) n a) (originalLine q n a ha))).range_gluedTo
  have himage : Set.range fE.base = π.base '' Positivity.nullLocus
      (multiStructure (q + 1) n a) (originalLine q n a ha) := by
    change Set.range (π.base ∘ ι.base) = _
    rw [Set.range_comp, hι]
  have hconstant : ∀ r, ∀ x ∈ Z r, fE.base x = fieldMorphismPoint (point r) := by
    intro r x hx
    obtain ⟨z, rfl⟩ := hx
    have hfactor : blockToNullLocus q n a ha H hn r ≫ fE =
        blockStructure q n a ha r ≫ point r := by
      dsimp only [fE, ι]
      rw [← Category.assoc, blockToNullLocus_comp, hpoint]
    exact PrimeCurvePointFiberFactorization.base_eq_of_factor
      (blockStructure q n a ha r) _ (point r) hfactor z
  have hfcover : ∀ y ∈ Set.range fE.base, π.base ⁻¹' {y} ⊆ Set.range ι.base := by
    intro y hy x hx
    have hyimage : y ∈ π.base '' Positivity.nullLocus
        (multiStructure (q + 1) n a) (originalLine q n a ha) := by
      rw [← himage]
      exact hy
    have hximage : x ∈ π.base ⁻¹' (π.base '' Positivity.nullLocus
        (multiStructure (q + 1) n a) (originalLine q n a ha)) := by
      change π.base x ∈ π.base '' Positivity.nullLocus
        (multiStructure (q + 1) n a) (originalLine q n a ha)
      change π.base x = y at hx
      rw [hx]
      exact hyimage
    rw [hsaturated] at hximage
    rw [hι]
    exact hximage
  have hpre : ∀ y : Y, IsPreconnected (fE.base ⁻¹' {y}) :=
    ClosedImmersionFiberConnected.all_pointFibers_isPreconnected ι π hfcover hconnected
  have hfinite : (Set.range fE.base).Finite :=
    KltDP.Topology.ConnectedPartitionImages.range_finite Z hne hcover fE.base
      (fun r => fieldMorphismPoint (point r)) hconstant
  have hcard : Nat.card (Set.range fE.base) = Nat.card (BlockIndex n) :=
    KltDP.Topology.ConnectedPartitionImages.natCard_range Z hclosed hne hdisj hcover fE.base
      (fun r => fieldMorphismPoint (point r)) hconstant hpre
  rw [himage] at hfinite hcard
  refine ⟨hfinite, hcard.trans ?_⟩
  simp [BlockIndex, Nat.card_eq_fintype_card, two_mul]

end KltDP.Geometry.FrobeniusBlockImageCount

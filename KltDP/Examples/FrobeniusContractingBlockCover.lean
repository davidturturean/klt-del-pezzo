import KltDP.Examples.FrobeniusContractingBlockSupports
import KltDP.Examples.FrobeniusMultiCentreContractingNullLocus

/-!
# The original blocks cover the actual null-locus scheme

The previously computed exact support is the finite union of the original
block supports. Consequently every point of the independently defined
reduced null-locus scheme belongs to one original block. The proof uses
the actual null-locus inclusion and its verified range.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Examples.FrobeniusContractingBlockCover

open KltDP.Geometry FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusMultiCentreContractingNef FrobeniusMultiCentreContractingNullLocus
open FrobeniusContractingBlockSupports

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The exact contracting support is the union of the original labeled blocks. -/
theorem contractingSupport_eq_iUnion_blocks :
    contractingSupport q n a ha hproj = ⋃ r : BlockIndex n, blockSupport q n a r := by
  ext x
  constructor
  · rintro ((hx | hx) | hx)
    · exact Set.mem_iUnion.mpr ⟨none, hx⟩
    · obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨some (.inl i), hx⟩
    · obtain ⟨i, j, hx⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion.mpr ⟨some (.inr i), Set.mem_iUnion.mpr ⟨j, hx⟩⟩
  · intro hx
    obtain ⟨r, hx⟩ := Set.mem_iUnion.mp hx
    cases r with
    | none => exact Or.inl (Or.inl hx)
    | some r =>
        cases r with
        | inl i => exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩))
        | inr i => exact Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩)

/-- Every point of the actual reduced null locus lies over one original block. -/
theorem nullLocus_point_mem_block (hn : 2 < n)
    (x : Positivity.nullLocusScheme (multiStructure (q + 1) n a)
      (contractingLine q n a ha hproj)) :
    ∃ r : BlockIndex n,
      (Positivity.nullLocusInclusion (multiStructure (q + 1) n a)
        (contractingLine q n a ha hproj)).base x ∈ blockSupport q n a r := by
  have hx : (Positivity.nullLocusInclusion (multiStructure (q + 1) n a)
      (contractingLine q n a ha hproj)).base x ∈ contractingSupport q n a ha hproj :=
    (nullLocusInclusion_range q n a ha hproj hn) ▸ ⟨x, rfl⟩
  have h := congrArg (fun T : Set (multiSurface (q + 1) n a) =>
    (Positivity.nullLocusInclusion (multiStructure (q + 1) n a)
      (contractingLine q n a ha hproj)).base x ∈ T)
    (contractingSupport_eq_iUnion_blocks q n a ha hproj)
  exact Set.mem_iUnion.mp (h.mp hx)

end KltDP.Examples.FrobeniusContractingBlockCover

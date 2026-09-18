import KltDP.Examples.FrobeniusExceptionalLocusCover

/-!
# The original second ruling and the existing special-fibre components

The accepted `FrobeniusExceptionalLocusCover.specialFiberSSupport_eq_components`
already decomposes the actual special fibre into its strict tangent fibre and all
embedded exceptional components. This file identifies that support with the
preimage of the original point under the original second-ruling map, and records
the resulting finite-component alternative for an irreducible subset.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusMultiCentreRulingFibers

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusGraphClosed
  FrobeniusGraphPicardClassZeroFiber FrobeniusMultiCentreGraphContacts
  FrobeniusExceptionalFinalConfiguration FrobeniusMultiCentreSurface
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphFiber
  FrobeniusSpecialFiberSPn FrobeniusExceptionalLocusCover

variable {k : Type u} [Field k]

/-- The original horizontal fibre is precisely the fibre of the second projection
over its specified rational point. -/
theorem range_horizontalFiberMorphism_eq (c : k) :
    Set.range (horizontalFiberMorphism c).base =
      (secondProjection (k := k)).base ⁻¹' {point c} := by
  rw [← horizontalFiberIso_hom_fst c, range_iso_comp_base,
    Scheme.Pullback.range_fst, range_fieldMorphism]
  rfl

variable (q n : ℕ) (a : Fin n → k)
variable [IsAlgClosed k] [Fact (q + 1).Prime] [CharP k (q + 1)]
variable (ha : Function.Injective a)
include ha

/-- The actual second ruling has exactly the accepted strict and exceptional
supports over each selected height. No projectivity hypothesis is needed. -/
theorem secondRuling_special_preimage (i : Fin n) :
    (multiProjection (q + 1) n a ≫ secondProjection).base ⁻¹'
        {point (a i ^ (q + 1))} =
      Set.range (fiberStrictι (q + 1) n a i).base ∪
        ⋃ idx : FinalIndex.{0} q, exceptionalSupport q n a i idx := by
  change (multiProjection (q + 1) n a).base ⁻¹'
    ((secondProjection (k := k)).base ⁻¹' {point (a i ^ (q + 1))}) = _
  rw [← range_horizontalFiberMorphism_eq, ← specialFiberSSupport_eq]
  exact specialFiberSSupport_eq_components q n a ha i

/-- The same component list for the literal scheme fibre of the original ruling. -/
theorem secondRuling_special_fiber_support (i : Fin n) :
    Set.range (pullback.fst (multiProjection (q + 1) n a ≫ secondProjection)
      (pointMorphism (a i ^ (q + 1)))).base =
      Set.range (fiberStrictι (q + 1) n a i).base ∪
        ⋃ idx : FinalIndex.{0} q, exceptionalSupport q n a i idx := by
  rw [Scheme.Pullback.range_fst, range_fieldMorphism]
  exact secondRuling_special_preimage q n a ha i

/-- An irreducible subset lying over a selected height is contained in the
original strict fibre or in one of the original embedded exceptional components. -/
theorem irreducible_subset_special_fiber (i : Fin n)
    (T : Set (multiSurface (q + 1) n a)) (hT : IsIrreducible T)
    (hTi : T ⊆ (multiProjection (q + 1) n a ≫ secondProjection).base ⁻¹'
      {point (a i ^ (q + 1))}) :
    T ⊆ Set.range (fiberStrictι (q + 1) n a i).base ∨
      ∃ idx : FinalIndex.{0} q, T ⊆ exceptionalSupport q n a i idx := by
  classical
  rw [secondRuling_special_preimage q n a ha i] at hTi
  obtain hF | hE := isPreirreducible_iff_isClosed_union_isClosed.mp hT.2
    _ _ (fiberStrictι (q + 1) n a i).isClosedEmbedding.isClosed_range
    (isClosed_iUnion_of_finite fun idx => exceptionalSupport_isClosed q n a i idx) hTi
  · exact Or.inl hF
  · right
    obtain ⟨z, hz, hTz⟩ := isIrreducible_iff_sUnion_isClosed.mp hT
      (Finset.univ.image fun idx : FinalIndex.{0} q => exceptionalSupport q n a i idx)
      (fun z hz => by
        obtain ⟨idx, -, rfl⟩ := Finset.mem_image.mp hz
        exact exceptionalSupport_isClosed q n a i idx)
      (fun x hx => by
        obtain ⟨idx, hidx⟩ := Set.mem_iUnion.mp (hE hx)
        exact Set.mem_sUnion.mpr
          ⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem
            (fun idx : FinalIndex.{0} q => exceptionalSupport q n a i idx)
            (Finset.mem_univ idx)), hidx⟩)
    obtain ⟨idx, -, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨idx, hTz⟩

end KltDP.Examples.FrobeniusMultiCentreRulingFibers

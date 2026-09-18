import KltDP.Geometry.SplitAmbientPullbackCopies

/-!
# Both actual copies exhaust the original pullback

The original splitting and the actual scheme coproduct topology give
coverage by the two labeled copies. Their ambient ranges exhaust the
range of the original first pullback projection. For a nonempty original
curve included by a preimmersion, the two actual ambient maps are distinct.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.SplitAmbientPullbackCopyRanges

open SplitAmbientPullbackCopies QuadraticAtlasGlobalSplitting

variable {X Z C : Scheme.{u}} (p : Z ⟶ X) (f : C ⟶ X)
    (q : pullback p f ≅ C ⨿ C)

/-- Every actual pullback point belongs to one of the two original labeled copies. -/
theorem copies_cover (z : (pullback p f : Scheme.{u})) :
    ∃ (ε : Bool) (c : C), (copyToPullback p f q ε).base c = z := by
  obtain ⟨s, hs⟩ := (AlgebraicGeometry.coprodMk C C).surjective (q.hom.base z)
  rcases s with c | c
  · refine ⟨false, c, ?_⟩
    apply q.hom.isOpenEmbedding.injective
    change (copyToPullback p f q false ≫ q.hom).base c = q.hom.base z
    rw [copyToPullback_hom]
    simpa only [inclusion, AlgebraicGeometry.coprodMk_inl] using hs
  · refine ⟨true, c, ?_⟩
    apply q.hom.isOpenEmbedding.injective
    change (copyToPullback p f q true ≫ q.hom).base c = q.hom.base z
    rw [copyToPullback_hom]
    simpa only [inclusion, AlgebraicGeometry.coprodMk_inr] using hs

/-- The two labeled ambient ranges retain the entire original pulled-back locus. -/
theorem ambient_ranges_union :
    Set.range (ambientCopy p f q false).base ∪ Set.range (ambientCopy p f q true).base =
      Set.range (pullback.fst p f).base := by
  ext z
  constructor
  · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨(copyToPullback p f q false).base c, rfl⟩
    · exact ⟨(copyToPullback p f q true).base c, rfl⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨ε, c, rfl⟩ := copies_cover p f q w
    cases ε
    · exact Or.inl ⟨c, rfl⟩
    · exact Or.inr ⟨c, rfl⟩

/-- On a nonempty original curve, disjoint ambient images force distinct actual maps. -/
theorem ambientCopy_false_ne_true [Nonempty C] [IsPreimmersion f] :
    ambientCopy p f q false ≠ ambientCopy p f q true := by
  intro h
  obtain ⟨c⟩ := ‹Nonempty C›
  exact (Set.disjoint_left.mp (ambientCopy_disjoint p f q)) ⟨c, rfl⟩
    ⟨c, congrArg (fun m : C ⟶ Z => m.base c) h.symm⟩

/-- The two labels retain two different original ambient maps. -/
theorem ambientCopy_injective [Nonempty C] [IsPreimmersion f] :
    Function.Injective (ambientCopy p f q) := by
  intro ε ε' h
  cases ε <;> cases ε'
  · rfl
  · exact False.elim (ambientCopy_false_ne_true p f q h)
  · exact False.elim (ambientCopy_false_ne_true p f q h.symm)
  · rfl

end KltDP.Geometry.SplitAmbientPullbackCopyRanges

#print axioms KltDP.Geometry.SplitAmbientPullbackCopyRanges.ambient_ranges_union
#print axioms KltDP.Geometry.SplitAmbientPullbackCopyRanges.ambientCopy_injective

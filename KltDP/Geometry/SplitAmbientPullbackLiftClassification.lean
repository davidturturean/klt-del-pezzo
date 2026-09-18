import KltDP.Geometry.SplitAmbientPullbackCopyRanges
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Every actual lift of an integral curve is one of the two split copies

The image of the generic point chooses one labeled component of the
actual split pullback. Its closed range then contains the whole image.
The existing open-immersion lift factors the original map through that
copy; compatibility with the original second projection forces this
factor to be the identity. Thus any original lifted curve map equals
one of the two actual copy maps, including independently constructed
whole-tree component lifts.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.SplitAmbientPullbackLiftClassification

open SplitAmbientPullbackCopies SplitAmbientPullbackCopyRanges QuadraticAtlasGlobalSplitting

variable {X Z C : Scheme.{u}} [IsIntegral C]
    (p : Z ⟶ X) (f : C ⟶ X) (q : pullback p f ≅ C ⨿ C)
    (hq : q.hom ≫ coprod.desc (𝟙 C) (𝟙 C) = pullback.snd p f)

include hq in
/-- Every actual map of the original integral curve above f is one of the original two copy maps. -/
theorem eq_ambientCopy_of_projection (g : C ⟶ Z) (hg : g ≫ p = f) :
    ∃ ε : Bool, g = ambientCopy p f q ε := by
  let r : C ⟶ pullback p f := pullback.lift g (𝟙 C) (by simpa only [Category.id_comp] using hg)
  have hr_snd : r ≫ pullback.snd p f = 𝟙 C := pullback.lift_snd _ _ _
  obtain ⟨ε, c, hc⟩ := copies_cover p f q (r.base (genericPoint C))
  let j : C ⟶ pullback p f := copyToPullback p f q ε
  letI : IsOpenImmersion j := by
    dsimp only [j, copyToPullback]
    cases ε <;> dsimp only [inclusion] <;> infer_instance
  have hsub : Set.range r.base ⊆ Set.range j.base := by
    have hclosed : IsClosed (r.base ⁻¹' Set.range j.base) :=
      j.isClosedEmbedding.isClosed_range.preimage (by fun_prop)
    have hgp : genericPoint C ∈ r.base ⁻¹' Set.range j.base := ⟨c, hc⟩
    have hfull := closure_minimal (Set.singleton_subset_iff.mpr hgp) hclosed
    rw [(genericPoint_spec C).def] at hfull
    rintro _ ⟨x, rfl⟩
    exact hfull (Set.mem_univ x)
  let l : C ⟶ C := IsOpenImmersion.lift j r hsub
  have hl : l ≫ j = r := IsOpenImmersion.lift_fac j r hsub
  have hj : j ≫ pullback.snd p f = 𝟙 C := copyToPullback_snd p f q hq ε
  have hl_id : l = 𝟙 C := by
    calc
      l = l ≫ (j ≫ pullback.snd p f) := by rw [hj, Category.comp_id]
      _ = (l ≫ j) ≫ pullback.snd p f := (Category.assoc _ _ _).symm
      _ = r ≫ pullback.snd p f := by rw [hl]
      _ = 𝟙 C := hr_snd
  have hr : r = j := by rw [← hl, hl_id, Category.id_comp]
  refine ⟨ε, ?_⟩
  have h := congrArg (fun t => t ≫ pullback.fst p f) hr
  simpa only [r, j, pullback.lift_fst, ambientCopy] using h

end KltDP.Geometry.SplitAmbientPullbackLiftClassification

#print axioms KltDP.Geometry.SplitAmbientPullbackLiftClassification.eq_ambientCopy_of_projection

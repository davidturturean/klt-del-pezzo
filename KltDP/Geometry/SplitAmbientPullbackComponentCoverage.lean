import KltDP.Geometry.SplitAmbientPullbackComponentCopies
import KltDP.Geometry.SplitAmbientPullbackCopyRanges
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Both component copies exhaust the actual original component preimage

The two original component images are exactly the inverse image of that
component's image in the original base. Equivalently they exhaust the
range of the first projection of the actual component pullback scheme.
The proof uses the derived splitting over the base and the original
scheme pullback point-surjectivity theorem.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

namespace KltDP.Geometry.SplitAmbientPullbackComponentCoverage

open RationalTreePicard SplitAmbientPullbackCopies SplitAmbientPullbackCopyRanges
open SplitAmbientPullbackComponentCopies

variable {X Z C : Scheme.{u}} [NoetherianSpace C]
    (p : Z ⟶ X) (f : C ⟶ X) (q : pullback p f ≅ C ⨿ C)
    (hq : q.hom ≫ coprod.desc (𝟙 C) (𝟙 C) = pullback.snd p f)

include hq in
/-- The two original copied component images are the entire original component preimage. -/
theorem componentImages_eq_preimage (D : ↥(irreducibleComponents C)) :
    componentImage p f q (false, D) ∪ componentImage p f q (true, D) =
      p.base ⁻¹' (f.base '' (D : Set C)) := by
  rw [componentImage_eq, componentImage_eq]
  ext z
  constructor
  · rintro (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩)
    · refine ⟨c, hc, ?_⟩
      exact (congrArg (fun m : C ⟶ X => m.base c)
        (ambientCopy_projection p f q hq false)).symm
    · refine ⟨c, hc, ?_⟩
      exact (congrArg (fun m : C ⟶ X => m.base c)
        (ambientCopy_projection p f q hq true)).symm
  · rintro ⟨x, hx, hxz⟩
    obtain ⟨w, hwz, hwx⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := p) (g := f) z x hxz.symm
    obtain ⟨ε, c, hc⟩ := copies_cover p f q w
    have hcx : c = x := by
      calc
        c = (pullback.snd p f).base ((copyToPullback p f q ε).base c) :=
          (congrArg (fun m : C ⟶ C => m.base c) (copyToPullback_snd p f q hq ε)).symm
        _ = x := by rw [hc, hwx]
    have hcz : (ambientCopy p f q ε).base c = z := by
      change (pullback.fst p f).base ((copyToPullback p f q ε).base c) = z
      rw [hc, hwz]
    have hcmem : c ∈ (D : Set C) := by rw [hcx]; exact hx
    cases ε
    · exact Or.inl ⟨c, hcmem, hcz⟩
    · exact Or.inr ⟨c, hcmem, hcz⟩

include hq in
/-- They also exhaust precisely the image of the actual original component pullback scheme. -/
theorem componentImages_eq_range_pullback (D : ↥(irreducibleComponents C)) :
    componentImage p f q (false, D) ∪ componentImage p f q (true, D) =
      Set.range (pullback.fst p (componentUnionInclusion C {D} ≫ f)).base := by
  rw [componentImages_eq_preimage p f q hq D, Scheme.Pullback.range_fst]
  change p.base ⁻¹' (f.base '' (D : Set C)) =
    p.base ⁻¹' Set.range (f.base ∘ (componentUnionInclusion C {D}).base)
  rw [Set.range_comp, range_componentUnionInclusion, coe_componentClosedUnion_singleton]

end KltDP.Geometry.SplitAmbientPullbackComponentCoverage

#print axioms KltDP.Geometry.SplitAmbientPullbackComponentCoverage.componentImages_eq_range_pullback

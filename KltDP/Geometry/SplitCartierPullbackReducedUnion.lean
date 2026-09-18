import KltDP.Geometry.CartierPullbackClosedFiber
import KltDP.Geometry.SplitAmbientPullbackCopyRanges
import KltDP.Geometry.RationalTreePicardComponentIntersectionReduced

/-!
# A split actual Cartier inverse image is the reduced union of its two actual copies

The existing general Cartier closed-fiber theorem identifies the actual
pulled Cartier ideal with the original categorical pullback's kernel.
An actual splitting makes that pullback reduced. The proved coverage
by the two labeled original ambient maps therefore identifies the
actual pulled ideal with their reduced closed union ideal.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

namespace KltDP.Geometry.SplitCartierPullbackReducedUnion

open SplitAmbientPullbackCopies SplitAmbientPullbackCopyRanges

private theorem reduced_coprod (C : Scheme.{u}) [IsReduced C] : IsReduced (C ⨿ C) := by
  letI : ∀ i, IsReduced ((coprodOpenCover.{u, u} C C).obj i) := by
    rintro (i | i) <;> exact inferInstanceAs (IsReduced C)
  exact IsReduced.of_openCover (coprodOpenCover.{u, u} C C)

variable {X Y C : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsReduced C]
    (π : X ⟶ Y) [GenericPointPreserving π] [QuasiCompact π]
    (i : C ⟶ Y) [IsClosedImmersion i] (q : pullback π i ≅ C ⨿ C)

/-- The literal union of the two original ambient-copy ranges. -/
def copyUnion : Closeds X :=
  ⟨Set.range (ambientCopy π i q false).base ∪ Set.range (ambientCopy π i q true).base,
    (ambientCopy π i q false).isClosedEmbedding.isClosed_range.union
      (ambientCopy π i q true).isClosedEmbedding.isClosed_range⟩

/-- The actual pullback of the Cartier center has the reduced union ideal of its two actual copies. -/
theorem pullbackIdealData_eq_copyUnion
    (D : CartierDivisor Y) (hD : HasRegularCartierEquations Y D)
    (hI : effectiveCartierIdealDataOfRegularEquations Y D hD = i.ker) :
    pullbackIdealData π D hD = Scheme.IdealSheafData.vanishingIdeal (copyUnion π i q) := by
  letI : IsReduced (C ⨿ C) := reduced_coprod C
  letI : IsReduced (pullback π i) := isReduced_of_isOpenImmersion q.hom
  letI : IsClosedImmersion (pullback.fst π i) :=
    MorphismProperty.pullback_fst (P := @IsClosedImmersion) π i inferInstance
  rw [CartierPullbackClosedFiber.ideal_eq_fiber_ker π D hD i hI,
    ← SchematicImageDenseOpen.ker_radical (pullback.fst π i),
    ← Scheme.IdealSheafData.vanishingIdeal_support]
  apply congrArg Scheme.IdealSheafData.vanishingIdeal
  apply Closeds.ext
  rw [Scheme.Hom.support_ker, (pullback.fst π i).isClosedEmbedding.isClosed_range.closure_eq]
  exact (ambient_ranges_union π i q).symm

end KltDP.Geometry.SplitCartierPullbackReducedUnion

#print axioms KltDP.Geometry.SplitCartierPullbackReducedUnion.pullbackIdealData_eq_copyUnion


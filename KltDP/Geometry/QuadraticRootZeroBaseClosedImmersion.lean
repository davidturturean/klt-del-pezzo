import KltDP.Geometry.QuadraticRamificationGluing

/-!
# The original global root-zero scheme is closed in the original base

The original root-zero chart is the pullback over its original affine
base chart. Its base map is the original branch quotient after the
existing root-zero/branch isomorphism, hence a closed immersion. Target
locality proves the same property for the unchanged global composite.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open QuadraticCover TransitionUnitGluing

variable {X : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)

/-- The original root-zero chart is the actual pullback of its original map to the base. -/
def rootZeroGlobalBaseChartIsPullback (i : ι) :
    IsPullback (D.rootZeroGlobalChartι i)
      (rootZeroι (res X (le_refl (D.opens i)) (D.sections i)) ≫
        toBase (res X (le_refl (D.opens i)) (D.sections i)))
      (D.rootZeroGlobalι ≫ D.morphism) (D.affine i).fromSpec :=
  KltDP.SchemeTwoOpenGluing.isPullback_of_range _ _ _ _ (D.rootZeroGlobalChartι_toBase i)
    ((D.range_rootZeroGlobalChartι i).trans
      (congrArg (fun V : Set X => (D.rootZeroGlobalι ≫ D.morphism).base ⁻¹' V)
        (IsAffineOpen.range_fromSpec (D.affine i)).symm))

/-- The unchanged global root-zero inclusion followed by the original cover map is closed. -/
theorem rootZeroGlobal_toBase_isClosedImmersion :
    IsClosedImmersion (D.rootZeroGlobalι ≫ D.morphism) := by
  apply IsLocalAtTarget.of_openCover (P := @IsClosedImmersion) D.baseCover
  intro i
  change IsClosedImmersion (pullback.snd (D.rootZeroGlobalι ≫ D.morphism) (D.affine i).fromSpec)
  rw [← (D.rootZeroGlobalBaseChartIsPullback i).isoPullback_inv_snd]
  let s := res X (le_refl (D.opens i)) (D.sections i)
  letI : IsClosedImmersion (rootZeroι s ≫ toBase s) := by
    rw [← rootZeroIsoBranch_hom_toBase]
    infer_instance
  infer_instance

end KltDP.Geometry.QuadraticCoverAtlas.Data

#print axioms KltDP.Geometry.QuadraticCoverAtlas.Data.rootZeroGlobal_toBase_isClosedImmersion

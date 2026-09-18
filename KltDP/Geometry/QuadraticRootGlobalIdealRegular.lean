import KltDP.Geometry.PrincipalQuotientOpenChart
import KltDP.Geometry.QuadraticRamificationGluing
import KltDP.Geometry.QuadraticRootRegular

/-!
# The original global ramification kernel has actual regular equations

Every original root-zero chart is the proved pullback of the original
global closed immersion. The actual quotient root therefore generates
the global kernel on that chart's image. Its regularity follows from
the original branch coefficient. Only nonempty base charts are used,
so no artificial nonemptiness restriction is placed on the atlas.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open QuadraticCover TransitionUnitGluing PrincipalQuotientOpenChart

variable {X : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)

local instance quadraticRootGlobalIdealRegularClosed : IsClosedImmersion D.rootZeroGlobalι :=
  D.rootZeroGlobalι_isClosedImmersion

/-- The actual affine open carrying the original quadratic root equation. -/
def rootEquationOpen (i : ι) : D.scheme.affineOpens := imageAffineOpen (D.chartι i)

/-- The original quotient root, as a section on its original global-cover chart. -/
def rootEquationSection (i : ι) : Γ(D.scheme, (D.rootEquationOpen i).1) :=
  sectionEquiv (D.chartι i) (root (res X (le_refl (D.opens i)) (D.sections i)))

/-- The actual original root equation generates the actual original ramification kernel. -/
theorem rootZeroGlobal_kernel_ideal (i : ι) :
    D.rootZeroGlobalι.ker.ideal (D.rootEquationOpen i) =
      Ideal.span {D.rootEquationSection i} :=
  kernel_ideal_eq_span D.rootZeroGlobalι (D.chartι i)
    (root (res X (le_refl (D.opens i)) (D.sections i)))
    (D.rootZeroGlobalChartι i) (D.rootZeroGlobalChartIsPullback i).flip

/-- Original branch regularity gives regularity of the actual global-cover equation. -/
theorem rootEquationSection_regular (i : ι)
    (hi : D.sections i ∈ nonZeroDivisors Γ(X, D.opens i)) :
    D.rootEquationSection i ∈ nonZeroDivisors Γ(D.scheme, (D.rootEquationOpen i).1) := by
  apply sectionEquiv_regular
  apply root_mem_nonZeroDivisors
  simpa only [res_self] using hi

/-- The original ramification kernel is locally principal regular on its actual cover. -/
theorem rootZeroGlobal_kernel_locallyPrincipalRegular
    (hbranch : ∀ i, (D.opens i : Set X).Nonempty →
      D.sections i ∈ nonZeroDivisors Γ(X, D.opens i)) :
    IdealLocallyPrincipalRegular D.rootZeroGlobalι.ker := by
  intro x
  obtain ⟨i, z, rfl⟩ := D.glueData.ι_jointly_surjective x
  have hi : (D.opens i : Set X).Nonempty :=
    ⟨D.morphism.base ((D.chartι i).base z), (D.range_chartι i).le ⟨z, rfl⟩⟩
  refine ⟨D.rootEquationOpen i, ?_, D.rootEquationSection i,
    D.rootZeroGlobal_kernel_ideal i, D.rootEquationSection_regular i (hbranch i hi)⟩
  exact ⟨z, trivial, rfl⟩

end KltDP.Geometry.QuadraticCoverAtlas.Data

#print axioms KltDP.Geometry.QuadraticCoverAtlas.Data.rootZeroGlobal_kernel_ideal
#print axioms KltDP.Geometry.QuadraticCoverAtlas.Data.rootZeroGlobal_kernel_locallyPrincipalRegular

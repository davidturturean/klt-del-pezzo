import KltDP.Geometry.OriginalCartierQuadraticIntegral
import KltDP.Geometry.QuadraticReducedBranchNormal
import KltDP.Geometry.NormalAffineSections

/-!
# Normality of the original cover with reduced nonempty Cartier branch

The original canonical branch proves integrality of the unchanged cover.
At each actual cover point its original affine chart is therefore a
domain. The original base chart is normal; the original Cartier quotient
comparison proves its branch quotient reduced; and the nonzero canonical
section proves the coefficient nonzero. The actual quadratic integral
closure theorem proves normality of that same chart. The original open
immersion identifies its stalk with the original cover stalk.

There is no cover-normality or integrality premise, no chosen valuation,
and no supplied branch coordinates. Smoothness of the ambient cover at
branch points remains distinct from this normality conclusion.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.OriginalCartierQuadraticIntegral

open QuadraticCover InvertibleQuadraticAtlas TransitionUnitGluing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated]
local instance originalCartierQuadraticNormalMonoidal : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X

/-- Reduced nonempty original Cartier branch makes the same original cover normal. -/
theorem scheme_isNormal_of_reduced_nonempty_branch
    (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X E)
    (hnormal : IsNormalScheme X) (h2 : IsUnit (2 : Γ(X, ⊤)))
    (hred : IsReduced (effectiveCartierIdealDataOfRegularEquations X E hE).glueData.glued)
    (hne : Nonempty (effectiveCartierIdealDataOfRegularEquations X E hE).glueData.glued) :
    IsNormalScheme (fromSquareRoot X L (cartierDivisorModule X E) e
      (effectiveCartierSection X E hE)).scheme := by
  let A := effectiveCartierQuadraticAtlas X E hE L e
  letI : IsIntegral A.scheme := scheme_isIntegral_of_reduced_nonempty_branch
    X E hE L e hnormal hred hne
  have hred' : IsReduced (effectiveCartierIdealData X E hE L e).glueData.glued := by
    rw [effectiveCartierIdealData_eq_ofRegularEquations X E hE L e]
    exact hred
  intro y
  obtain ⟨i, z, rfl⟩ := A.charts_cover y
  letI : Nonempty (A.chart i) := ⟨z⟩
  letI : IsIntegral (A.chart i) := isIntegral_of_isOpenImmersion (A.chartι i)
  letI : Nonempty (A.opens i) :=
    ⟨⟨(A.chartToBase i).base z, A.frameToBase_mem (le_refl (A.opens i)) (A.affine i) z⟩⟩
  letI : Nonempty (AffineOpenRefinement.opens X L.localTrivializations.X i) :=
    ⟨⟨(A.chartToBase i).base z, A.frameToBase_mem (le_refl (A.opens i)) (A.affine i) z⟩⟩
  letI : IsDomain Γ(X, A.opens i) := IsIntegral.component_integral (A.opens i)
  letI : IsIntegrallyClosed Γ(X, A.opens i) :=
    isIntegrallyClosed_affineSections_of_isNormal X hnormal (A.affine i)
  let s := res X (le_refl (A.opens i)) (A.sections i)
  letI : IsDomain (CoverAlgebra s) :=
    (affine_isIntegral_iff (CommRingCat.of (CoverAlgebra s))).mp
      (inferInstanceAs (IsIntegral (A.chart i)))
  have hs : s ≠ 0 := by
    dsimp only [s]
    rw [res_self]
    exact fromSquareRoot_coefficient_ne_zero X L (cartierDivisorModule X E) e
      (effectiveCartierSection X E hE) (effectiveCartierSection_ne_zero X E hE) i
  have h2i : IsUnit (2 : Γ(X, A.opens i)) := by
    simpa only [map_ofNat] using h2.map (res X (show A.opens i ≤ ⊤ from le_top))
  have hbranch : _root_.IsReduced (Γ(X, A.opens i) ⧸ Ideal.span ({s} : Set Γ(X, A.opens i))) := by
    dsimp only [s]
    rw [res_self]
    exact branch_quotient_isReduced (A.sections i) (branchChart_isReduced X E hE L e hred' i)
  letI : IsIntegrallyClosed (CoverAlgebra s) :=
    coverAlgebra_isIntegrallyClosed_of_reduced_branch (FractionRing Γ(X, A.opens i)) s hs h2i hbranch
  exact normal_stalk_at_image_of_isOpenImmersion (A.chartι i)
    (spec_isNormalScheme_of_isIntegrallyClosed (CoverAlgebra s)) z

end KltDP.Geometry.OriginalCartierQuadraticIntegral

#print axioms KltDP.Geometry.OriginalCartierQuadraticIntegral.scheme_isNormal_of_reduced_nonempty_branch

import KltDP.Geometry.OriginalCartierQuadraticSurface
import KltDP.Geometry.OriginalCartierGlobalRamificationSmooth
import KltDP.Geometry.OriginalCartierRootZeroChartDimension
import KltDP.Geometry.PrincipalQuotientCotangentBound
import KltDP.Geometry.SpecPrincipalQuotientStalkKernel

/-!
# Regularity at actual closed branch points of the original cover

The already constructed original normal projective cover has actual
closed-point stalk dimension two. Its original open chart identifies that
stalk with the ambient quadratic chart stalk. The original root-zero
quotient is smooth of dimension at most one, so its cotangent rank is at
most one. The original quotient inclusion has the actual principal root
germ as its stalk kernel. The proved principal-quotient cotangent bound
therefore proves regularity of the original ambient cover point.

No ambient regularity, quotient coordinates, principal stalk kernel, or
cotangent bound is supplied. The branch smoothness premise concerns the
original canonical Cartier zero scheme over the original field.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace IsLocalRing
universe u

namespace KltDP.Geometry.OriginalCartierRamificationSmooth

open QuadraticCover TransitionUnitGluing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)

local instance originalCartierBranchPointSeparated : S.toScheme.IsSeparated :=
  NormalProjectiveSurface.surfaceSeparated S
local instance originalCartierBranchPointMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

/-- A closed point reached by the original root-zero chart is regular in the same original cover. -/
theorem regularPoint_of_closed_rootZeroChart
    (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
    (hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hsm : IsSmooth
      ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism))
    (i : AffineOpenRefinement.Index S.toScheme L.localTrivializations.X) :
    let A := effectiveCartierQuadraticAtlas S.toScheme E hE L e
    let s := res S.toScheme (le_refl (A.opens i)) (A.sections i)
    ∀ y : A.rootZeroChart i,
      IsClosed ({(rootZeroι s ≫ A.chartι i).base y} : Set A.scheme) →
        RegularPoint A.scheme ((rootZeroι s ≫ A.chartι i).base y) := by
  let A := effectiveCartierQuadraticAtlas S.toScheme E hE L e
  let s := res S.toScheme (le_refl (A.opens i)) (A.sections i)
  dsimp only
  intro y hclosed
  let T := OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
  let j := rootZeroι s ≫ A.chartι i
  let q := (rootZeroι s).base y
  letI : IsIntegral A.scheme := T.integral
  letI : LocallyOfFiniteType T.structureMorphism := T.projective.locallyOfFiniteType
  letI : IsNoetherianRing (A.scheme.presheaf.stalk (j.base y)) :=
    T.projective.isNoetherianRing_stalk (j.base y)
  letI : IsDomain (A.scheme.presheaf.stalk (j.base y)) := (T.normal (j.base y)).1
  let ε := (asIso ((A.chartι i).stalkMap q)).commRingCatIsoToRingEquiv
  letI : IsNoetherianRing ((A.chart i).presheaf.stalk q) :=
    isNoetherianRing_of_ringEquiv (A.scheme.presheaf.stalk (j.base y)) ε
  letI : IsDomain ((A.chart i).presheaf.stalk q) :=
    MulEquiv.isDomain (A.scheme.presheaf.stalk (j.base y)) ε.symm.toMulEquiv
  have hdimGlobal : ringKrullDim (A.scheme.presheaf.stalk (j.base y)) = 2 :=
    (closed_stalk_dimension_eq_global A.scheme T.structureMorphism (j.base y) hclosed).trans
      T.dimension_two
  have hdim : ringKrullDim ((A.chart i).presheaf.stalk q) = 2 :=
    (ringKrullDim_eq_of_ringEquiv ε).symm.trans hdimGlobal
  have hy : IsClosed ({y} : Set (A.rootZeroChart i)) := by
    have hpre := hclosed.preimage j.isEmbedding.continuous
    have heq : j.base ⁻¹' ({j.base y} : Set A.scheme) = {y} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact j.isEmbedding.injective.eq_iff
    rwa [heq] at hpre
  let P (t : Γ(S.toScheme, A.opens i)) : Prop :=
    ∀ w : rootZeroScheme t, IsClosed ({w} : Set (rootZeroScheme t)) →
      Module.finrank (ResidueField ((rootZeroScheme t).presheaf.stalk w))
        (CotangentSpace ((rootZeroScheme t).presheaf.stalk w)) ≤ 1
  have hP : P (A.sections i) := fun w hw =>
    rootZeroChart_cotangent_finrank_le_one S E hE L e hsm i w hw
  have hquot := ((congrArg P (res_self S.toScheme (A.opens i) (A.sections i))).mpr hP) y hy
  have hreg : RegularPoint (A.chart i) q :=
    RegularLocalParameterQuotient.regularLocal_of_principal_quotient_cotangent_le_one
      ((rootZeroι s).stalkMap y).hom ((rootZeroι s).stalkMap_surjective y)
      (SpecPrincipalQuotient.equationGerm_mem_maximalIdeal (root s) y)
      (SpecPrincipalQuotient.stalkMap_ker (root s) y) hdim hquot
  exact (regularPoint_iff_of_isOpenImmersion (A.chartι i) q).mp hreg

end KltDP.Geometry.OriginalCartierRamificationSmooth

#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.regularPoint_of_closed_rootZeroChart

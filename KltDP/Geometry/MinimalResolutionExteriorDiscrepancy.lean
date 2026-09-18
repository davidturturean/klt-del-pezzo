import KltDP.Geometry.MinimalResolutionDiscrepancy
import KltDP.Geometry.KltResolutionExceptionalProjectiveLine

/-!
# The original canonical discrepancy against an exterior prime

Klt supplies the actual exceptional projective-line isomorphisms needed by
minimal-resolution discrepancy nonpositivity. The literal compatible
difference is supported on contracted primes. Every such prime is distinct
from an exterior prime, so its original intersection with that prime is
nonnegative. Summing the actual nonpositive coefficients gives the bound.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.IsMinimalResolution

open NormalProjectiveSurface SmoothCanonicalExteriorComparison
open BirationalWeilPushforward RationalWeilIntersection

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}

local instance exteriorDiscrepancyIntegral (T : NormalProjectiveSurface k) :
    IsIntegral T.toScheme := T.integral

/-- On every original exterior prime, the degree of an actually compatible
canonical divisor is at most the original pulled target canonical degree.
No discrepancy equation, support, coefficient sign, or curve rationality
is an input. -/
theorem canonical_degree_le_pullback_of_klt
    (hmin : IsMinimalResolution S X π)
    (KS : CartierDivisor S.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      relativeDifferentialExterior S.structureMorphism 2)
    (KX : X.WeilDivisor) (hKX : IsKltWithCanonicalDivisor X KX) :
    letI : IsProper π := hmin.toIsResolution.isProper
    let hbir : IsBirationalScheme π :=
      (isBirational_iff_isBirationalScheme π).mp hmin.birational
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    pushforward π hbir (S.cartierToWeilHom KS) = KX →
    ∀ C : S.PrimeCurve, ¬ IsExceptionalCurve π C →
      (C.intersectionNumber KS : ℚ) ≤ degreeLinearMap S hmin.regular C
        (QCartierPullback.pullback π (rationalizeWeilDivisor X KX) hKX.2.1) := by
  classical
  letI : IsProper π := hmin.toIsResolution.isProper
  let hbir : IsBirationalScheme π :=
    (isBirational_iff_isBirationalScheme π).mp hmin.birational
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hmin.regular
  dsimp only
  intro hpush C hC
  let Δ : S.RationalWeilDivisor := S.rationalCartierToWeilHom KS -
    QCartierPullback.pullback π (rationalizeWeilDivisor X KX) hKX.2.1
  have hsupport : (Δ.support : Set S.PrimeCurve) ⊆ {E | IsExceptionalCurve π E} :=
    MinimalResolutionDiscrepancy.difference_support_subset_exceptional
      π hbir KS KX hKX.2.1 hpush
  have hcoeff : ∀ E : S.PrimeCurve, Δ E ≤ 0 :=
    MinimalResolutionDiscrepancy.coefficient_nonpos S X π hmin KS eKS KX hKX.2.1
      (hmin.toIsResolution.exceptional_projectiveLine_iso_of_klt ⟨KX, hKX⟩) hpush
  have hdegree : degreeLinearMap S hmin.regular C Δ ≤ 0 := by
    rw [degreeLinearMap_apply]
    apply Finset.sum_nonpos
    intro E hE
    have hCE : C ≠ E := by
      intro heq
      subst E
      exact hC (hsupport hE)
    have hpair : (0 : ℚ) ≤
        (C.intersectionNumber (S.primeCurveCartier hmin.regular E) : ℚ) := by
      exact_mod_cast PrimeCurvePairingSupport.intersectionNumber_nonneg_of_notInSupport
        C (S.primeCurveCartier hmin.regular E)
        (S.primeCurveCartier_hasRegularEquations hmin.regular E)
        (S.notInSupport_of_ne hmin.regular hCE)
    exact mul_nonpos_of_nonpos_of_nonneg (hcoeff E) hpair
  change degreeLinearMap S hmin.regular C
    (S.rationalCartierToWeilHom KS -
      QCartierPullback.pullback π (rationalizeWeilDivisor X KX) hKX.2.1) ≤ 0 at hdegree
  rw [map_sub, degreeLinearMap_rationalCartier] at hdegree
  exact sub_nonpos.mp hdegree

end KltDP.Geometry.IsMinimalResolution

#check @KltDP.Geometry.IsMinimalResolution.canonical_degree_le_pullback_of_klt
#print axioms KltDP.Geometry.IsMinimalResolution.canonical_degree_le_pullback_of_klt

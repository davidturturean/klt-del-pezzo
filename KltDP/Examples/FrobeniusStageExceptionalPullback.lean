import KltDP.Examples.FrobeniusStageSurface
import KltDP.Geometry.GluedIdealSheafLift
import KltDP.Geometry.SchematicImageDenseOpen
import KltDP.Geometry.PrimeCurveRestrictionDegree
import KltDP.Geometry.AffinePIDInvertibleTrivial
import KltDP.Geometry.SchemeModuleFunctorial
import KltDP.Geometry.SchemeModulePullbackUnit

/-!
# `E · π^*L = 0`: the exceptional curve meets pulled-back line bundles trivially

For the prime curve `E = exceptionalPrimeCurve n hproj` of the stage-`(n+1)` surface and every
invertible sheaf `L` on stage `n`, the restriction degree of `π^*L` to `E` vanishes
(`restrictionDegree_pullback_stepProjection`); in lane D's notation this is
`E · π^*D = 0` for every Cartier divisor `D` on stage `n`
(`intersectionNumber C D = restrictionDegree C (cartierDivisorInvertibleSheaf D)` by definition).

Route. The scheme `E.toScheme` of the prime curve is the accepted glued closed subscheme of the
vanishing ideal of the range of the accepted closed immersion `stepExceptionalInclusion n` (the
categorical centre fibre, reduced since it is `P¹`); the kernel of that closed immersion is radical
(accepted `ker_radical`) with support the range, so it *is* the vanishing ideal
(`stepExceptionalInclusion_ker`). The accepted `GluedIdealSheafLift.liftGlued` therefore factors the
centre fibre through `E.inclusion`; the factor is a surjective closed immersion onto the reduced
`E.toScheme`, hence an isomorphism (pinned `isIso_of_isClosedImmersion_of_surjective`), so
`E.inclusion = inv exceptionalLift ≫ stepExceptionalInclusion n` (`inclusion_eq_inv_exceptionalLift`).
Composing with the step projection lands in the closed centre through the pullback square of the
centre fibre (`inclusion_comp_stepProjection`); the pullback of `L` to the centre `Spec (k[u][v]/m)`
(a field) is trivial (accepted `pidInvertibleUnitIso`), and pullbacks compose (accepted
`schemeModulePullbackCompIso`, `schemeModulePullbackUnitIso`), so the restricted line bundle is
trivial and its degree is zero (accepted `lineDegree_eq_zero_of_iso_unit`).

Hypotheses: `k` algebraically closed (dimension two of the stage) and the projectivity hypothesis
`hproj` of `stageSurface`; nothing else.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusStageExceptionalPullback

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
open FrobeniusGlobalExceptionalNormal FrobeniusStrictTransformProductKernel
open FrobeniusStageSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

local instance exceptionalPullbackOriginIdealMaximal :
    (originPoint (k := k)).asIdeal.IsMaximal :=
  centerIdeal_isMaximal

/-- The support of the kernel of the exceptional closed immersion is the curve `E`. -/
theorem stepExceptionalInclusion_ker_support :
    (stepExceptionalInclusion (k := k) n).ker.support =
      (exceptionalPrimeCurve n hproj).closedSubset := by
  apply TopologicalSpace.Closeds.ext
  rw [Scheme.Hom.support_ker]
  exact (range_stepExceptionalInclusion_isClosed n).closure_eq

/-- The kernel of the exceptional closed immersion is the vanishing ideal of `E`: the centre fibre
is reduced, so its kernel is radical with support `E`. -/
theorem stepExceptionalInclusion_ker :
    (stepExceptionalInclusion (k := k) n).ker = (exceptionalPrimeCurve n hproj).vanishingIdeal := by
  rw [← SchematicImageDenseOpen.ker_radical (stepExceptionalInclusion (k := k) n),
    ← Scheme.IdealSheafData.vanishingIdeal_support, stepExceptionalInclusion_ker_support]
  rfl

/-- The centre fibre factors through the prime-curve scheme of `E`. -/
def exceptionalLift :
    globalExceptionalScheme ((projectiveProductInitial (k := k)).stage n) ⟶
      (exceptionalPrimeCurve n hproj).toScheme :=
  GluedIdealSheafLift.liftGlued (exceptionalPrimeCurve n hproj).vanishingIdeal
    (stepExceptionalInclusion (k := k) n) (stepExceptionalInclusion_ker n hproj).ge

@[reassoc] theorem exceptionalLift_inclusion :
    exceptionalLift n hproj ≫ (exceptionalPrimeCurve n hproj).inclusion =
      stepExceptionalInclusion (k := k) n :=
  GluedIdealSheafLift.liftGlued_gluedTo _ _ _

instance exceptionalLift_isClosedImmersion : IsClosedImmersion (exceptionalLift n hproj) := by
  haveI : IsClosedImmersion
      (exceptionalLift n hproj ≫ (exceptionalPrimeCurve n hproj).inclusion) := by
    rw [exceptionalLift_inclusion]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (exceptionalPrimeCurve n hproj).inclusion

instance exceptionalLift_surjective : Surjective (exceptionalLift n hproj) := by
  refine ⟨fun y => ?_⟩
  have hy : (exceptionalPrimeCurve n hproj).inclusion.base y ∈
      (exceptionalPrimeCurve n hproj : Set (stageSurface (n + 1) hproj).toScheme) := by
    rw [← PrimeCurve.range_inclusion]
    exact ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := hy
  refine ⟨z, (exceptionalPrimeCurve n hproj).inclusion.isClosedEmbedding.injective ?_⟩
  rw [← hz, ← exceptionalLift_inclusion n hproj, Scheme.comp_base_apply]
  rfl

/-- The factor is an isomorphism: a surjective closed immersion onto the reduced curve scheme. -/
instance exceptionalLift_isIso : IsIso (exceptionalLift n hproj) :=
  isIso_of_isClosedImmersion_of_surjective _

/-- The prime-curve inclusion of `E` is the centre-fibre inclusion transported along the iso. -/
theorem inclusion_eq_inv_exceptionalLift :
    (exceptionalPrimeCurve n hproj).inclusion =
      inv (exceptionalLift n hproj) ≫ stepExceptionalInclusion (k := k) n := by
  rw [← exceptionalLift_inclusion n hproj, IsIso.inv_hom_id_assoc]

/-- The closed centre of the `(n+1)`-st blowup, as the spectrum of the residue field of the origin. -/
abbrev centreScheme : Scheme.{u} :=
  Spec (CommRingCat.of (planeRing k ⧸ (originPoint (k := k)).asIdeal))

/-- The prime curve `E` maps to the centre. -/
def exceptionalToCentre : (exceptionalPrimeCurve n hproj).toScheme ⟶ centreScheme (k := k) :=
  inv (exceptionalLift n hproj) ≫
    PointBlowupGluing.globalCenterFiberToCenter
      ((projectiveProductInitial (k := k)).stage n).chart (originPoint (k := k))
      ((projectiveProductInitial (k := k)).stage n).center_closed

/-- **`E` followed by the step projection factors through the closed centre.** -/
theorem inclusion_comp_stepProjection :
    (exceptionalPrimeCurve n hproj).inclusion ≫ (projectiveProductInitial (k := k)).stepProjection n =
      exceptionalToCentre n hproj ≫
        PointBlowupGluing.closedCenterInclusion
          ((projectiveProductInitial (k := k)).stage n).chart (originPoint (k := k)) := by
  rw [inclusion_eq_inv_exceptionalLift, exceptionalToCentre, Category.assoc, Category.assoc]
  congr 1
  exact pullback.condition

/-- **`E · π^*L = 0`**: the restriction to `E` of the pullback along the step projection of any
invertible sheaf `L` on stage `n` has degree zero. -/
theorem restrictionDegree_pullback_stepProjection
    (L : InvertibleSheaf (projectiveContactStage (k := k) n)) :
    (exceptionalPrimeCurve n hproj).restrictionDegree
      (pullbackInvertibleSheaf ((projectiveProductInitial (k := k)).stepProjection n) L) = 0 := by
  letI : Field (planeRing k ⧸ (originPoint (k := k)).asIdeal) := Ideal.Quotient.field _
  unfold PrimeCurve.restrictionDegree
  apply (exceptionalPrimeCurve n hproj).lineDegree_eq_zero_of_iso_unit
  refine ((schemeModulePullbackCompIso (exceptionalPrimeCurve n hproj).inclusion
    ((projectiveProductInitial (k := k)).stepProjection n)).app L.obj) ≪≫ ?_
  rw [inclusion_comp_stepProjection]
  refine ((schemeModulePullbackCompIso (exceptionalToCentre n hproj)
    (PointBlowupGluing.closedCenterInclusion
      ((projectiveProductInitial (k := k)).stage n).chart (originPoint (k := k)))).symm.app
        L.obj) ≪≫ ?_
  refine (schemeModulePullback (exceptionalToCentre n hproj)).mapIso
    (AffineModuleTilde.pidInvertibleUnitIso (pullbackInvertibleSheaf
      (PointBlowupGluing.closedCenterInclusion
        ((projectiveProductInitial (k := k)).stage n).chart (originPoint (k := k))) L)) ≪≫ ?_
  exact schemeModulePullbackUnitIso (exceptionalToCentre n hproj)

/-- The same statement for the pullback of an invertible sheaf on any earlier stage `m ≤ n`,
composed through the step projection: `E · (π ∘ ρ)^*L = 0` for every `ρ : stage n ⟶ Y`. -/
theorem restrictionDegree_pullback_stepProjection_comp {Y : Scheme.{u}}
    (ρ : projectiveContactStage (k := k) n ⟶ Y) (L : InvertibleSheaf Y) :
    (exceptionalPrimeCurve n hproj).restrictionDegree
      (pullbackInvertibleSheaf ((projectiveProductInitial (k := k)).stepProjection n ≫ ρ) L) = 0 := by
  rw [← restrictionDegree_pullback_stepProjection n hproj (pullbackInvertibleSheaf ρ L)]
  unfold PrimeCurve.restrictionDegree
  apply (exceptionalPrimeCurve n hproj).lineDegree_eq_of_iso
  exact (schemeModulePullback (exceptionalPrimeCurve n hproj).inclusion).mapIso
    ((schemeModulePullbackCompIso ((projectiveProductInitial (k := k)).stepProjection n) ρ).symm.app
      L.obj)

end KltDP.Examples.FrobeniusStageExceptionalPullback

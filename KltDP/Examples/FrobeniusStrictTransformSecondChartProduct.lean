import KltDP.Examples.FrobeniusStrictTransformProductKernel
import KltDP.Examples.FrobeniusStrictTransformSecondChartFrame

/-!
# The original exceptional ideal on the second whole-stage chart

The original exceptional quotient chart and the actual affine-to-global center
fiber isomorphism give the original second-chart pullback square. Its kernel is
the literal global center-fiber kernel, with equation v in the original Rees ring.
The already proved total equation therefore factors into the two original ideals.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusStrictTransformSecondChartProduct

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupChartIteration
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusExceptionalSuccessorChart FrobeniusGraphPicardClassContactIdeal
open FrobeniusStrictTransformProductKernel FrobeniusStrictTransformSecondChartAlgebra
open FrobeniusStrictTransformSecondChart FrobeniusStrictTransformSecondChartFrame

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

local instance secondProductOriginIdealMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  centerIdeal_isMaximal

/-- The original second exceptional quotient chart maps into the literal global center fiber. -/
def secondExceptionalToGlobal (n : ℕ) :
    exceptionalChart (centerIdeal (k := k)) centerV ⟶
      PointBlowupGluing.globalCenterFiber
        ((projectiveProductInitial (k := k)).stage n).chart (originPoint (k := k))
        ((projectiveProductInitial (k := k)).stage n).center_closed :=
  exceptionalChartToFiber (centerIdeal (k := k)) centerV ≫
    (PointBlowupGluing.affineCenterFiberIso
      ((projectiveProductInitial (k := k)).stage n).chart (originPoint (k := k))
      ((projectiveProductInitial (k := k)).stage n).center_closed).hom

private theorem affineCenterFiber_global_isPullback (n : ℕ) :
    IsPullback (centerFiberι (centerIdeal (k := k)))
      (PointBlowupGluing.affineCenterFiberIso
        ((projectiveProductInitial (k := k)).stage n).chart (originPoint (k := k))
        ((projectiveProductInitial (k := k)).stage n).center_closed).hom
      (((projectiveProductInitial (k := k)).stage n).nextAffineBlowup)
      (stepExceptionalInclusion n) := by
  refine (PointBlowupGluing.exceptionalGlobalFiber_isPullback
    ((projectiveProductInitial (k := k)).stage n).chart (originPoint (k := k))
    ((projectiveProductInitial (k := k)).stage n).center_closed).of_iso
      (exceptionalFiberIso (centerIdeal (k := k))) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, exceptionalFiberIso_hom_ι]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id,
      PointBlowupGluing.exceptionalGlobalFiberIso, Iso.trans_hom]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- Pasting the actual quotient and global fiber squares gives the original chart restriction. -/
theorem secondExceptionalGlobal_isPullback (n : ℕ) :
    IsPullback (exceptionalChartInclusion (centerIdeal (k := k)) centerV)
      (secondExceptionalToGlobal n) (secondStageChart n) (stepExceptionalInclusion n) := by
  simpa only [secondExceptionalToGlobal, secondStageChart] using
    (exceptionalChartToFiber_isPullback (centerIdeal (k := k)) centerV).paste_vert
      (affineCenterFiber_global_isPullback n)

/-- The literal global center-fiber kernel in the original second-chart coordinates. -/
def stepExceptionalSecondChartIdeal (n : ℕ) : Ideal (reesVChartRing k) :=
  (((stepExceptionalInclusion (k := k) n).ker.ideal (secondAffineOpen n)).comap
    ((secondStageChart n).appIso ⊤).inv.hom).comap
      (Scheme.ΓSpecIso (CommRingCat.of (reesVChartRing k))).inv.hom

private theorem secondExceptional_coordinateKernel :
    RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (reesVChartRing k))).inv ≫
      (exceptionalChartInclusion (centerIdeal (k := k)) centerV).appTop).hom) =
        chartCenterIdeal (centerIdeal (k := k)) centerV := by
  have hΓ : Function.Injective
      ((Scheme.ΓSpecIso (CommRingCat.of
        (exceptionalChartRing (centerIdeal (k := k)) centerV))).inv.hom) :=
    (Scheme.ΓSpecIso (CommRingCat.of
      (exceptionalChartRing (centerIdeal (k := k)) centerV))).symm.commRingCatIsoToRingEquiv.injective
  rw [exceptionalChartInclusion, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.hom_comp, RingHom.ker_comp_of_injective _ hΓ,
    CommRingCat.hom_ofHom, Ideal.mk_ker]

/-- The actual global exceptional kernel is exactly the original Rees center ideal. -/
theorem stepExceptionalSecondChartIdeal_eq_rees (n : ℕ) :
    stepExceptionalSecondChartIdeal (k := k) n = chartCenterIdeal (centerIdeal (k := k)) centerV := by
  unfold stepExceptionalSecondChartIdeal secondAffineOpen
  rw [← Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (stepExceptionalInclusion (k := k) n) (exceptionalChartInclusion (centerIdeal (k := k)) centerV)
    (secondExceptionalToGlobal n) (secondStageChart n)
    (secondExceptionalGlobal_isPullback n)
    ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of (reesVChartRing k)))⟩,
    Scheme.Hom.ker_apply]
  change RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (reesVChartRing k))).inv ≫
    (exceptionalChartInclusion (centerIdeal (k := k)) centerV).appTop).hom) = _
  exact secondExceptional_coordinateKernel

/-- Its generator is the actual pulled base coordinate v, with no unit rescaling. -/
theorem stepExceptionalSecondChartIdeal_eq_span (n : ℕ) :
    stepExceptionalSecondChartIdeal (k := k) n = Ideal.span {vEquation} :=
  (stepExceptionalSecondChartIdeal_eq_rees n).trans
    (map_chartBaseMap_ideal (centerIdeal (k := k)) centerV)

/-- The original previous strict ideal pulls back to the two actual global kernel ideals. -/
theorem strictSecondChart_globalTotalIdeal_factorization (n m : ℕ) :
    Ideal.map (chartBaseMap (centerIdeal (k := k)) centerV) (strictChartIdeal (k := k) n (m + 1)) =
      stepExceptionalSecondChartIdeal n * strictSecondChartIdeal n m := by
  rw [stepExceptionalSecondChartIdeal_eq_rees]
  exact strictSecondChart_totalIdeal_factorization n m

end KltDP.Examples.FrobeniusStrictTransformSecondChartProduct

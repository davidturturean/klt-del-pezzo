import KltDP.Geometry.PointBlowupChartStalkAtCenter
import KltDP.Geometry.AffineBlowupRegularPairExceptionalPrime
import KltDP.Geometry.AffineBlowupChartLocalizationCenter
import KltDP.Geometry.SchemePointBlowupSourceRegular
import KltDP.Geometry.SchemePointBlowupSequenceProper
import KltDP.Geometry.RegularProperSurface

/-!
# The original exceptional prime in the original centre-localized chart

The source surface retains the original glued scheme and projection.
Its integrality, regularity, dimension, normality and projectivity are
derived by the existing actual point-blowup producers. At any original
prime curve contracted to the centre, the actual global stalk is a DVR.
The original chart stalk equivalence therefore identifies its localized
chart prime with the original exceptional chart ideal. The latter
equality and the DVR property are conclusions, not inputs.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.PointBlowupExceptionalPrimeStalk

open AffineBlowup AffineBlowupChartBaseChange AffineBlowupRegularPairChart
open PointBlowupGluing PointBlowupChartStalk

variable {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))

/-- The original blowup scheme, equipped with its proved surface properties.
Its structure map is the original projection followed by the original one. -/
def sourceSurface : NormalProjectiveSurface k := by
  let c : PointBlowupChart X.toScheme (j.base q) :=
    { R := R, j := j, q := q, isClosed := hclosed, base_eq := rfl }
  have h := SchemePointBlowup.isAt_projection c
  letI : IsIntegral (scheme j q hclosed) := h.source_isIntegral_of_surface X
  letI : IsLocallyNoetherian X.toScheme :=
    isLocallyNoetherian_of_locallyOfFiniteType_spec X.structureMorphism
  letI : IsProper (projection j q hclosed) := h.isProper
  letI : IsProper X.structureMorphism := X.projective.isProper
  exact regularProperSurface (scheme j q hclosed)
    (projection j q hclosed ≫ X.structureMorphism)
    (h.source_regular X) (h.source_dimension_two X)

@[simp] theorem sourceSurface_toScheme :
    (sourceSurface X j q hclosed).toScheme = scheme j q hclosed := rfl

@[simp] theorem sourceSurface_structureMorphism :
    (sourceSurface X j q hclosed).structureMorphism =
      projection j q hclosed ≫ X.structureMorphism := rfl

/-- The actual centre ideal in its original prime localization. -/
abbrev centerIdeal : Ideal (Localization.AtPrime q.asIdeal) :=
  q.asIdeal.map (algebraMap R (Localization.AtPrime q.asIdeal))

/-- An original Rees denominator, mapped into that exact ideal stalk. -/
abbrev centerParameter (a : q.asIdeal) : centerIdeal q :=
  mappedElement q.asIdeal (algebraMap R (Localization.AtPrime q.asIdeal)) a

local instance : (centerIdeal q).IsPrime := by
  dsimp only [centerIdeal]
  rw [Localization.AtPrime.map_eq_maximalIdeal]
  infer_instance

variable (C : (sourceSurface X j q hclosed).PrimeCurve)
    (a : q.asIdeal) (P : PrimeSpectrum (chartRing q.asIdeal a))
    (hC : (chartInclusion j q hclosed a).base P = C.genericPoint)
    (hcenter : (projection j q hclosed).base C.genericPoint = j.base q)

include hC hcenter in
/-- The original contraction and the original chart projection derive
the image of the actual chart prime in the original base ring. -/
theorem chartPrime_comap : P.asIdeal.comap (chartBaseMap q.asIdeal a) = q.asIdeal := by
  have hpoints : j.base (PrimeSpectrum.comap (chartBaseMap q.asIdeal a) P) = j.base q := by
    calc
      _ = (projection j q hclosed).base ((chartInclusion j q hclosed a).base P) :=
        (congrArg (fun f : Spec (CommRingCat.of (chartRing q.asIdeal a)) ⟶ X.toScheme =>
          f.base P) (chartInclusion_projection j q hclosed a)).symm
      _ = (projection j q hclosed).base C.genericPoint := congrArg _ hC
      _ = j.base q := hcenter
  exact congrArg PrimeSpectrum.asIdeal (j.isOpenEmbedding.injective hpoints)

/-- At the original contracted prime curve, the original localized chart
prime is exactly the actual exceptional centre ideal. The local pair lives
in the original centre stalk, with no affine-global generation premise. -/
theorem localizedPrime_eq_chartCenterIdeal
    (b : centerIdeal q)
    (ha : (centerParameter q a : Localization.AtPrime q.asIdeal) ∈
      nonZeroDivisors (Localization.AtPrime q.asIdeal))
    (hb : Ideal.Quotient.mk
      (Ideal.span {(centerParameter q a : Localization.AtPrime q.asIdeal)})
      (b : Localization.AtPrime q.asIdeal) ∈ nonZeroDivisors
        (Localization.AtPrime q.asIdeal ⧸
          Ideal.span {(centerParameter q a : Localization.AtPrime q.asIdeal)}))
    (hI : centerIdeal q = Ideal.span
      {(centerParameter q a : Localization.AtPrime q.asIdeal),
        (b : Localization.AtPrime q.asIdeal)}) :
    localizedChartPrime q.asIdeal a q.asIdeal P.asIdeal
        (chartPrime_comap X j q hclosed C a P hC hcenter) =
      chartCenterIdeal (centerIdeal q) (centerParameter q a) := by
  let hPq := chartPrime_comap X j q hclosed C a P hC hcenter
  let Q := localizedChartPrime q.asIdeal a q.asIdeal P.asIdeal hPq
  letI : IsDomain (Localization.AtPrime q.asIdeal) :=
    X.affineLocalization_isDomain j q
  letI : IsIntegral (scheme j q hclosed) := (sourceSurface X j q hclosed).integral
  letI : IsDomain ((scheme j q hclosed).presheaf.stalk
      ((chartInclusion j q hclosed a).base P)) :=
    integralSchemeStalk_isDomain _ _
  letI : IsDiscreteValuationRing ((scheme j q hclosed).presheaf.stalk
      ((chartInclusion j q hclosed a).base P)) := by
    change IsDiscreteValuationRing ((sourceSurface X j q hclosed).stalk
      ((chartInclusion j q hclosed a).base P))
    rw [hC]
    exact C.genericPoint_isDiscreteValuationRing
  letI : IsDomain (chartRing (centerIdeal q) (centerParameter q a)) :=
    chartRing_isDomain_of_parameter (centerIdeal q) (centerParameter q a) ha
  letI : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (globalStalkEquiv j q hclosed a P hPq)
  exact prime_eq_chartCenterIdeal (centerIdeal q) (centerParameter q a) b ha hb hI Q
    (Ideal.map_le_iff_le_comap.mp
      (localizedChartPrime_center_le q.asIdeal a P.asIdeal hPq))

end KltDP.Geometry.PointBlowupExceptionalPrimeStalk

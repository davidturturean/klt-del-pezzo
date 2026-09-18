import KltDP.Geometry.PointBlowupExceptionalStalkEquiv
import KltDP.Geometry.PointBlowupProjectionStalkCoefficients

/-!
# The original pulled base parameter is an exceptional uniformizer

An original affine coefficient defines its actual germ at the image of
the original source prime. The original projection stalk map and the
proved exceptional-stalk equivalence send that germ to its original
localized Rees coefficient. For the first genuine centre parameter,
this is the previously proved exceptional uniformizer. No pulled-order
or multiplicity hypothesis is supplied.
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
    (C : (sourceSurface X j q hclosed).PrimeCurve)
    (a : q.asIdeal) (P : PrimeSpectrum (chartRing q.asIdeal a))
    (hC : (chartInclusion j q hclosed a).base P = C.genericPoint)

/-- The actual germ of the original affine coefficient at the image of
the original source prime. All point transports come from proved original
chart/projection identities; this definition contains no order formula. -/
def baseCoefficientGerm (r : R) :
    X.stalk ((projection j q hclosed).base C.genericPoint) :=
  (X.toScheme.presheaf.stalkCongr
      (.of_eq (congrArg (projection j q hclosed).base hC))).hom
    ((X.toScheme.presheaf.stalkCongr (.of_eq
      (congrArg (fun f : Spec (CommRingCat.of (chartRing q.asIdeal a)) ⟶ X.toScheme =>
        f.base P) (chartInclusion_projection j q hclosed a)))).inv
      ((openImmersionStalkLocalizationEquiv j
        (PrimeSpectrum.comap (chartBaseMap q.asIdeal a) P)).symm
        (algebraMap R (Localization.AtPrime
          (PrimeSpectrum.comap (chartBaseMap q.asIdeal a) P).asIdeal) r)))

/-- The original projection sends that actual target germ to the actual
original chart coefficient germ at the original source prime. -/
theorem pullback_baseCoefficientGerm (r : R) :
    (projection j q hclosed).stalkMap C.genericPoint
      (baseCoefficientGerm X j q hclosed C a P hC r) =
    ((scheme j q hclosed).presheaf.stalkCongr (.of_eq hC)).hom
      ((openImmersionStalkLocalizationEquiv (chartInclusion j q hclosed a) P).symm
        (algebraMap _ (Localization.AtPrime P.asIdeal) (chartBaseMap q.asIdeal a r))) := by
  let t := (X.toScheme.presheaf.stalkCongr (.of_eq
    (congrArg (fun f : Spec (CommRingCat.of (chartRing q.asIdeal a)) ⟶ X.toScheme =>
      f.base P) (chartInclusion_projection j q hclosed a)))).inv
    ((openImmersionStalkLocalizationEquiv j
      (PrimeSpectrum.comap (chartBaseMap q.asIdeal a) P)).symm
      (algebraMap R (Localization.AtPrime
        (PrimeSpectrum.comap (chartBaseMap q.asIdeal a) P).asIdeal) r))
  have h := ConcreteCategory.congr_hom
    (Scheme.stalkMap_congr_point (projection j q hclosed)
      ((chartInclusion j q hclosed a).base P) C.genericPoint hC) t
  calc
    _ = ((scheme j q hclosed).presheaf.stalkCongr (.of_eq hC)).hom
        ((projection j q hclosed).stalkMap ((chartInclusion j q hclosed a).base P) t) :=
      h.symm
    _ = _ := congrArg
      (((scheme j q hclosed).presheaf.stalkCongr (.of_eq hC)).hom)
      (projection_stalkMap_baseCoefficient j q hclosed a P r)

local instance : (centerIdeal q).IsPrime := by
  dsimp only [centerIdeal]
  rw [Localization.AtPrime.map_eq_maximalIdeal]
  infer_instance

variable (hcenter : (projection j q hclosed).base C.genericPoint = j.base q)
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
        (b : Localization.AtPrime q.asIdeal)})

/-- The original projection stalk map is normalized by the original
exceptional localization, on every original affine base coefficient. -/
theorem exceptionalStalkEquiv_pullback_baseCoefficientGerm (r : R) :
    exceptionalStalkEquiv X j q hclosed C a P hC hcenter b ha hb hI
      ((projection j q hclosed).stalkMap C.genericPoint
        (baseCoefficientGerm X j q hclosed C a P hC r)) =
      exceptionalGenericBaseMap (centerIdeal q) (centerParameter q a) b ha hb hI
        (algebraMap R (Localization.AtPrime q.asIdeal) r) := by
  rw [pullback_baseCoefficientGerm]
  exact exceptionalStalkEquiv_baseCoefficient X j q hclosed C a P hC hcenter b ha hb hI r

include hcenter b ha hb hI in
/-- The genuine first centre parameter becomes an actual irreducible
element under the original projection's original stalk map. -/
theorem pullback_firstParameter_irreducible :
    Irreducible ((projection j q hclosed).stalkMap C.genericPoint
      (baseCoefficientGerm X j q hclosed C a P hC (a : R))) := by
  letI : IsDomain (Localization.AtPrime q.asIdeal) := X.affineLocalization_isDomain j q
  let e := exceptionalStalkEquiv X j q hclosed C a P hC hcenter b ha hb hI
  apply (MulEquiv.irreducible_iff e.toMulEquiv).mp
  have h := exceptionalStalkEquiv_pullback_baseCoefficientGerm
    X j q hclosed C a P hC hcenter b ha hb hI (a : R)
  exact Eq.mpr (congrArg Irreducible h)
    (exceptionalGenericParameter_irreducible (centerIdeal q) (centerParameter q a) b ha hb hI)

include hcenter b ha hb hI in
/-- The original target parameter germ is nonzero, derived from its
proved irreducible image under the original projection stalk map. -/
theorem firstParameterGerm_ne_zero :
    baseCoefficientGerm X j q hclosed C a P hC (a : R) ≠ 0 := by
  letI : IsDomain ((scheme j q hclosed).presheaf.stalk C.genericPoint) :=
    (inferInstance : IsDomain ((sourceSurface X j q hclosed).stalk C.genericPoint))
  intro hzero
  apply (pullback_firstParameter_irreducible X j q hclosed C a P hC hcenter b ha hb hI).ne_zero
  exact (congrArg ((projection j q hclosed).stalkMap C.genericPoint) hzero).trans
    ((projection j q hclosed).stalkMap C.genericPoint).hom.map_zero

end KltDP.Geometry.PointBlowupExceptionalPrimeStalk

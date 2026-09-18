import KltDP.Geometry.PointBlowupExceptionalPullbackParameter

/-!
# Original coefficient germs in the actual centre localization

The target point is identified with the original closed centre by the
actual projection equation. The original affine open-stalk equivalence
then identifies its local ring with the original prime localization.
The proved point transports carry every original affine coefficient to
its literal localization image, so SNC parameters need no alignment premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

private theorem stalkCongr_three_coefficients (X : Scheme.{u})
    {x y z w : X} (hxy : x = y) (hxz : x = z) (hzw : z = w)
    (t : X.presheaf.stalk y) :
    (X.presheaf.stalkCongr (.of_eq hzw)).hom
        ((X.presheaf.stalkCongr (.of_eq hxz)).hom
          ((X.presheaf.stalkCongr (.of_eq hxy)).inv t)) =
      (X.presheaf.stalkCongr (.of_eq ((hxy.symm.trans hxz).trans hzw))).hom t := by
  subst y
  subst z
  subst w
  simp [TopCat.Presheaf.stalkCongr]

private theorem openChart_coefficient_point_transport
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (p q : PrimeSpectrum R) (h : j.base p = j.base q) (r : R) :
    (X.presheaf.stalkCongr (.of_eq h)).hom
        ((openImmersionStalkLocalizationEquiv j p).symm
          (algebraMap R (Localization.AtPrime p.asIdeal) r)) =
      (openImmersionStalkLocalizationEquiv j q).symm
        (algebraMap R (Localization.AtPrime q.asIdeal) r) := by
  have hpq : p = q := j.isOpenEmbedding.injective h
  subst q
  simp [TopCat.Presheaf.stalkCongr]

namespace PointBlowupExceptionalPrimeStalk

open AffineBlowup PointBlowupGluing PointBlowupChartStalk

variable {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))
    (C : (sourceSurface X j q hclosed).PrimeCurve)
    (hcenter : (projection j q hclosed).base C.genericPoint = j.base q)

/-- The actual target-centre local-ring equivalence. Its definition uses
only the original point equality and the original open-chart stalk map. -/
def centerStalkEquiv :
    X.stalk ((projection j q hclosed).base C.genericPoint) ≃+*
      Localization.AtPrime q.asIdeal :=
  ((X.toScheme.presheaf.stalkCongr (.of_eq hcenter)).commRingCatIsoToRingEquiv).trans
    (openImmersionStalkLocalizationEquiv j q)

variable (a : q.asIdeal) (P : PrimeSpectrum (chartRing q.asIdeal a))
    (hC : (chartInclusion j q hclosed a).base P = C.genericPoint)

/-- The original affine coefficient germ is transported to the original
centre through the proved chart/projection and centre point identities. -/
theorem baseCoefficientGerm_center_transport (r : R) :
    (X.toScheme.presheaf.stalkCongr (.of_eq hcenter)).hom
        (baseCoefficientGerm X j q hclosed C a P hC r) =
      (openImmersionStalkLocalizationEquiv j q).symm
        (algebraMap R (Localization.AtPrime q.asIdeal) r) := by
  let p := PrimeSpectrum.comap (chartBaseMap q.asIdeal a) P
  have hs : (projection j q hclosed).base ((chartInclusion j q hclosed a).base P) =
      j.base p := congrArg
    (fun f : Spec (CommRingCat.of (chartRing q.asIdeal a)) ⟶ X.toScheme => f.base P)
      (chartInclusion_projection j q hclosed a)
  have ht : (projection j q hclosed).base ((chartInclusion j q hclosed a).base P) =
      (projection j q hclosed).base C.genericPoint := congrArg (projection j q hclosed).base hC
  have he : j.base p = j.base q := (hs.symm.trans ht).trans hcenter
  calc
    _ = (X.toScheme.presheaf.stalkCongr (.of_eq he)).hom
        ((openImmersionStalkLocalizationEquiv j p).symm
          (algebraMap R (Localization.AtPrime p.asIdeal) r)) :=
      stalkCongr_three_coefficients X.toScheme hs ht hcenter _
    _ = _ := openChart_coefficient_point_transport j p q he r

/-- The actual centre equivalence sends each actual original coefficient
germ to its literal original localization image. -/
theorem centerStalkEquiv_baseCoefficient (r : R) :
    centerStalkEquiv X j q hclosed C hcenter
        (baseCoefficientGerm X j q hclosed C a P hC r) =
      algebraMap R (Localization.AtPrime q.asIdeal) r := by
  change openImmersionStalkLocalizationEquiv j q
    ((X.toScheme.presheaf.stalkCongr (.of_eq hcenter)).hom
      (baseCoefficientGerm X j q hclosed C a P hC r)) = _
  exact (congrArg (openImmersionStalkLocalizationEquiv j q)
    (baseCoefficientGerm_center_transport X j q hclosed C hcenter a P hC r)).trans
      ((openImmersionStalkLocalizationEquiv j q).apply_symm_apply _)

end PointBlowupExceptionalPrimeStalk
end KltDP.Geometry

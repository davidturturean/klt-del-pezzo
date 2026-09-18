import KltDP.Geometry.AffineBlowupChartStalkAtCenter
import KltDP.Geometry.PointBlowupGluing
import KltDP.Geometry.SurfaceRegularCharts

/-!
# Original whole-blowup stalks and the original centre localization

The actual Rees chart open immersion gives the first stalk equivalence;
the original chart map under base localization gives the second. The
original projection square is retained on stalk maps. No exceptional
multiplicity, generic-point identification, or coefficient is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.PointBlowupChartStalk

open AffineBlowup AffineBlowupChartBaseChange PointBlowupGluing

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X)) (a : q.asIdeal)

/-- The original Rees chart inclusion into the original whole blowup. -/
abbrev chartInclusion := chartι q.asIdeal a ≫ affineBlowupι j q hclosed

/-- The literal original projection square on this Rees chart. -/
theorem chartInclusion_projection :
    chartInclusion j q hclosed a ≫ projection j q hclosed =
      Spec.map (CommRingCat.ofHom (chartBaseMap q.asIdeal a)) ≫ j := by
  rw [chartInclusion, Category.assoc, affineBlowupι_projection,
    ← Category.assoc, chartι_toSpec]
  rfl

variable (P : PrimeSpectrum (chartRing q.asIdeal a))

/-- The original projection square, now as equality of the actual stalk
maps. The only transport is the proved equality of the original points. -/
theorem chartInclusion_projection_stalkMap :
    (projection j q hclosed).stalkMap ((chartInclusion j q hclosed a).base P) ≫
        (chartInclusion j q hclosed a).stalkMap P =
      (X.presheaf.stalkCongr (.of_eq
        (congrArg (fun f : Spec (CommRingCat.of (chartRing q.asIdeal a)) ⟶ X => f.base P)
          (chartInclusion_projection j q hclosed a)))).hom ≫
        j.stalkMap (PrimeSpectrum.comap (chartBaseMap q.asIdeal a) P) ≫
        (Spec.map (CommRingCat.ofHom (chartBaseMap q.asIdeal a))).stalkMap P := by
  simpa only [Scheme.stalkMap_comp, Category.assoc] using
    Scheme.stalkMap_congr_hom
      (chartInclusion j q hclosed a ≫ projection j q hclosed)
      (Spec.map (CommRingCat.ofHom (chartBaseMap q.asIdeal a)) ≫ j)
      (chartInclusion_projection j q hclosed a) P

variable (hPq : P.asIdeal.comap (chartBaseMap q.asIdeal a) = q.asIdeal)

include hPq in
/-- The original image point is the original centre, derived from the
actual prime's image under the actual chart base map. -/
theorem projection_chartPoint :
    (projection j q hclosed).base ((chartInclusion j q hclosed a).base P) = j.base q := by
  change (chartInclusion j q hclosed a ≫ projection j q hclosed).base P = _
  rw [chartInclusion_projection]
  change j.base (PrimeSpectrum.comap (chartBaseMap q.asIdeal a) P) = j.base q
  exact congrArg j.base (PrimeSpectrum.ext hPq)

/-- The literal whole-blowup stalk is identified with the chart stalk
over the original centre localization through the two original maps. -/
def globalStalkEquiv :
    (scheme j q hclosed).presheaf.stalk ((chartInclusion j q hclosed a).base P) ≃+*
      Localization.AtPrime (localizedChartPrime q.asIdeal a q.asIdeal P.asIdeal hPq) :=
  (openImmersionStalkLocalizationEquiv (chartInclusion j q hclosed a) P).trans
    (originalChartStalkEquiv q.asIdeal a q.asIdeal P.asIdeal hPq)

/-- Every original chart coefficient is retained by the whole-stalk
comparison and the original localized chart map. -/
theorem globalStalkEquiv_chartCoefficient (z : chartRing q.asIdeal a) :
    globalStalkEquiv j q hclosed a P hPq
      ((openImmersionStalkLocalizationEquiv (chartInclusion j q hclosed a) P).symm
        (algebraMap _ (Localization.AtPrime P.asIdeal) z)) =
      algebraMap _
        (Localization.AtPrime (localizedChartPrime q.asIdeal a q.asIdeal P.asIdeal hPq))
        (chartMap q.asIdeal (algebraMap R (Localization.AtPrime q.asIdeal)) a z) := by
  change originalChartStalkEquiv q.asIdeal a q.asIdeal P.asIdeal hPq
    ((openImmersionStalkLocalizationEquiv (chartInclusion j q hclosed a) P)
      ((openImmersionStalkLocalizationEquiv (chartInclusion j q hclosed a) P).symm
        (algebraMap _ (Localization.AtPrime P.asIdeal) z))) = _
  rw [RingEquiv.apply_symm_apply]
  exact originalChartStalkEquiv_to_map q.asIdeal a q.asIdeal P.asIdeal hPq z

end KltDP.Geometry.PointBlowupChartStalk

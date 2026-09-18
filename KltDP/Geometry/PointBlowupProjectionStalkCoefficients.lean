import KltDP.Geometry.PointBlowupChartStalkAtCenter

/-!
# Original point-blowup projection on actual affine coefficient germs

The pinned Spec stalk map preserves the original ring coefficient.
The actual open-immersion stalk isomorphisms and the original projection
square transport that equality to the whole blowup. No commutation or
coefficient equality is assumed for the original point-blowup endpoint.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

private theorem openChart_stalkMap_localizedCoefficient
    {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (j : Spec (CommRingCat.of R) ⟶ Y) [IsOpenImmersion j]
    (p : PrimeSpectrum R) (r : R) :
    j.stalkMap p ((openImmersionStalkLocalizationEquiv j p).symm
      (algebraMap R (Localization.AtPrime p.asIdeal) r)) =
        StructureSheaf.toStalk R p r := by
  change (asIso (j.stalkMap p)).hom
    ((asIso (j.stalkMap p)).inv
      ((StructureSheaf.stalkIso R p).inv
        (algebraMap R (Localization.AtPrime p.asIdeal) r))) = _
  rw [Iso.inv_hom_id_apply]
  exact StructureSheaf.localizationToStalk_of R p r

private theorem openChartSquare_stalkMap_localizedCoefficient
    {R A : Type u} [CommRing R] [CommRing A] {X Y : Scheme.{u}}
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (i : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion i]
    (π : Y ⟶ X) (ρ : R →+* A)
    (h : i ≫ π = Spec.map (CommRingCat.ofHom ρ) ≫ j)
    (p : PrimeSpectrum A) (r : R) :
    π.stalkMap (i.base p)
      ((X.presheaf.stalkCongr (.of_eq
        (congrArg (fun f : Spec (CommRingCat.of A) ⟶ X => f.base p) h))).inv
        ((openImmersionStalkLocalizationEquiv j (PrimeSpectrum.comap ρ p)).symm
          (algebraMap R (Localization.AtPrime (PrimeSpectrum.comap ρ p).asIdeal) r))) =
      (openImmersionStalkLocalizationEquiv i p).symm
        (algebraMap A (Localization.AtPrime p.asIdeal) (ρ r)) := by
  let e := X.presheaf.stalkCongr (.of_eq
    (congrArg (fun f : Spec (CommRingCat.of A) ⟶ X => f.base p) h))
  let t := (openImmersionStalkLocalizationEquiv j (PrimeSpectrum.comap ρ p)).symm
    (algebraMap R (Localization.AtPrime (PrimeSpectrum.comap ρ p).asIdeal) r)
  have hs : π.stalkMap (i.base p) ≫ i.stalkMap p =
      e.hom ≫ j.stalkMap (PrimeSpectrum.comap ρ p) ≫
        (Spec.map (CommRingCat.ofHom ρ)).stalkMap p := by
    simpa only [Scheme.stalkMap_comp, Category.assoc] using
      Scheme.stalkMap_congr_hom (i ≫ π) (Spec.map (CommRingCat.ofHom ρ) ≫ j) h p
  apply (asIso (i.stalkMap p)).commRingCatIsoToRingEquiv.injective
  have hhraw := RingHom.congr_fun (congrArg CommRingCat.Hom.hom hs) (e.inv t)
  change i.stalkMap p (π.stalkMap (i.base p) (e.inv t)) =
    (Spec.map (CommRingCat.ofHom ρ)).stalkMap p
      (j.stalkMap (PrimeSpectrum.comap ρ p) (e.hom (e.inv t))) at hhraw
  have he : e.hom (e.inv t) = t := by
    have he := ConcreteCategory.congr_hom e.inv_hom_id t
    change e.hom (e.inv t) = t at he
    exact he
  have hh : i.stalkMap p (π.stalkMap (i.base p) (e.inv t)) =
      (Spec.map (CommRingCat.ofHom ρ)).stalkMap p
        (j.stalkMap (PrimeSpectrum.comap ρ p) t) :=
    hhraw.trans (congrArg (fun z => (Spec.map (CommRingCat.ofHom ρ)).stalkMap p
      (j.stalkMap (PrimeSpectrum.comap ρ p) z)) he)
  calc
    i.stalkMap p (π.stalkMap (i.base p) (e.inv t)) =
        (Spec.map (CommRingCat.ofHom ρ)).stalkMap p
          (j.stalkMap (PrimeSpectrum.comap ρ p) t) := hh
    _ = (Spec.map (CommRingCat.ofHom ρ)).stalkMap p
        (StructureSheaf.toStalk R (PrimeSpectrum.comap ρ p) r) :=
      congrArg ((Spec.map (CommRingCat.ofHom ρ)).stalkMap p)
        (openChart_stalkMap_localizedCoefficient j (PrimeSpectrum.comap ρ p) r)
    _ = StructureSheaf.toStalk A p (ρ r) :=
      AlgebraicGeometry.stalkMap_toStalk_apply (CommRingCat.ofHom ρ) p r
    _ = i.stalkMap p ((openImmersionStalkLocalizationEquiv i p).symm
        (algebraMap A (Localization.AtPrime p.asIdeal) (ρ r))) :=
      (openChart_stalkMap_localizedCoefficient i p (ρ r)).symm

/-- Public normalization of an original affine coefficient in its actual open-chart stalk. -/
alias openChart_stalkMap_coefficient := openChart_stalkMap_localizedCoefficient

/-- Public form of the actual open-chart stalk coefficient square. -/
alias openChartSquare_stalkMap_coefficient := openChartSquare_stalkMap_localizedCoefficient

namespace PointBlowupChartStalk

open AffineBlowup PointBlowupGluing

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X)) (a : q.asIdeal)
    (P : PrimeSpectrum (chartRing q.asIdeal a))

/-- The actual whole projection sends the original affine coefficient
germ to the original Rees-chart coefficient germ. The only point transport
comes from its proved original projection square. -/
theorem projection_stalkMap_baseCoefficient (r : R) :
    (projection j q hclosed).stalkMap ((chartInclusion j q hclosed a).base P)
      ((X.presheaf.stalkCongr (.of_eq
        (congrArg (fun f : Spec (CommRingCat.of (chartRing q.asIdeal a)) ⟶ X => f.base P)
          (chartInclusion_projection j q hclosed a)))).inv
        ((openImmersionStalkLocalizationEquiv j
          (PrimeSpectrum.comap (chartBaseMap q.asIdeal a) P)).symm
          (algebraMap R (Localization.AtPrime
            (PrimeSpectrum.comap (chartBaseMap q.asIdeal a) P).asIdeal) r))) =
      (openImmersionStalkLocalizationEquiv (chartInclusion j q hclosed a) P).symm
        (algebraMap _ (Localization.AtPrime P.asIdeal) (chartBaseMap q.asIdeal a r)) :=
  openChartSquare_stalkMap_localizedCoefficient j (chartInclusion j q hclosed a)
    (projection j q hclosed) (chartBaseMap q.asIdeal a)
    (chartInclusion_projection j q hclosed a) P r

end PointBlowupChartStalk

end KltDP.Geometry

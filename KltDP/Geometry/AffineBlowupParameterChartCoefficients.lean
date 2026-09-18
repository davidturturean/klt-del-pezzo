import KltDP.Geometry.AffineBlowupParameterChartPoints
import KltDP.Geometry.PointBlowupProjectionStalkCoefficients

/-!
# Actual base coefficients across the original Rees charts

The generic original open-chart coefficient square is reused through its
public export. Normalizing only the identity base chart and equality of
points identifies its coefficient with the original structure-map stalk
pullback. The actual two-chart stalk equivalence therefore preserves every
original base coefficient. No commuting-square hypothesis is added for
the original Rees charts.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

private theorem identityChart_coefficient {R : Type u} [CommRing R]
    (p : PrimeSpectrum R) (r : R) :
    (openImmersionStalkLocalizationEquiv (𝟙 (Spec (CommRingCat.of R))) p).symm
      (algebraMap R (Localization.AtPrime p.asIdeal) r) = StructureSheaf.toStalk R p r := by
  have h := openChart_stalkMap_coefficient (𝟙 (Spec (CommRingCat.of R))) p r
  rw [Scheme.stalkMap_id] at h
  exact h

private theorem stalkCongr_inv_toStalk {R : Type u} [CommRing R]
    (p q : PrimeSpectrum R) (h : p = q) (r : R) :
    ((Spec (CommRingCat.of R)).presheaf.stalkCongr (.of_eq h)).inv
      (StructureSheaf.toStalk R q r) = StructureSheaf.toStalk R p r := by
  subst q
  change (Spec (CommRingCat.of R)).presheaf.stalkSpecializes (specializes_refl p)
    (StructureSheaf.toStalk R p r) = _
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

private theorem stalkCongr_projection_toStalk {R : Type u} [CommRing R]
    {Y : Scheme.{u}} (π : Y ⟶ Spec (CommRingCat.of R))
    (x y : Y) (h : x = y) (r : R) :
    (Y.presheaf.stalkCongr (.of_eq h)).hom
      (π.stalkMap x (StructureSheaf.toStalk R (π.base x) r)) =
      π.stalkMap y (StructureSheaf.toStalk R (π.base y) r) := by
  subst y
  change Y.presheaf.stalkSpecializes (specializes_refl x)
    (π.stalkMap x (StructureSheaf.toStalk R (π.base x) r)) = _
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- An actual affine chart over the original affine base identifies
its base coefficient with the original structure-map stalk pullback. -/
theorem openChart_projection_coefficient
    {R A : Type u} [CommRing R] [CommRing A] {Y : Scheme.{u}}
    (i : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion i]
    (π : Y ⟶ Spec (CommRingCat.of R)) (ρ : R →+* A)
    (h : i ≫ π = Spec.map (CommRingCat.ofHom ρ))
    (p : PrimeSpectrum A) (r : R) :
    (openImmersionStalkLocalizationEquiv i p).symm
      (algebraMap A (Localization.AtPrime p.asIdeal) (ρ r)) =
      π.stalkMap (i.base p) (StructureSheaf.toStalk R (π.base (i.base p)) r) := by
  have h' : i ≫ π = Spec.map (CommRingCat.ofHom ρ) ≫ 𝟙 (Spec (CommRingCat.of R)) :=
    h.trans (Category.comp_id _).symm
  have hs := openChartSquare_stalkMap_coefficient
    (𝟙 (Spec (CommRingCat.of R))) i π ρ h' p r
  rw [identityChart_coefficient] at hs
  have hpoint : π.base (i.base p) = PrimeSpectrum.comap ρ p :=
    congrArg (fun f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) => f.base p) h
  calc
    _ = π.stalkMap (i.base p)
        (((Spec (CommRingCat.of R)).presheaf.stalkCongr (.of_eq hpoint)).inv
          (StructureSheaf.toStalk R (PrimeSpectrum.comap ρ p) r)) := hs.symm
    _ = _ := congrArg (π.stalkMap (i.base p))
      (stalkCongr_inv_toStalk (π.base (i.base p)) (PrimeSpectrum.comap ρ p) hpoint r)

namespace AffineBlowup

variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)
variable (p : PrimeSpectrum (chartRing I a)) (q : PrimeSpectrum (chartRing I b))
variable (h : (chartι I a).base p = (chartι I b).base q)

/-- The original native two-chart stalk equivalence preserves every
original base coefficient, through the literal chart base maps. -/
theorem parameterChartStalkEquiv_baseMap (r : R) :
    parameterChartStalkEquiv I a b p q h
      (algebraMap (chartRing I a) (Localization.AtPrime p.asIdeal) (chartBaseMap I a r)) =
      algebraMap (chartRing I b) (Localization.AtPrime q.asIdeal) (chartBaseMap I b r) := by
  have ha := openChart_projection_coefficient (chartι I a) (toSpec I)
    (chartBaseMap I a) (chartι_toSpec I a) p r
  have hb := openChart_projection_coefficient (chartι I b) (toSpec I)
    (chartBaseMap I b) (chartι_toSpec I b) q r
  change (openImmersionStalkLocalizationEquiv (chartι I b) q)
    (((scheme I).presheaf.stalkCongr (.of_eq h)).hom
      ((openImmersionStalkLocalizationEquiv (chartι I a) p).symm
        (algebraMap (chartRing I a) (Localization.AtPrime p.asIdeal) (chartBaseMap I a r)))) = _
  rw [ha, stalkCongr_projection_toStalk (toSpec I)
    ((chartι I a).base p) ((chartι I b).base q) h r, ← hb, RingEquiv.apply_symm_apply]

end AffineBlowup
end KltDP.Geometry

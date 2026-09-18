import KltDP.Geometry.AffineBlowupChartBaseChangeFlat
import KltDP.Geometry.FlatSurjectiveLocalRingIso
import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks

/-! Original affine Rees charts after localization of their original base ring. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace KltDP.Geometry.AffineBlowupChartBaseChange

open AffineBlowup

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
variable (I : Ideal R) (φ : R →+* S)

/-- Surjectivity on stalks passes through the actual flat blowup comparison. -/
theorem comparison_surjectiveOnStalks
    [hflat : Flat (Spec.map (CommRingCat.ofHom φ))]
    [hsurj : SurjectiveOnStalks (Spec.map (CommRingCat.ofHom φ))] :
    SurjectiveOnStalks (openBaseChangeMap I φ) := by
  have hfst : SurjectiveOnStalks
      (pullback.fst (toSpec I) (Spec.map (CommRingCat.ofHom φ))) :=
    MorphismProperty.pullback_fst (P := @SurjectiveOnStalks) (toSpec I)
      (Spec.map (CommRingCat.ofHom φ)) hsurj
  rw [← openBaseChangeToPullback_fst I φ]
  change SurjectiveOnStalks ((flatBaseChangeIso I φ).hom ≫ pullback.fst _ _)
  exact IsLocalAtSource.comp hfst (flatBaseChangeIso I φ).hom

/-- The original affine chart map inherits surjectivity on stalks. -/
theorem chartMap_surjectiveOnStalks (a : I)
    [Flat (Spec.map (CommRingCat.ofHom φ))]
    [SurjectiveOnStalks (Spec.map (CommRingCat.ofHom φ))] :
    (chartMap I φ a).SurjectiveOnStalks := by
  letI : SurjectiveOnStalks (openBaseChangeMap I φ) :=
    comparison_surjectiveOnStalks I φ
  haveI : SurjectiveOnStalks
      (Spec.map (CommRingCat.ofHom (chartMap I φ a)) ≫ chartι I a) := by
    rw [chartMap_chartι]
    infer_instance
  exact SurjectiveOnStalks.Spec_iff.mp (SurjectiveOnStalks.of_comp
    (Spec.map (CommRingCat.ofHom (chartMap I φ a))) (chartι I a))

variable [Algebra R S]

/-- Localizing the base induces a bijection on the original local rings at
every corresponding chart point. -/
theorem localization_localRingHom_bijective (M : Submonoid R) [IsLocalization M S] (a : I)
    (Q : Ideal (chartRing (I.map (algebraMap R S))
      (mappedElement I (algebraMap R S) a))) [Q.IsPrime] :
    Function.Bijective (Localization.localRingHom
      (Q.comap (chartMap I (algebraMap R S) a)) Q
      (chartMap I (algebraMap R S) a) rfl) := by
  letI : Module.Flat R S := IsLocalization.flat S M
  letI : Flat (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mpr
      (flat_algebraMap_iff.mpr inferInstance)
  letI : SurjectiveOnStalks (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    SurjectiveOnStalks.Spec_iff.mpr (RingHom.surjectiveOnStalks_of_isLocalization M S)
  exact FlatSurjectiveLocalRingIso.bijective _
    ((chartMap_flat I (algebraMap R S) a).localRingHom Q _ rfl)
    (chartMap_surjectiveOnStalks I (algebraMap R S) a Q inferInstance)

/-- This equivalence is literally induced by the original chart ring map. -/
def localizationLocalRingEquiv (M : Submonoid R) [IsLocalization M S] (a : I)
    (Q : Ideal (chartRing (I.map (algebraMap R S))
      (mappedElement I (algebraMap R S) a))) [Q.IsPrime] :
    Localization.AtPrime (Q.comap (chartMap I (algebraMap R S) a)) ≃+*
      Localization.AtPrime Q :=
  RingEquiv.ofBijective _ (localization_localRingHom_bijective I M a Q)

@[simp]
theorem localizationLocalRingEquiv_to_map (M : Submonoid R) [IsLocalization M S] (a : I)
    (Q : Ideal (chartRing (I.map (algebraMap R S))
      (mappedElement I (algebraMap R S) a))) [Q.IsPrime] (z : chartRing I a) :
    localizationLocalRingEquiv I M a Q
      (algebraMap _ (Localization.AtPrime (Q.comap (chartMap I (algebraMap R S) a))) z) =
      algebraMap _ (Localization.AtPrime Q) (chartMap I (algebraMap R S) a z) :=
  Localization.localRingHom_to_map _ _ _ rfl z

@[simp]
theorem localizationLocalRingEquiv_baseMap (M : Submonoid R) [IsLocalization M S] (a : I)
    (Q : Ideal (chartRing (I.map (algebraMap R S))
      (mappedElement I (algebraMap R S) a))) [Q.IsPrime] (r : R) :
    localizationLocalRingEquiv I M a Q
      (algebraMap _ (Localization.AtPrime (Q.comap (chartMap I (algebraMap R S) a)))
        (chartBaseMap I a r)) =
      algebraMap _ (Localization.AtPrime Q)
        (chartBaseMap (I.map (algebraMap R S)) (mappedElement I (algebraMap R S) a)
          (algebraMap R S r)) := by
  rw [localizationLocalRingEquiv_to_map, chartMap_baseMap]
  rfl

@[simp]
theorem localizationLocalRingEquiv_fraction (M : Submonoid R) [IsLocalization M S] (a b : I)
    (Q : Ideal (chartRing (I.map (algebraMap R S))
      (mappedElement I (algebraMap R S) a))) [Q.IsPrime] :
    localizationLocalRingEquiv I M a Q
      (algebraMap _ (Localization.AtPrime (Q.comap (chartMap I (algebraMap R S) a)))
        (chartFraction I a b)) =
      algebraMap _ (Localization.AtPrime Q)
        (chartFraction (I.map (algebraMap R S)) (mappedElement I (algebraMap R S) a)
          (mappedElement I (algebraMap R S) b)) := by
  rw [localizationLocalRingEquiv_to_map, chartMap_fraction]

end KltDP.Geometry.AffineBlowupChartBaseChange

import KltDP.Geometry.AffineBlowupChartBaseChangeMap
import KltDP.Geometry.AffineBlowupFlatBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Étaleness of the actual map between original Rees charts

The chart map agrees with the original global blowup comparison by the
existing uniqueness theorem. For a flat étale base map that comparison is
étale by the proved actual blowup base-change isomorphism. Postcomposing the
chart map with the original open chart immersion gives the restriction of
that étale comparison; the pinned base-change cancellation along monomorphisms
then proves that the original chart map itself is étale.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace KltDP.Geometry.AffineBlowupChartBaseChange

open AffineBlowup

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
variable (I : Ideal R) (φ : R →+* S) (a : I)

/-- The actual affine chart lift is the original global comparison on this chart. -/
theorem chartMap_chartι :
    Spec.map (CommRingCat.ofHom (chartMap I φ a)) ≫ chartι I a =
      chartι (Ideal.map φ I) (mappedElement I φ a) ≫ openBaseChangeMap I φ := by
  symm
  change chartι (Ideal.map φ I) (mappedElement I φ a) ≫ openBaseChangeMap I φ =
    affineLift I a (baseMap I φ a) (baseMap_regular I φ a) (mappedCenter_span I φ a).le
  apply affineLift_unique
  rw [Category.assoc, openBaseChangeMap_toSpec, ← Category.assoc, chartι_toSpec]
  change Spec.map (CommRingCat.ofHom
      (chartBaseMap (Ideal.map φ I) (mappedElement I φ a))) ≫
      Spec.map (CommRingCat.ofHom φ) =
    Spec.map (CommRingCat.ofHom
      ((chartBaseMap (Ideal.map φ I) (mappedElement I φ a)).comp φ))
  exact (Spec.map_comp (CommRingCat.ofHom φ)
    (CommRingCat.ofHom (chartBaseMap (Ideal.map φ I) (mappedElement I φ a)))).symm

variable [hFlat : Flat (Spec.map (CommRingCat.ofHom φ))]
variable [hEtale : IsEtale (Spec.map (CommRingCat.ofHom φ))]

include hFlat hEtale in
/-- Étaleness is inherited by the original global blowup comparison. -/
theorem comparison_isEtale : IsEtale (openBaseChangeMap I φ) := by
  have hfst : IsEtale (pullback.fst (toSpec I) (Spec.map (CommRingCat.ofHom φ))) :=
    MorphismProperty.pullback_fst (P := @IsEtale) (toSpec I)
      (Spec.map (CommRingCat.ofHom φ)) hEtale
  rw [← openBaseChangeToPullback_fst I φ]
  change IsEtale ((flatBaseChangeIso I φ).hom ≫ pullback.fst _ _)
  exact IsLocalAtSource.comp hfst (flatBaseChangeIso I φ).hom

include hFlat hEtale in
/-- The original chart ring map defines an étale morphism of actual affine schemes. -/
theorem chartMap_isEtale : IsEtale (Spec.map (CommRingCat.ofHom (chartMap I φ a))) := by
  letI : IsEtale (openBaseChangeMap I φ) := comparison_isEtale I φ
  have hcomp : IsEtale (Spec.map (CommRingCat.ofHom (chartMap I φ a)) ≫ chartι I a) := by
    rw [chartMap_chartι]
    infer_instance
  exact MorphismProperty.of_postcomp @IsEtale
    (W' := MorphismProperty.monomorphisms Scheme)
    (Spec.map (CommRingCat.ofHom (chartMap I φ a))) (chartι I a)
    (show Mono (chartι I a) from inferInstance) hcomp

end KltDP.Geometry.AffineBlowupChartBaseChange

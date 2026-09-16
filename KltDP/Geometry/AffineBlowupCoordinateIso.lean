import KltDP.Geometry.AffineBlowupOpenBaseChange

/-!
# Actual affine blowup invariance under a coordinate isomorphism

An actual scheme isomorphism between two affine schemes determines an
actual isomorphism of their coordinate rings by the fully faithful Spec
functor. If it identifies two specified points, extension of the first
point ideal is exactly the second point ideal. This equality and the
proved open-base-change comparison construct an actual Rees blowup
isomorphism. No blowup invariance or ideal comparison is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.AffineBlowup

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Transporting an actual ideal equality commutes with the actual Rees projection. -/
theorem eqToHom_toSpec {I J : Ideal R} (h : I = J) :
    eqToHom (congrArg scheme h) ≫ toSpec J = toSpec I := by
  subst J
  simp

variable (e : Spec (CommRingCat.of S) ≅ Spec (CommRingCat.of R))

/-- The actual coordinate-ring isomorphism extracted through fully faithful Spec. -/
def coordinateRingIso : CommRingCat.of R ≅ CommRingCat.of S :=
  (Scheme.Spec.preimageIso e).unop

theorem coordinateRingIso_hom : (coordinateRingIso e).hom = Spec.preimage e.hom := rfl

theorem coordinateMap_bijective : Function.Bijective (Spec.preimage e.hom).hom := by
  haveI : IsIso (Spec.preimage e.hom) := by
    rw [← coordinateRingIso_hom]
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective (Spec.preimage e.hom)).mp inferInstance

variable (qR : PrimeSpectrum R) (qS : PrimeSpectrum S)
    (hpoint : e.hom.base qS = qR)

include hpoint in
/-- The actual point identification forces the exact extension of ideals. -/
theorem coordinateMap_center :
    Ideal.map (Spec.preimage e.hom).hom qR.asIdeal = qS.asIdeal := by
  have hcomap : Ideal.comap (Spec.preimage e.hom).hom qS.asIdeal = qR.asIdeal := by
    have hp : PrimeSpectrum.comap (Spec.preimage e.hom).hom qS = qR := by
      change (Spec.map (Spec.preimage e.hom)).base qS = qR
      rw [Spec.map_preimage]
      exact hpoint
    exact congrArg PrimeSpectrum.asIdeal hp
  rw [← hcomap]
  exact Ideal.map_comap_of_surjective _ (coordinateMap_bijective e).surjective _

/-- The affine blowup comparison for an isomorphic base is itself an isomorphism. -/
theorem coordinateBaseChangeMap_isIso (I : Ideal R) :
    IsIso (openBaseChangeMap I (Spec.preimage e.hom).hom) := by
  haveI : IsIso (Spec.map (CommRingCat.ofHom (Spec.preimage e.hom).hom)) := by
    change IsIso (Spec.map (Spec.preimage e.hom))
    rw [Spec.map_preimage]
    infer_instance
  rw [← openBaseChangeToPullback_fst]
  change IsIso ((openBaseChangeIso I (Spec.preimage e.hom).hom).hom ≫ pullback.fst _ _)
  infer_instance

/-- The actual Rees blowups at the identified points are isomorphic. -/
def coordinateBlowupIso : scheme qS.asIdeal ≅ scheme qR.asIdeal := by
  haveI := coordinateBaseChangeMap_isIso e qR.asIdeal
  exact eqToIso (congrArg scheme (coordinateMap_center e qR qS hpoint).symm) ≪≫
    asIso (openBaseChangeMap qR.asIdeal (Spec.preimage e.hom).hom)

/-- The constructed isomorphism lies over the original affine coordinate isomorphism. -/
theorem coordinateBlowupIso_hom_toSpec :
    (coordinateBlowupIso e qR qS hpoint).hom ≫ toSpec qR.asIdeal =
      toSpec qS.asIdeal ≫ e.hom := by
  change (eqToHom (congrArg scheme (coordinateMap_center e qR qS hpoint).symm) ≫
    openBaseChangeMap qR.asIdeal (Spec.preimage e.hom).hom) ≫ toSpec qR.asIdeal = _
  rw [Category.assoc, openBaseChangeMap_toSpec, ← Category.assoc,
    eqToHom_toSpec (coordinateMap_center e qR qS hpoint).symm]
  change toSpec qS.asIdeal ≫ Spec.map (Spec.preimage e.hom) = toSpec qS.asIdeal ≫ e.hom
  rw [Spec.map_preimage]

end KltDP.Geometry.AffineBlowup

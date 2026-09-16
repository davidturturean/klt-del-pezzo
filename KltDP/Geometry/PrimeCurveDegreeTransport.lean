import KltDP.Geometry.PrimeCurveRestrictionDegree
import KltDP.Geometry.SchemeIsoEulerTransport
import KltDP.Geometry.RationalTreePicardMultidegree

/-!
# Transport of the degree of a prime curve along an isomorphism

For a prime curve `C` of a normal projective surface and an isomorphism `φ : C.toScheme ⟶ G`
over `k` (`φ ≫ g = C.toSpec`), the degree on `C` of the pullback along `φ` of a Picard class `p`
of `G` is the Euler value of `p` on `G` relative to the unit (`picardDegree_pullback_iso`), by the
accepted Euler transport along isomorphisms. Two prime curves isomorphic over `k` to the same
scheme therefore have the same degree on pulled-back classes.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PrimeCurveDegreeTransport

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface KltDP.Geometry.ModuleCohomology

variable {k : Type u} [Field k]

/-- The Euler value of a Picard class of `G` relative to the unit, for the base `g : G ⟶ Spec k`. -/
def eulerDegree {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of k)) (p : G.Pic) : ℤ :=
  picardEulerValue g p - picardEulerValue g 1

variable {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
variable {G : Scheme.{u}} (φ : C.toScheme ⟶ G) [IsIso φ] (g : G ⟶ Spec (CommRingCat.of k))
variable (hφ : φ ≫ g = C.toSpec)

include hφ in
/-- **Degree transport**: the degree on `C` of `φ^*p` is the Euler degree of `p` on `G`. -/
theorem picardDegree_pullback_iso (p : G.Pic) :
    C.picardDegree (schemePicardPullbackHom φ p) = eulerDegree g p := by
  obtain ⟨L, rfl⟩ := RationalTreePicard.toPic_surjective p
  unfold PrimeCurve.picardDegree eulerDegree
  rw [schemePicardPullbackHom_toPic, picardEulerValue_toPic, picardEulerValue_toPic,
    picardEulerValue_one, picardEulerValue_one]
  have hinv : (asIso φ).symm.hom ≫ C.toSpec = g := by
    rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq, hφ]
  have h1 := eulerCharacteristic_eq_pullback_inv (asIso φ).symm g C.toSpec hinv L.obj
  have h2 := eulerCharacteristic_unit_eq (asIso φ).symm g C.toSpec hinv
  rw [Iso.symm_inv, asIso_hom] at h1
  rw [h1, h2]
  rfl

end KltDP.Geometry.PrimeCurveDegreeTransport

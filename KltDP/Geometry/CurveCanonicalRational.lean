import KltDP.Geometry.CurveCanonicalSchemeIso
import KltDP.Geometry.ProjectiveLineAffineVanishingProved

/-!
# Genus and canonical degree of an original rational curve

Scalar cohomology transports through the actual scheme isomorphism over the
field. The already proved affine vanishing and projective-line computation
therefore give genus zero, and the actual differential degree gives the
canonical degree formula. No new vanishing or duality assumption is used.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.CurveCanonical

open ModuleCohomology

variable {k : Type u} [Field k] {C D : Scheme.{u}}

/-- Scalar cohomological dimensions transport through the inverse of the original isomorphism. -/
theorem cohomologyDimension_eq_pullback_inv (e : C ≅ D)
    (f : C ⟶ Spec (CommRingCat.of k)) (g : D ⟶ Spec (CommRingCat.of k))
    (he : e.hom ≫ g = f) (M : C.Modules) (n : ℕ) :
    cohomologyDimension f M n =
      cohomologyDimension g ((schemeModulePullback e.inv).obj M) n := by
  calc
    cohomologyDimension f M n = cohomologyDimension (e.hom ≫ g) M n := by rw [he]
    _ = cohomologyDimension g ((schemeModulePushforward e.hom).obj M) n :=
      (cohomologyDimension_pushforward_iso e g M n).symm
    _ = cohomologyDimension g ((schemeModulePullback e.inv).obj M) n :=
      cohomologyDimension_eq_of_iso g ((schemeIsoPushforwardPullbackIso e).app M) n

/-- The original scalar first-cohomology genus is invariant under a scheme isomorphism over k. -/
theorem genus_eq_of_schemeIso (e : C ≅ D)
    (f : C ⟶ Spec (CommRingCat.of k)) (g : D ⟶ Spec (CommRingCat.of k))
    (he : e.hom ≫ g = f) : genus f = genus g := by
  unfold genus
  rw [cohomologyDimension_eq_pullback_inv e f g he]
  exact cohomologyDimension_eq_of_iso g (schemeModulePullbackUnitIso e.inv) 1

/-- An original curve isomorphic over k to the projective line has genus zero. -/
theorem genus_eq_zero_of_projectiveLineIso
    (f : C ⟶ Spec (CommRingCat.of k)) (e : C ≅ projectiveSpace k 1)
    (he : e.hom ≫ projectiveSpaceToSpec k 1 = f) : genus f = 0 :=
  (genus_eq_of_schemeIso e f (projectiveSpaceToSpec k 1) he).trans
    (AffineCohomologyPort.genus_projectiveLine_eq_zero k)

/-- The actual rational curve satisfies the canonical degree formula with its original genus. -/
theorem canonicalDegreeFormula_of_projectiveLineIso
    (f : C ⟶ Spec (CommRingCat.of k)) (e : C ≅ projectiveSpace k 1)
    (he : e.hom ≫ projectiveSpaceToSpec k 1 = f) : CanonicalDegreeFormula f := by
  rw [canonicalDegreeFormula_iff, canonicalDegree_eq_neg_two_of_projectiveLineIso f e he,
    genus_eq_zero_of_projectiveLineIso f e he]
  norm_num

end KltDP.Geometry.CurveCanonical

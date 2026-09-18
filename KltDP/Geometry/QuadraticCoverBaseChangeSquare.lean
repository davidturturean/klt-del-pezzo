import KltDP.Geometry.QuadraticCoverRestriction

/-!
# The original quadratic coefficient square is a pullback

This adapter exposes the universal property already proved by the actual
quadratic tensor-product isomorphism. Both projections are the original
coefficient quotient map and the original quadratic structural morphism.
Reuse: `QuadraticCover.baseChangeSpecIso` and its two projection identities;
pinned Mathlib `IsPullback.of_iso_pullback`. No new foundation or source port.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.QuadraticCover

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Changing the actual branch coefficient gives the actual affine pullback square. -/
theorem baseChangeIsPullback (s : R) :
    IsPullback (baseChangeProjection (S := S) s)
      (toBase (algebraMap R S s)) (toBase s)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  IsPullback.of_iso_pullback ⟨baseChangeProjection_toBase s⟩
    (baseChangeSpecIso S s).symm
    (baseChangeSpecIso_inv_fst s) (baseChangeSpecIso_inv_snd S s)

#print axioms baseChangeIsPullback

end KltDP.Geometry.QuadraticCover

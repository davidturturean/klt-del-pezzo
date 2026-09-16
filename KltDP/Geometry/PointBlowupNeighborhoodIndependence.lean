import KltDP.Geometry.AffineCommonPrincipalNeighborhood
import KltDP.Geometry.PointBlowupCoordinateComparison

/-!
# Actual independence of the affine neighborhood in point blowup gluing

Two arbitrary affine open neighborhoods of the same closed point yield
isomorphic actual glued point blowups. A common principal neighborhood is
obtained from the pinned affine communication theorem. The two principal
presentations have an actual coordinate isomorphism identifying the actual
points; the previous Rees and gluing comparisons transport that isomorphism.
The resulting global isomorphism lies over the original scheme and is the
unique morphism over it. No common refinement or blowup comparison is an
input assumption.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.PointBlowupGluing

variable {R S : Type u} [CommRing R] [CommRing S] {X : Scheme.{u}}
    (jR : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion jR]
    (jS : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion jS]
    (qR : PrimeSpectrum R) [qR.asIdeal.IsMaximal]
    (qS : PrimeSpectrum S) [qS.asIdeal.IsMaximal]
    (hR : IsClosed ({jR.base qR} : Set X)) (hS : IsClosed ({jS.base qS} : Set X))
    (hpoint : jR.base qR = jS.base qS)

include hpoint in
/-- The actual glued point blowups from two arbitrary affine neighborhoods
of the same point are isomorphic over the original scheme. -/
theorem exists_neighborhoodIso :
    ∃ e : scheme jR qR hR ≅ scheme jS qS hS,
      e.hom ≫ projection jS qS hS = projection jR qR hR := by
  obtain ⟨r, s, hr, hs, hcommon⟩ :=
    exists_common_principalNeighborhood jR jS qR qS hpoint
  let e := commonPrincipalIso jR jS r s hcommon
  have he : e.hom ≫ principalNeighborhood jS s = principalNeighborhood jR r :=
    commonPrincipalIso_hom_over_base jR jS r s hcommon
  have hp : e.hom.base (principalPoint qR r hr) = principalPoint qS s hs :=
    commonPrincipalIso_point jR jS qR qS hpoint r s hcommon hr hs
  let a := principalNeighborhoodIso jR qR hR r hr
  let b := coordinateComparisonIso (principalNeighborhood jS s) (principalNeighborhood jR r)
    (principalPoint qS s hs) (principalPoint qR r hr)
    (principalPoint_image_closed jS qS hS s hs) (principalPoint_image_closed jR qR hR r hr)
    e he hp
  let c := principalNeighborhoodIso jS qS hS s hs
  refine ⟨a.symm ≪≫ b ≪≫ c, ?_⟩
  change (a.inv ≫ b.hom ≫ c.hom) ≫ projection jS qS hS = projection jR qR hR
  rw [Category.assoc, Category.assoc,
    principalNeighborhoodIso_over_base jS qS hS s hs]
  rw [coordinateComparisonIso_over_base (principalNeighborhood jS s) (principalNeighborhood jR r)
      (principalPoint qS s hs) (principalPoint qR r hr)
      (principalPoint_image_closed jS qS hS s hs) (principalPoint_image_closed jR qR hR r hr)
      e he hp]
  exact principalNeighborhoodIso_inv_over_base jR qR hR r hr

/-- The actual comparison, chosen from the proved existence theorem. -/
def neighborhoodIso : scheme jR qR hR ≅ scheme jS qS hS :=
  (exists_neighborhoodIso jR jS qR qS hR hS hpoint).choose

@[simp] theorem neighborhoodIso_over_base :
    (neighborhoodIso jR jS qR qS hR hS hpoint).hom ≫ projection jS qS hS =
      projection jR qR hR :=
  (exists_neighborhoodIso jR jS qR qS hR hS hpoint).choose_spec

theorem neighborhoodIso_inv_over_base :
    (neighborhoodIso jR jS qR qS hR hS hpoint).inv ≫ projection jR qR hR =
      projection jS qS hS := by
  apply (cancel_epi (neighborhoodIso jR jS qR qS hR hS hpoint).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, neighborhoodIso_over_base]

/-- No other morphism over the original scheme gives a different comparison. -/
theorem neighborhoodIso_unique (f : scheme jR qR hR ⟶ scheme jS qS hS)
    (hf : f ≫ projection jS qS hS = projection jR qR hR) :
    f = (neighborhoodIso jR jS qR qS hR hS hpoint).hom := by
  have h := endomorphism_eq_id jR qR hR
    (f ≫ (neighborhoodIso jR jS qR qS hR hS hpoint).inv) (by
      rw [Category.assoc, neighborhoodIso_inv_over_base, hf])
  apply (cancel_mono (neighborhoodIso jR jS qR qS hR hS hpoint).inv).mp
  rw [h, Iso.hom_inv_id]

end KltDP.Geometry.PointBlowupGluing

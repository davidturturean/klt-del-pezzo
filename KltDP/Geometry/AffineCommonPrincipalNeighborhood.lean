import KltDP.Geometry.PointBlowupPrincipalComparison

/-!
# Actual common principal neighborhoods of two affine charts

The pinned affine communication theorem already produces a simultaneous
principal open in two affine open subsets of a scheme. This file translates
its sections into elements of the two original affine coordinate rings,
using the actual restriction maps and `ΓSpecIso`. It derives nonvanishing
at the specified points and equal ranges of the actual localization maps.
Their equal-range open-immersion isomorphism commutes with the maps to the
original scheme and identifies the actual localized points.

No common refinement, coordinate isomorphism, or point identification is
assumed in the existence theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.PointBlowupGluing

section OneChart

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]

private theorem top_le_preimage_opensRange :
    (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ j ⁻¹ᵁ j.opensRange := by
  intro p _
  exact ⟨p, rfl⟩

/-- The element of the original coordinate ring represented by an actual
section over this affine open immersion's range. -/
def affineSectionCoordinate (s : Γ(X, j.opensRange)) : R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom
    (j.appLE j.opensRange ⊤ (top_le_preimage_opensRange j) s)

theorem basicOpen_affineSectionCoordinate (s : Γ(X, j.opensRange)) :
    PrimeSpectrum.basicOpen (affineSectionCoordinate j s) = j ⁻¹ᵁ X.basicOpen s := by
  rw [affineSectionCoordinate, ← basicOpen_eq_of_affine', Scheme.basicOpen_appLE, top_inf_eq]

/-- The actual principal localization maps onto the principal open of the
original section, with no change of coordinate-ring convention. -/
theorem principalNeighborhood_opensRange_of_section (s : Γ(X, j.opensRange)) :
    (principalNeighborhood j (affineSectionCoordinate j s)).opensRange = X.basicOpen s := by
  let r := affineSectionCoordinate j s
  letI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) :=
    IsOpenImmersion.of_isLocalization r
  have hrange :
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))).opensRange =
        PrimeSpectrum.basicOpen r :=
    Opens.ext (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r)
  change (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫
    j).opensRange = X.basicOpen s
  rw [Scheme.Hom.opensRange_comp, hrange]
  change j ''ᵁ PrimeSpectrum.basicOpen (affineSectionCoordinate j s) = X.basicOpen s
  rw [basicOpen_affineSectionCoordinate, Scheme.Hom.image_preimage_eq_opensRange_inter,
    inf_eq_right.mpr (X.basicOpen_le s)]

theorem affineSectionCoordinate_not_mem
    (s : Γ(X, j.opensRange)) (q : PrimeSpectrum R) (hq : j.base q ∈ X.basicOpen s) :
    affineSectionCoordinate j s ∉ q.asIdeal := by
  change q ∈ PrimeSpectrum.basicOpen (affineSectionCoordinate j s)
  rw [basicOpen_affineSectionCoordinate]
  exact hq

end OneChart

section TwoCharts

variable {R S : Type u} [CommRing R] [CommRing S] {X : Scheme.{u}}
    (jR : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion jR]
    (jS : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion jS]
    (qR : PrimeSpectrum R) (qS : PrimeSpectrum S)
    (hpoint : jR.base qR = jS.base qS)

include hpoint in
/-- Two actual affine neighborhoods of the same point have a common
principal neighborhood in their original affine coordinate rings. -/
theorem exists_common_principalNeighborhood :
    ∃ (r : R) (s : S), r ∉ qR.asIdeal ∧ s ∉ qS.asIdeal ∧
      (principalNeighborhood jR r).opensRange = (principalNeighborhood jS s).opensRange := by
  have hx : jR.base qR ∈ jR.opensRange ⊓ jS.opensRange :=
    ⟨⟨qR, rfl⟩, ⟨qS, hpoint.symm⟩⟩
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter
    (isAffineOpen_opensRange jR) (isAffineOpen_opensRange jS) (jR.base qR) hx
  refine ⟨affineSectionCoordinate jR f, affineSectionCoordinate jS g,
    affineSectionCoordinate_not_mem jR f qR hxf, ?_, ?_⟩
  · apply affineSectionCoordinate_not_mem jS g qS
    rw [← hpoint, ← hfg]
    exact hxf
  · rw [principalNeighborhood_opensRange_of_section,
      principalNeighborhood_opensRange_of_section, hfg]

variable (r : R) (s : S)
    (hcommon : (principalNeighborhood jR r).opensRange =
      (principalNeighborhood jS s).opensRange)

/-- The actual coordinate schemes of a common principal neighborhood are
isomorphic by the proved universal property of open immersions. -/
def commonPrincipalIso :
    Spec (CommRingCat.of (Localization.Away r)) ≅
      Spec (CommRingCat.of (Localization.Away s)) :=
  IsOpenImmersion.isoOfRangeEq (principalNeighborhood jR r) (principalNeighborhood jS s)
    (congrArg (fun U : X.Opens => (U : Set X)) hcommon)

@[simp] theorem commonPrincipalIso_hom_over_base :
    (commonPrincipalIso jR jS r s hcommon).hom ≫ principalNeighborhood jS s =
      principalNeighborhood jR r :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[simp] theorem commonPrincipalIso_inv_over_base :
    (commonPrincipalIso jR jS r s hcommon).inv ≫ principalNeighborhood jR r =
      principalNeighborhood jS s :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

variable [qR.asIdeal.IsMaximal] [qS.asIdeal.IsMaximal]
    (hr : r ∉ qR.asIdeal) (hs : s ∉ qS.asIdeal)

include hpoint in
/-- This coordinate isomorphism identifies the two actual localized
points, because both open immersions are injective and lie over `X`. -/
theorem commonPrincipalIso_point :
    (commonPrincipalIso jR jS r s hcommon).hom.base (principalPoint qR r hr) =
      principalPoint qS s hs := by
  apply (principalNeighborhood jS s).isOpenEmbedding.injective
  change ((commonPrincipalIso jR jS r s hcommon).hom ≫
    principalNeighborhood jS s).base (principalPoint qR r hr) =
      (principalNeighborhood jS s).base (principalPoint qS s hs)
  rw [commonPrincipalIso_hom_over_base, principalNeighborhood_point,
    principalNeighborhood_point, hpoint]

end TwoCharts

end KltDP.Geometry.PointBlowupGluing

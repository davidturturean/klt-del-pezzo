import KltDP.Geometry.AffinePlaneEtaleBlowupSmooth
import KltDP.Geometry.PointBlowupGluingSmooth
import KltDP.Geometry.SmoothSurfacePointFlatPlaneCoordinates

/-!
The original smooth surface internally supplies centered flat étale plane
coordinates. On the derived principal neighborhood the extended plane
origin is exactly the original point ideal. Its actual blowup is smooth,
as is the unchanged complement. The established neighborhood isomorphism
transfers this to the original glued point blowup over the original surface.
No coordinate presentation or source smoothness is supplied as a premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open PointBlowupGluing
open KltDP.Examples.FrobeniusBlowupContact KltDP.Examples.FrobeniusBlowupSmooth

variable {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))

/-- The original glued blowup of a closed point on the original smooth
surface is smooth over the same field, for its actual structure morphism. -/
theorem pointBlowup_isSmooth :
    IsSmooth (projection j q hclosed ≫ X.structureMorphism) := by
  obtain ⟨U, hU, hx, φ, hbase, hstandard, hflat, hetale, r, hr, hcenter, hmax⟩ :=
    X.exists_centered_flat_etale_plane_coordinates (j.base q) hclosed
  let qU : PrimeSpectrum Γ(X.toScheme, U) := hU.primeIdealOf ⟨j.base q, hx⟩
  letI : qU.asIdeal.IsMaximal :=
    isMaximal_primeIdealOf_of_isClosed X.toScheme hU ⟨j.base q, hx⟩ hclosed
  have hUclosed : IsClosed ({hU.fromSpec.base qU} : Set X.toScheme) := by
    rw [show hU.fromSpec.base qU = j.base q from hU.fromSpec_primeIdealOf ⟨j.base q, hx⟩]
    exact hclosed
  let jV := principalNeighborhood hU.fromSpec r
  let qV := principalPoint qU r hr
  letI : IsOpenImmersion jV := principalNeighborhood_isOpenImmersion hU.fromSpec r
  letI : qV.asIdeal.IsMaximal := principalPoint_isMaximal qU r hr
  have hVclosed : IsClosed ({jV.base qV} : Set X.toScheme) :=
    principalPoint_image_closed hU.fromSpec qU hUclosed r hr
  let ψ : planeRing k →+* Localization.Away r :=
    (algebraMap Γ(X.toScheme, U) (Localization.Away r)).comp φ
  letI : Flat (Spec.map (CommRingCat.ofHom φ)) := hflat
  letI : IsEtale (Spec.map (CommRingCat.ofHom φ)) := hetale
  letI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X.toScheme, U) (Localization.Away r)))) :=
    IsOpenImmersion.of_isLocalization r
  letI : Flat (Spec.map (CommRingCat.ofHom ψ)) := by
    dsimp only [ψ]
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    infer_instance
  letI : IsEtale (Spec.map (CommRingCat.ofHom ψ)) := by
    dsimp only [ψ]
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    infer_instance
  have hφstructure :
      Spec.map (CommRingCat.ofHom φ) ≫ planeStructure = hU.fromSpec ≫ X.structureMorphism := by
    rw [planeStructure, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hbase]
    exact Spec_map_baseToAffineSectionsMap X.structureMorphism hU
  have hψstructure :
      Spec.map (CommRingCat.ofHom ψ) ≫ planeStructure = jV ≫ X.structureMorphism := by
    simp only [ψ, CommRingCat.ofHom_comp, Spec.map_comp, jV,
      principalNeighborhood, Category.assoc, hφstructure]
  have hcenter' : Ideal.map ψ (centerIdeal (k := k)) = qV.asIdeal := by
    change Ideal.map ((algebraMap Γ(X.toScheme, U) (Localization.Away r)).comp φ)
        (centerIdeal (k := k)) =
      Ideal.map (algebraMap Γ(X.toScheme, U) (Localization.Away r)) qU.asIdeal
    rw [← Ideal.map_map]
    exact hcenter
  have hA : IsSmooth (AffineBlowup.toSpec qV.asIdeal ≫ jV ≫ X.structureMorphism) := by
    have h := AffinePlaneEtaleBlowupSmooth.isSmoothOfRelativeDimension_two ψ
    rw [hcenter', hψstructure] at h
    letI := h
    exact IsSmoothOfRelativeDimension.isSmooth 2 _
  letI : IsSmooth (projection jV qV hVclosed ≫ X.structureMorphism) :=
    isSmooth_projection_comp_of_affine jV qV hVclosed X.structureMorphism hA
  have hpoint : j.base q = jV.base qV := by
    change j.base q =
      (principalNeighborhood hU.fromSpec r).base (principalPoint qU r hr)
    rw [principalNeighborhood_point]
    exact (hU.fromSpec_primeIdealOf ⟨j.base q, hx⟩).symm
  let e := neighborhoodIso j jV q qV hclosed hVclosed hpoint
  have he : e.hom ≫ projection jV qV hVclosed = projection j q hclosed :=
    neighborhoodIso_over_base j jV q qV hclosed hVclosed hpoint
  rw [← he, Category.assoc]
  infer_instance

end KltDP.Geometry.NormalProjectiveSurface

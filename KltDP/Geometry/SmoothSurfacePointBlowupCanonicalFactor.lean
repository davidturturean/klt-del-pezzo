import KltDP.Geometry.PointBlowupCenteredCanonicalFactor
import KltDP.Geometry.PointBlowupNeighborhoodDifferentialFactor
import KltDP.Geometry.SmoothSurfacePointFlatPlaneCoordinates
import KltDP.Geometry.SmoothSurfaceRelativeDimension

/-!
# The original whole canonical factor for a smooth surface point blowup

The original smooth surface supplies centered standard-smooth plane
coordinates. After the internally obtained principal shrinking, its plane
origin is exactly the selected reduced point. The proved whole centered
factor is returned to the original affine neighborhood by the actual
neighborhood and center-fiber isomorphisms. The final endpoints have no
coordinate, basis, factorization or differential-compatibility premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open PointBlowupGluing PointBlowupTopDifferential
open KltDP.Examples.FrobeniusBlowupContact KltDP.Examples.FrobeniusBlowupSmooth

variable {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))

/-- The actual blowup of an original smooth surface point has the normalized
whole intrinsic top-differential factor through its actual exceptional kernel. -/
theorem pointBlowup_exists_canonicalFactorIso :
    ∃ e : (schemeModulePullback (projection j q hclosed)).obj
          (sourceSheaf X.structureMorphism 2) ≅
        exceptionalTensor X.structureMorphism j q hclosed 2,
      e.hom ≫ exceptionalInclusion X.structureMorphism j q hclosed 2 =
        blowdownMap X.structureMorphism j q hclosed 2 := by
  letI := X.isSmoothOfRelativeDimension_two
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
  letI := affineSectionsAlgebra X.structureMorphism hU
  let φA : planeRing k →ₐ[k] Γ(X.toScheme, U) :=
    { __ := φ
      commutes' := fun t =>
        congrArg (fun ρ : k →+* Γ(X.toScheme, U) => ρ t) hbase }
  let ψA : planeRing k →ₐ[k] Localization.Away r :=
    (IsScalarTower.toAlgHom k Γ(X.toScheme, U) (Localization.Away r)).comp φA
  have hψring : ψA.toRingHom =
      (algebraMap Γ(X.toScheme, U) (Localization.Away r)).comp φ := rfl
  have hlocal : (algebraMap Γ(X.toScheme, U) (Localization.Away r)).IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway r
  have hψ : ψA.toRingHom.IsStandardSmoothOfRelativeDimension 0 := by
    rw [hψring]
    exact hlocal.comp hstandard
  have hφstructure :
      Spec.map (CommRingCat.ofHom φ) ≫ planeStructure = hU.fromSpec ≫ X.structureMorphism := by
    rw [planeStructure, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hbase]
    exact Spec_map_baseToAffineSectionsMap X.structureMorphism hU
  have hψbase :
      Spec.map (CommRingCat.ofHom ψA.toRingHom) ≫ planeStructure = jV ≫ X.structureMorphism := by
    rw [hψring]
    simp only [CommRingCat.ofHom_comp, Spec.map_comp, jV,
      principalNeighborhood, Category.assoc, hφstructure]
  have hψstructure : jV ≫ X.structureMorphism =
      Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r))) :=
    hψbase.symm.trans (AffineNativeTopDifferential.spec_comp k ψA)
  have hcenter' : SmoothPointBlowupAffineCanonicalFactor.extendedCenter k ψA = qV.asIdeal := by
    change Ideal.map ψA.toRingHom (centerIdeal (k := k)) =
      Ideal.map (algebraMap Γ(X.toScheme, U) (Localization.Away r)) qU.asIdeal
    rw [hψring, ← Ideal.map_map]
    exact hcenter
  have hpoint : j.base q = jV.base qV := by
    change j.base q =
      (principalNeighborhood hU.fromSpec r).base (principalPoint qU r hr)
    rw [principalNeighborhood_point]
    exact (hU.fromSpec_primeIdealOf ⟨j.base q, hx⟩).symm
  let eS := centeredCanonicalFactorIso X.structureMorphism jV qV hVclosed
    hψstructure ψA hψ hcenter'
  have heS : eS.hom ≫ exceptionalInclusion X.structureMorphism jV qV hVclosed 2 =
      blowdownMap X.structureMorphism jV qV hVclosed 2 :=
    centeredCanonicalFactorIso_comp X.structureMorphism jV qV hVclosed
      hψstructure ψA hψ hcenter'
  refine ⟨neighborhoodFactorIso X.structureMorphism j jV q qV hclosed hVclosed hpoint 2 eS, ?_⟩
  exact neighborhoodFactorIso_comp X.structureMorphism j jV q qV hclosed hVclosed hpoint 2 eS heS

/-- An actual normalized canonical factor on the original whole point blowup. -/
def pointBlowupCanonicalFactorIso :
    (schemeModulePullback (projection j q hclosed)).obj (sourceSheaf X.structureMorphism 2) ≅
      exceptionalTensor X.structureMorphism j q hclosed 2 :=
  Classical.choose (X.pointBlowup_exists_canonicalFactorIso j q hclosed)

/-- Its forward map factors exactly the original global intrinsic exterior differential. -/
theorem pointBlowupCanonicalFactorIso_comp :
    (X.pointBlowupCanonicalFactorIso j q hclosed).hom ≫
        exceptionalInclusion X.structureMorphism j q hclosed 2 =
      blowdownMap X.structureMorphism j q hclosed 2 :=
  Classical.choose_spec (X.pointBlowup_exists_canonicalFactorIso j q hclosed)

end KltDP.Geometry.NormalProjectiveSurface

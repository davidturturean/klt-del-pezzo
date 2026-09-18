import KltDP.Geometry.SmoothSurfacePointCoordinates
import KltDP.Geometry.SmoothSurfaceRegularity
import KltDP.Geometry.StandardSmoothSpecFlat
import KltDP.Geometry.PlaneCoordinateOrigin

/-!
# Actual centered flat étale plane coordinates at a smooth surface point

The original smooth structure morphism and chosen closed point supply the
coordinate presentation. Its stronger standard-smooth condition is retained,
so flatness is proved for the original map. The original ordered plane
equivalence identifies its center with the original reduced point ideal on
the constructed principal neighborhood. No coordinate or basis is an input.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

namespace KltDP.Geometry.NormalProjectiveSurface

open KltDP.Examples.FrobeniusBlowupContact KltDP.Examples.FrobeniusBlowupSmooth
open PlaneBlowupNativeDifferentialBasis

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

/-- The original smooth surface supplies a flat étale map from the actual
polynomial plane, with the actual reduced point as its centered fiber after
an internally constructed principal shrinking. -/
theorem exists_centered_flat_etale_plane_coordinates
    [IsSmooth X.structureMorphism] (x : X.toScheme)
    (hclosed : IsClosed ({x} : Set X.toScheme)) :
    ∃ (U : X.toScheme.Opens) (hU : IsAffineOpen U) (hx : x ∈ U),
      ∃ φ : planeRing k →+* Γ(X.toScheme, U),
        φ.comp planeConstants = (baseToAffineSectionsMap X.structureMorphism hU).hom ∧
        φ.IsStandardSmoothOfRelativeDimension 0 ∧
        Flat (Spec.map (CommRingCat.ofHom φ)) ∧
        IsEtale (Spec.map (CommRingCat.ofHom φ)) ∧
        ∃ r : Γ(X.toScheme, U), r ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ∧
          (Ideal.map φ (centerIdeal (k := k))).map
              (algebraMap Γ(X.toScheme, U) (Localization.Away r)) =
            (hU.primeIdealOf ⟨x, hx⟩).asIdeal.map
              (algebraMap Γ(X.toScheme, U) (Localization.Away r)) ∧
          ((Ideal.map φ (centerIdeal (k := k))).map
            (algebraMap Γ(X.toScheme, U) (Localization.Away r))).IsMaximal := by
  obtain ⟨U, hU, hx, hsmooth⟩ := X.exists_affine_standardSmooth_two x hclosed
    (X.regularPoints_of_isSmooth x)
  letI := affineSectionsAlgebra X.structureMorphism hU
  letI : Algebra.FiniteType k Γ(X.toScheme, U) :=
    affineSectionsAlgebra_finiteType X.structureMorphism hU
  letI : IsNoetherianRing Γ(X.toScheme, U) :=
    Algebra.FiniteType.isNoetherianRing k Γ(X.toScheme, U)
  letI : Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X.toScheme, U) := hsmooth
  let q : Ideal Γ(X.toScheme, U) := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  letI : q.IsMaximal := isMaximal_primeIdealOf_of_isClosed X.toScheme hU ⟨x, hx⟩ hclosed
  let χ := KltDP.Compatibility.closedPointCharacter k q
  obtain ⟨g₀, hg₀⟩ :=
    KltDP.StandardSmoothCoordinates.exists_standardSmoothZero_mvPolynomial
      2 k Γ(X.toScheme, U)
  let g := EtaleCoordinates.centeredCoordinateMap g₀ χ
  have hg : g.toRingHom.IsStandardSmoothOfRelativeDimension 0 :=
    EtaleCoordinates.centeredCoordinateMap_standardSmoothZero g₀ χ hg₀
  let φ := g.comp (planeEquiv k).symm.toAlgHom
  have hφ : φ.toRingHom.IsStandardSmoothOfRelativeDimension 0 :=
    hg.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (planeEquiv k).symm.toRingEquiv)
  have hbase : φ.toRingHom.comp planeConstants =
      (baseToAffineSectionsMap X.structureMorphism hU).hom := φ.comp_algebraMap
  have hcenter : Ideal.map φ.toRingHom (centerIdeal (k := k)) =
      Ideal.map g.toRingHom
        (RingHom.ker (MvPolynomial.aeval (R := k) (fun _ : Fin 2 => (0 : k))).toRingHom) := by
    change Ideal.map (g.toRingHom.comp (planeEquiv k).symm.toRingHom) _ = _
    rw [← Ideal.map_map, planeEquiv_symm_map_centerIdeal k]
  obtain ⟨r, hr, heq, hmax⟩ :=
    EtaleCoordinates.exists_away_centered_coordinate_fiber g₀ χ hg₀
  refine ⟨U, hU, hx, φ.toRingHom, hbase, hφ,
    flat_spec_map_of_standardSmooth φ.toRingHom hφ.isStandardSmooth,
    isEtale_spec_map_of_standardSmoothZero φ.toRingHom hφ, r, ?_, ?_, ?_⟩
  · intro hrq
    exact hr ((KltDP.Compatibility.closedPointCharacter_eq_zero_iff k q r).mpr hrq)
  · rw [hcenter]
    simpa only [χ, KltDP.Compatibility.closedPointCharacter_ker] using heq
  · rw [hcenter]
    exact hmax

end KltDP.Geometry.NormalProjectiveSurface

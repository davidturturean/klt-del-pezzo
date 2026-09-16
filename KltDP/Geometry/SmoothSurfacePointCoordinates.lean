import KltDP.Geometry.StandardSmoothSurfaceDimension
import KltDP.Geometry.UnramifiedPointFiber

/-!
# Actual centered étale coordinates at a regular smooth surface point

The affine chart, its two polynomial coordinates, and its principal
shrinking are constructed from the actual structure morphism and point.
The inverse-image origin ideal equals the original point's extended
maximal ideal on that shrinking, so the fiber is the reduced chosen point.
Regularity remains an explicit assertion about the original surface stalk.
No isomorphism with an affine-plane open or center-comparison hypothesis
is supplied as input.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

/-- A closed regular point of a smooth surface admits actual two-dimensional
étale coordinates over the original field. On a constructed principal
neighborhood, the inverse-image origin has exactly the chosen point's
maximal ideal, including the reduced scheme structure. -/
theorem exists_centered_etale_coordinates_reduced_fiber
    [IsSmooth X.structureMorphism] (x : X.toScheme)
    (hclosed : IsClosed ({x} : Set X.toScheme))
    (hregular : RegularPoint X.toScheme x) :
    ∃ (U : X.toScheme.Opens) (hU : IsAffineOpen U) (hx : x ∈ U),
      ∃ g : MvPolynomial (Fin 2) k →+* Γ(X.toScheme, U),
        g.comp MvPolynomial.C = (baseToAffineSectionsMap X.structureMorphism hU).hom ∧
        IsEtale (Spec.map (CommRingCat.ofHom g)) ∧
        ∃ r : Γ(X.toScheme, U), r ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ∧
          ((RingHom.ker (MvPolynomial.aeval (fun _ : Fin 2 ↦ (0 : k))).toRingHom).map g).map
              (algebraMap Γ(X.toScheme, U) (Localization.Away r)) =
            (hU.primeIdealOf ⟨x, hx⟩).asIdeal.map
              (algebraMap Γ(X.toScheme, U) (Localization.Away r)) ∧
          (((RingHom.ker (MvPolynomial.aeval (fun _ : Fin 2 ↦ (0 : k))).toRingHom).map g).map
            (algebraMap Γ(X.toScheme, U) (Localization.Away r))).IsMaximal := by
  obtain ⟨U, hU, hx, hsmooth⟩ := X.exists_affine_standardSmooth_two x hclosed hregular
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
  obtain ⟨r, hr, heq, hmax⟩ :=
    EtaleCoordinates.exists_away_centered_coordinate_fiber g₀ χ hg₀
  refine ⟨U, hU, hx, g.toRingHom, g.comp_algebraMap,
    isEtale_spec_map_of_standardSmoothZero g.toRingHom hg, r, ?_, ?_, hmax⟩
  · intro hrq
    exact hr ((KltDP.Compatibility.closedPointCharacter_eq_zero_iff k q r).mpr hrq)
  · simpa only [χ, KltDP.Compatibility.closedPointCharacter_ker] using heq

end KltDP.Geometry.NormalProjectiveSurface

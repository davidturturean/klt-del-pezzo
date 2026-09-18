import KltDP.Geometry.SingularClosed
import KltDP.Topology.DimensionOpenCover

/-! A common bound on the actual stalk dimensions bounds the scheme's
dimension. This is the pinned prime-height formula and actual affine cover. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.SchemeDimensionFromStalks

theorem affine_bound (X : Scheme.{u}) (d : WithBot ℕ∞)
    (h : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ d)
    {U : X.Opens} (hU : IsAffineOpen U) : ringKrullDim Γ(X, U) ≤ d := by
  rw [ringKrullDim, Order.krullDim_eq_iSup_height]
  refine iSup_le fun p => ?_
  obtain ⟨x, hx⟩ := hU.isoSpec.hom.homeomorph.surjective p
  let xu : U := x
  have hp : hU.primeIdealOf xu = p := hx
  letI : Algebra Γ(X, U) (X.presheaf.stalk (xu : X)) :=
    X.presheaf.algebra_section_stalk xu
  letI := hU.isLocalization_stalk xu
  have hb := h (xu : X)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf xu).asIdeal,
    Ideal.height_eq_primeHeight] at hb
  change (Order.height (hU.primeIdealOf xu) : WithBot ℕ∞) ≤ d at hb
  rwa [hp] at hb

theorem bound (X : Scheme.{u}) (d : WithBot ℕ∞)
    (h : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ d) :
    topologicalKrullDim X ≤ d := by
  apply KltDP.Topology.topologicalKrullDim_le_of_open_cover
    (fun x : X => (X.affineCover.map x).opensRange)
    (fun x => ⟨x, X.affineCover.covers x⟩)
  intro x
  let U : X.Opens := (X.affineCover.map x).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.map x)
  have htop : topologicalKrullDim U = ringKrullDim Γ(X, U) :=
    (_root_.IsHomeomorph.topologicalKrullDim_eq hU.isoSpec.hom.homeomorph
      hU.isoSpec.hom.homeomorph.isHomeomorph).trans
        (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U))
  exact htop.le.trans (affine_bound X d h hU)

#print axioms bound

end KltDP.Geometry.SchemeDimensionFromStalks

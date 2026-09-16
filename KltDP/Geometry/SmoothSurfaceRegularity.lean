import KltDP.Compatibility.StandardSmoothClosedHeight
import KltDP.Geometry.SmoothFieldCharts
import KltDP.Geometry.ClosedPointDimension
import KltDP.Geometry.SurfaceRegularCharts
import KltDP.Geometry.RegularStalkUFD

/-!
# Regularity of the original stalks of a smooth normal projective surface

At an actual closed point, smoothness of the original structure morphism
provides a standard-smooth affine neighborhood over the original field.
The proved closed-point cotangent lower bound and the existing local-domain
dimension-at-most-two upper bound give equality on the actual affine
localization. Its canonical stalk equivalence proves regularity of the
original structure-sheaf stalk.

The existing normal-surface codimension argument then gives regularity
at every point. No regular-stalk, UFD-stalk, or smooth-implies-regular
literature hypothesis is introduced by this adapter.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

/-- An actual closed point of the original smooth normal projective
surface has a regular structure-sheaf stalk. -/
theorem regularPoint_of_isSmooth_of_isClosed [IsSmooth X.structureMorphism]
    (x : X.Point) (hclosed : IsClosed ({x} : Set X.Point)) :
    RegularPoint X.toScheme x := by
  obtain ⟨U, hU, hx, hsmooth⟩ :=
    isSmooth_field_exists_affine_standardSmooth X.structureMorphism x
  letI := affineSectionsAlgebra X.structureMorphism hU
  obtain ⟨⟨P⟩⟩ := hsmooth
  letI : Algebra.IsStandardSmoothOfRelativeDimension P.dimension k Γ(X.toScheme, U) :=
    ⟨P, rfl⟩
  let xu : U := ⟨x, hx⟩
  let q : Ideal Γ(X.toScheme, U) := (hU.primeIdealOf xu).asIdeal
  letI : q.IsMaximal :=
    isMaximal_primeIdealOf_of_isClosed X.toScheme hU xu hclosed
  letI : IsDomain (Localization.AtPrime q) :=
    X.affineLocalization_isDomain hU.fromSpec (hU.primeIdealOf xu)
  letI : IsNoetherianRing (Localization.AtPrime q) :=
    X.affineLocalization_isNoetherianRing hU.fromSpec (hU.primeIdealOf xu)
  have hdim : ringKrullDim (Localization.AtPrime q) ≤ 2 :=
    X.affineLocalization_ringKrullDim_le_two hU.fromSpec (hU.primeIdealOf xu)
  have hreg : RegularLocal (Localization.AtPrime q) :=
    ⟨inferInstance, le_antisymm
      (ringKrullDim_le_finrank_cotangentSpace_of_le_two (Localization.AtPrime q) hdim)
      (KltDP.Compatibility.standardSmooth_closed_cotangent_finrank_le_ringKrullDim
        k Γ(X.toScheme, U) P.dimension q)⟩
  exact (regularPoint_iff_regularLocal_affineLocalization hU xu).mpr hreg

/-- Smoothness of the original structure morphism proves regularity of
every original stalk, including the nonclosed points of the surface. -/
theorem regularPoints_of_isSmooth [IsSmooth X.structureMorphism] :
    ∀ x : X.Point, RegularPoint X.toScheme x :=
  X.regularPoints_of_closedPoints_regular
    (fun x hx => X.regularPoint_of_isSmooth_of_isClosed x hx)

end KltDP.Geometry.NormalProjectiveSurface

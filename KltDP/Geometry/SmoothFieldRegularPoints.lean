import KltDP.Compatibility.StandardSmoothClosedHeight
import KltDP.Geometry.SmoothFieldCharts
import KltDP.Geometry.ClosedPointDimension
import KltDP.Geometry.SurfaceRegularCharts
import KltDP.Geometry.RegularLocalDimensionTwo
import KltDP.Geometry.AffineRegularLocus
import KltDP.Geometry.SingularClosed
import KltDP.Geometry.DivisorOrder

/-!
# Smooth over a field implies regular, for integral schemes of dimension at most two (BRIEF20, item 1)

The accepted `NormalProjectiveSurface.regularPoint_of_isSmooth_of_isClosed` and
`NormalProjectiveSurface.regularPoints_of_isSmooth` made scheme-generic: no projectivity and no
`NormalProjectiveSurface` packaging, only an integral scheme `Y` with a smooth morphism
`f : Y ⟶ Spec k`, Noetherian stalks and `topologicalKrullDim Y ≤ 2`. `k` is algebraically closed and
`Y` integral because the two accepted ingredients require exactly that: the closed-point maximality
`isMaximal_primeIdealOf_of_isClosed` is stated for an integral scheme, and the cotangent bound
`standardSmooth_closed_cotangent_finrank_le_ringKrullDim` for an algebraically closed base field.

* `regularPoint_of_isSmooth_of_isClosed'`: every closed point is regular. On a standard-smooth affine
  chart (`isSmooth_field_exists_affine_standardSmooth`) the localization at the maximal ideal of the
  point has cotangent dimension at most its Krull dimension
  (`standardSmooth_closed_cotangent_finrank_le_ringKrullDim`). Conversely, a Noetherian local domain of
  dimension at most two has Krull dimension at most its cotangent dimension
  (`ringKrullDim_le_finrank_cotangentSpace_of_le_two`); the stalks are domains because `Y` is integral
  (`integralSchemeStalk_isDomain`). The local dimension is bounded by `topologicalKrullDim Y`
  (`ringKrullDim_stalk_le_topologicalKrullDim`), and regularity transfers from the affine localization
  to the stalk (`regularPoint_iff_regularLocal_affineLocalization`).
* `regularPoint_of_isSmooth_of_isNormalScheme`: if `Y` is moreover normal, every point is regular,
  generic points included. A non-closed point has stalk dimension at most one
  (`ringKrullDim_stalk_le_one_of_not_isClosed_singleton`), and a Noetherian normal local ring of
  dimension at most one is regular (`regularPoint_of_normal_of_ringKrullDim_le_one`).

Nothing here is assumed; both statements are proved from the accepted adapters.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace KltDP.Geometry.SmoothFieldRegularPoints

open KltDP.Geometry

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} [IsIntegral Y]

/-- **A closed point of an integral scheme smooth over an algebraically closed field is regular**,
when the stalks are Noetherian and the scheme has dimension at most two. -/
theorem regularPoint_of_isSmooth_of_isClosed' (f : Y ⟶ Spec (CommRingCat.of k)) [IsSmooth f]
    (hnoeth : ∀ y : Y, IsNoetherianRing (Y.presheaf.stalk y))
    (hdim : topologicalKrullDim Y ≤ 2) (x : Y) (hclosed : IsClosed ({x} : Set Y)) :
    RegularPoint Y x := by
  obtain ⟨U, hU, hx, hsmooth⟩ := isSmooth_field_exists_affine_standardSmooth f x
  letI := affineSectionsAlgebra f hU
  obtain ⟨⟨P⟩⟩ := hsmooth
  letI : Algebra.IsStandardSmoothOfRelativeDimension P.dimension k Γ(Y, U) := ⟨P, rfl⟩
  let xu : U := ⟨x, hx⟩
  let q : Ideal Γ(Y, U) := (hU.primeIdealOf xu).asIdeal
  letI : q.IsMaximal := isMaximal_primeIdealOf_of_isClosed Y hU xu hclosed
  letI : IsDomain (Y.presheaf.stalk (hU.fromSpec.base (hU.primeIdealOf xu))) :=
    integralSchemeStalk_isDomain Y _
  letI : IsNoetherianRing (Y.presheaf.stalk (hU.fromSpec.base (hU.primeIdealOf xu))) := hnoeth _
  letI : IsDomain (Localization.AtPrime q) :=
    MulEquiv.isDomain (Y.presheaf.stalk (hU.fromSpec.base (hU.primeIdealOf xu)))
      (openImmersionStalkLocalizationEquiv hU.fromSpec (hU.primeIdealOf xu)).symm.toMulEquiv
  letI : IsNoetherianRing (Localization.AtPrime q) :=
    isNoetherianRing_of_ringEquiv (Y.presheaf.stalk (hU.fromSpec.base (hU.primeIdealOf xu)))
      (openImmersionStalkLocalizationEquiv hU.fromSpec (hU.primeIdealOf xu))
  have hdimq : ringKrullDim (Localization.AtPrime q) ≤ 2 :=
    calc ringKrullDim (Localization.AtPrime q)
        = ringKrullDim (Y.presheaf.stalk (hU.fromSpec.base (hU.primeIdealOf xu))) :=
          (ringKrullDim_eq_of_ringEquiv
            (openImmersionStalkLocalizationEquiv hU.fromSpec (hU.primeIdealOf xu))).symm
      _ ≤ 2 := (ringKrullDim_stalk_le_topologicalKrullDim Y _).trans hdim
  have hreg : RegularLocal (Localization.AtPrime q) :=
    ⟨inferInstance, le_antisymm
      (ringKrullDim_le_finrank_cotangentSpace_of_le_two (Localization.AtPrime q) hdimq)
      (KltDP.Compatibility.standardSmooth_closed_cotangent_finrank_le_ringKrullDim
        k Γ(Y, U) P.dimension q)⟩
  exact (regularPoint_iff_regularLocal_affineLocalization hU xu).mpr hreg

/-- **Every point of a normal integral scheme smooth over an algebraically closed field is regular**
(generic points included), when the stalks are Noetherian and the scheme has dimension at most two. -/
theorem regularPoint_of_isSmooth_of_isNormalScheme (f : Y ⟶ Spec (CommRingCat.of k)) [IsSmooth f]
    (hnormal : IsNormalScheme Y) (hnoeth : ∀ y : Y, IsNoetherianRing (Y.presheaf.stalk y))
    (hdim : topologicalKrullDim Y ≤ 2) (x : Y) : RegularPoint Y x := by
  by_cases hclosed : IsClosed ({x} : Set Y)
  · exact regularPoint_of_isSmooth_of_isClosed' f hnoeth hdim x hclosed
  · letI := hnoeth x
    exact regularPoint_of_normal_of_ringKrullDim_le_one Y hnormal x
      (ringKrullDim_stalk_le_one_of_not_isClosed_singleton Y hdim x hclosed)

end KltDP.Geometry.SmoothFieldRegularPoints

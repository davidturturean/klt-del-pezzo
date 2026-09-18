import KltDP.Geometry.BirationalCartierPullbackAddPushforward
import KltDP.Geometry.CartierPullbackExceptionalModule
import KltDP.Geometry.BirationalCanonicalRepresentativeUnique

/-!
# The unique normalized canonical Cartier representative from the actual factor

The literal pullback plus exceptional Cartier divisor represents the original
exterior square by the actual sheaf factor. Its Weil pushforward is proved
to be the original base representative. Existing principal rigidity gives
uniqueness among all actual exterior-square representatives with that exact
pushforward. No canonical divisor formula or pushforward conclusion is input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace

universe u

namespace KltDP.Geometry.BirationalCanonicalRepresentative

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- The original differential factor and actual exceptional fibre construct
a unique source canonical Cartier representative with fixed original Weil
pushforward. The existence witness is the literal signed pullback plus E. -/
theorem existsUnique_of_exceptional_factor
    {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
    (K : CartierDivisor X.toScheme)
    (eK : cartierDivisorModule X.toScheme K ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior X.structureMorphism 2)
    (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    {Z : Scheme.{u}} (i : Z ⟶ S.toScheme) [IsClosedImmersion i]
    (hI : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE = i.ker)
    (x : X.toScheme) (hx : IsClosed ({x} : Set X.toScheme))
    (hi : ∀ z : Z, π.base (i.base z) = x)
    (eFactor : (schemeModulePullback π).obj
        (SmoothCanonicalExteriorComparison.relativeDifferentialExterior X.structureMorphism 2) ≅
      schemeKernelIdeal i ⊗
        SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2) :
    ∃! D : CartierDivisor S.toScheme,
      Nonempty (cartierDivisorModule S.toScheme D ≅
        SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2) ∧
      BirationalWeilPushforward.pushforward π hbir (S.cartierToWeilHom D) =
        X.cartierToWeilHom K := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  let D : CartierDivisor S.toScheme := DominantCartierPullback.pullbackHom π K + E
  let eD : cartierDivisorModule S.toScheme D ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2 :=
    CartierPullbackExceptionalModule.ofFactorIso π K
      (SmoothCanonicalExteriorComparison.relativeDifferentialExterior X.structureMorphism 2)
      (SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2)
      eK E hE i hI eFactor
  have hpush : BirationalWeilPushforward.pushforward π hbir (S.cartierToWeilHom D) =
      X.cartierToWeilHom K :=
    BirationalWeilPushforward.pushforward_cartier_pullback_add_of_kernel_maps_to_closed_point
      π hbir K E hE i hI x hx hi
  refine ⟨D, ⟨⟨eD⟩, hpush⟩, ?_⟩
  intro D' hD'
  obtain ⟨eD'⟩ := hD'.1
  exact eq_of_exterior_iso_of_pushforward_eq π hbir D' D eD' eD
    (hD'.2.trans hpush.symm)

end KltDP.Geometry.BirationalCanonicalRepresentative

#check @KltDP.Geometry.BirationalCanonicalRepresentative.existsUnique_of_exceptional_factor
#print axioms KltDP.Geometry.BirationalCanonicalRepresentative.existsUnique_of_exceptional_factor

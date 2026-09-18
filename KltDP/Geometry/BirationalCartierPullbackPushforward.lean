import KltDP.Geometry.DominantCartierPullbackEquations
import KltDP.Geometry.BirationalDivisorOrder
import KltDP.Geometry.BirationalWeilPushforward
import KltDP.Geometry.CartierWeilMap

/-!
# The original Cartier pullback and birational Weil pushforward

Each target prime has its proved unique original source prime. An actual
target equation pulls back to the inverse-image open, and the original
stalk-map isomorphism preserves its order. Thus the original integral
Weil pushforward recovers the actual target Cartier divisor's Weil image.
No regularity or common isomorphism-open hypothesis is needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.BirationalWeilPushforward

open BirationalPrimeCorrespondence

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)

/-- The actual pulled Cartier divisor has the original coefficient at
the unique original prime above each target prime. -/
theorem cartier_pullback_coefficient (D : CartierDivisor X.toScheme) (C : X.PrimeCurve) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    S.cartierToWeilHom (DominantCartierPullback.pullbackHom π D)
        (abovePrimeCurve π hbir C) = X.cartierToWeilHom D C := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  obtain ⟨f, U, hC, hf⟩ := exists_cartierOrderEquation X.toScheme D C.genericPoint
  letI : Nonempty U := ⟨⟨C.genericPoint, hC⟩⟩
  have hB : (abovePrimeCurve π hbir C).genericPoint ∈ π ⁻¹ᵁ U := by
    change π.base (abovePrimeCurve π hbir C).genericPoint ∈ U
    rw [abovePrimeCurve_map_genericPoint π hbir C]
    exact hC
  letI : Nonempty (π ⁻¹ᵁ U) := ⟨⟨(abovePrimeCurve π hbir C).genericPoint, hB⟩⟩
  calc
    S.cartierToWeilHom (DominantCartierPullback.pullbackHom π D)
        (abovePrimeCurve π hbir C) =
      (abovePrimeCurve π hbir C).order
        (Units.map (functionFieldMap π).hom.toMonoidHom f) :=
      S.cartierToWeilHom_apply_of_equation (DominantCartierPullback.pullbackHom π D)
        (abovePrimeCurve π hbir C) (π ⁻¹ᵁ U) hB
        (Units.map (functionFieldMap π).hom.toMonoidHom f)
        (DominantCartierPullback.pullbackHom_globalEquation_preimage π D U f hf)
    _ = C.order f := BirationalDivisorOrder.abovePrimeCurve_order π hbir C f
    _ = X.cartierToWeilHom D C :=
      (X.cartierToWeilHom_apply_of_equation D C U hC f hf).symm

/-- Original Weil pushforward is a left inverse to the original signed
Cartier pullback after the actual Cartier-to-Weil maps. -/
theorem pushforward_cartier_pullback (D : CartierDivisor X.toScheme) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    pushforward π hbir (S.cartierToWeilHom (DominantCartierPullback.pullbackHom π D)) =
      X.cartierToWeilHom D := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  apply Finsupp.ext
  intro C
  exact cartier_pullback_coefficient π hbir D C

end KltDP.Geometry.BirationalWeilPushforward

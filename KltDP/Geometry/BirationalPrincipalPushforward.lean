import KltDP.Geometry.BirationalDivisorOrder
import KltDP.Geometry.BirationalWeilPushforward
import KltDP.Geometry.PrincipalDivisor

/-!
# Pushforward of the original principal Weil divisor

The coefficient identity uses the existing finite-sum pushforward and the
proved equality of original orders at the unique corresponding prime.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.BirationalWeilPushforward

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)

/-- Pulling back a nonzero rational function by the original field map
and pushing forward its actual principal divisor recovers the original
target principal divisor. -/
theorem pushforward_principalDivisor (f : X.toScheme.functionFieldˣ) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    pushforward π hbir
        (S.principalDivisor (Units.map (functionFieldMap π).hom.toMonoidHom f)) =
      X.principalDivisor f := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  apply Finsupp.ext
  intro C
  exact BirationalDivisorOrder.abovePrimeCurve_order π hbir C f

end KltDP.Geometry.BirationalWeilPushforward

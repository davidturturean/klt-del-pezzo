import KltDP.Geometry.BirationalPrincipalPushforward
import KltDP.Geometry.BirationalFunctionField

/-!
# Principal pushforward for every original source rational function

The target function is transported by the inverse of the original
function-field map. Its invertibility follows from original birationality.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.BirationalWeilPushforward

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)

/-- The actual principal divisor of every source function pushes to the
principal divisor of its image under the inverse original field map. -/
theorem pushforward_principalDivisor_source (f : S.toScheme.functionFieldˣ) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    letI : IsIso (functionFieldMap π) :=
      (BirationalFunctionField.isBirationalScheme_iff_functionFieldMap_isIso π).mp hbir
    pushforward π hbir (S.principalDivisor f) =
      X.principalDivisor
        (Units.map (asIso (functionFieldMap π)).inv.hom.toMonoidHom f) := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  letI : IsIso (functionFieldMap π) :=
    (BirationalFunctionField.isBirationalScheme_iff_functionFieldMap_isIso π).mp hbir
  let g := Units.map (asIso (functionFieldMap π)).inv.hom.toMonoidHom f
  have hunit : Units.map (functionFieldMap π).hom.toMonoidHom g = f := by
    apply Units.ext
    exact Iso.inv_hom_id_apply (asIso (functionFieldMap π)) (f : S.toScheme.functionField)
  have h := pushforward_principalDivisor π hbir g
  rw [hunit] at h
  exact h

/-- In particular, the original pushforward preserves the actual
principal subgroup of the original Weil-divisor group. -/
theorem pushforward_principalDivisor_exists (f : S.toScheme.functionFieldˣ) :
    ∃ g : X.toScheme.functionFieldˣ,
      pushforward π hbir (S.principalDivisor f) = X.principalDivisor g := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  letI : IsIso (functionFieldMap π) :=
    (BirationalFunctionField.isBirationalScheme_iff_functionFieldMap_isIso π).mp hbir
  exact ⟨Units.map (asIso (functionFieldMap π)).inv.hom.toMonoidHom f,
    pushforward_principalDivisor_source π hbir f⟩

end KltDP.Geometry.BirationalWeilPushforward

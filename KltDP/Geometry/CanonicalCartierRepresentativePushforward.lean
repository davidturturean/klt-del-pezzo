import KltDP.Geometry.BirationalCartierRepresentative
import KltDP.Geometry.CanonicalWeilBirational

/-!
An actual source canonical Cartier representative can be chosen to push
forward to the independently constructed target canonical Weil divisor.
The original source exterior-square module is preserved by an actual
isomorphism, while the pushforward is an equality of divisors.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CanonicalWeilBirational

variable {k : Type u} [Field k] (S Y : NormalProjectiveSurface k)
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    (π : S.toScheme ⟶ Y.toScheme)
    (hπ : π ≫ Y.structureMorphism = S.structureMorphism)
    (U : Y.toScheme.Opens) [Nonempty U.toScheme] [IsIso (π ∣_ U)]
    [IsSmoothOfRelativeDimension 2 (U.ι ≫ Y.structureMorphism)]

include hπ in
/-- A source canonical Cartier divisor with the original exterior-square
module and exact pushforward equal to the chosen target canonical divisor. -/
theorem exists_compatible_canonical_cartier [IsProper π]
    (hbir : IsBirationalScheme π)
    (hU : ∀ C : Y.PrimeCurve, C.genericPoint ∈ U) :
    ∃ D : CartierDivisor S.toScheme,
      Nonempty (cartierDivisorModule S.toScheme D ≅
        SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2) ∧
      BirationalWeilPushforward.pushforward π hbir (S.cartierToWeilHom D) =
        SmoothOpenCanonicalWeil.weilRepresentative Y U := by
  have hclass := pushforward_canonical_weilClass S Y π hπ U hbir hU
  rw [BirationalWeilClassPushforward.pushforward_weilClassMap] at hclass
  have hclass' : Y.weilClassMap (BirationalWeilPushforward.pushforward π hbir
      (S.cartierToWeilHom
        (SmoothCanonicalCartierRepresentative.cartierRepresentative S.structureMorphism))) =
      Y.weilClassMap (SmoothOpenCanonicalWeil.weilRepresentative Y U) := hclass
  obtain ⟨D, hpush, ⟨e⟩⟩ :=
    BirationalWeilPushforward.exists_cartier_representative_with_pushforward π hbir
      (SmoothCanonicalCartierRepresentative.cartierRepresentative S.structureMorphism)
      (SmoothOpenCanonicalWeil.weilRepresentative Y U) hclass'
  exact ⟨D, ⟨e ≪≫
    SmoothCanonicalCartierExterior.representativeIsoExterior S.structureMorphism⟩, hpush⟩

end KltDP.Geometry.CanonicalWeilBirational

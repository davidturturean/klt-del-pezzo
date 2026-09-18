import KltDP.Geometry.BirationalWeilDegreeProjection
import KltDP.Geometry.BirationalCartierPullbackPushforward
import KltDP.Geometry.DominantCartierPullbackModule
import KltDP.Geometry.IntersectionPairingSymmetry

/-!
# The original Cartier intersection pairing under birational pullback

The actual signed Cartier pullback has the actual pulled line module and
its Weil image pushes forward to the original Cartier Weil image. The
proved finite-Weil projection formula therefore preserves the original
intersection pairing. No strict-transform curve isomorphism, numerical
isometry, or intersection equality is an input.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped BigOperators
universe u

namespace KltDP.Geometry.BirationalCartierIntersectionPullback

open BirationalWeilPushforward

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The existing mixed intersection formula is the actual finite
restriction-degree functional of the second Cartier module. -/
theorem intersectionPairing_eq_cartierWeilRestrictionDegree
    (Y : NormalProjectiveSurface k)
    (hY : ∀ x : Y.Point, RegularPoint Y.toScheme x)
    (D E : CartierDivisor Y.toScheme) :
    Y.intersectionPairing hY D E =
      Y.cartierWeilRestrictionDegree E (Y.cartierToWeilHom D) := by
  rw [Y.intersectionPairing_eq_weil_sum_right hY,
    NormalProjectiveSurface.cartierWeilRestrictionDegree,
    Y.picardWeilRestrictionDegree_apply]
  apply Finset.sum_congr rfl
  intro C hC
  dsimp only
  rw [C.intersectionNumber_eq_picardRestrictionDegree]

variable {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π]
  (hπ : π ≫ X.structureMorphism = S.structureMorphism)
  (hbir : IsBirationalScheme π)

include hπ hbir

/-- The actual signed Cartier module obeys the finite-Weil degree
projection formula, through its proved original pullback isomorphism. -/
theorem cartierWeilRestrictionDegree_pullback
    (D : CartierDivisor X.toScheme) (Z : S.WeilDivisor) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    S.cartierWeilRestrictionDegree (DominantCartierPullback.pullbackHom π D) Z =
      X.cartierWeilRestrictionDegree D (pushforward π hbir Z) := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  change S.picardWeilRestrictionDegree
      (cartierDivisorInvertibleSheaf S.toScheme
        (DominantCartierPullback.pullbackHom π D)).toPic Z =
    X.picardWeilRestrictionDegree (cartierDivisorInvertibleSheaf X.toScheme D).toPic
      (pushforward π hbir Z)
  calc
    _ = S.picardWeilRestrictionDegree
        (pullbackInvertibleSheaf π (cartierDivisorInvertibleSheaf X.toScheme D)).toPic Z :=
      congrArg (fun f : S.WeilDivisor →ₗ[ℤ] ℤ => f Z)
        (S.picardWeilRestrictionDegree_eq_of_iso
          (L := pullbackInvertibleSheaf π (cartierDivisorInvertibleSheaf X.toScheme D))
          (M := cartierDivisorInvertibleSheaf S.toScheme
            (DominantCartierPullback.pullbackHom π D))
          (DominantCartierPullback.modulePullbackIso π D)).symm
    _ = _ := by
      rw [← schemePicardPullbackHom_toPic]
      exact BirationalWeilDegreeProjection.picardWeilRestrictionDegree_pushforward
        π hπ hbir (cartierDivisorInvertibleSheaf X.toScheme D).toPic Z

/-- Proper birational pullback preserves the intersection of the two
original signed Cartier divisors on the original regular surfaces. -/
theorem intersectionPairing_pullback
    (hS : ∀ x : S.Point, RegularPoint S.toScheme x)
    (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
    (D E : CartierDivisor X.toScheme) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    S.intersectionPairing hS (DominantCartierPullback.pullbackHom π D)
        (DominantCartierPullback.pullbackHom π E) =
      X.intersectionPairing hX D E := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  rw [intersectionPairing_eq_cartierWeilRestrictionDegree S hS,
    cartierWeilRestrictionDegree_pullback π hπ hbir,
    pushforward_cartier_pullback π hbir D,
    ← intersectionPairing_eq_cartierWeilRestrictionDegree X hX]

end KltDP.Geometry.BirationalCartierIntersectionPullback

#check @KltDP.Geometry.BirationalCartierIntersectionPullback.intersectionPairing_pullback
#print axioms KltDP.Geometry.BirationalCartierIntersectionPullback.intersectionPairing_pullback

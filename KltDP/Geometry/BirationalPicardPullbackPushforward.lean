import KltDP.Geometry.BirationalGlobalCartierPullback
import KltDP.Geometry.PicardWeilClassHom
import KltDP.Geometry.SchemeInvertibleSheafPullback

/-!
# Original Picard pullback followed by Weil-class pushforward

The integral Cartier representative theorem applies to the original
target line and its actual pulled-back line. The global Cartier
comparison then proves the identity on the original Picard class.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.BirationalPicardPullbackPushforward

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
    (U : X.toScheme.Opens) [Nonempty U.toScheme] [IsIso (π ∣_ U)]

/-- Actual Picard pullback followed by the original Weil-class
pushforward recovers the original target Picard-to-Weil class. -/
theorem pushforward_picard_pullback
    (hU : ∀ C : X.PrimeCurve, C.genericPoint ∈ U) (L : X.toScheme.Pic) :
    BirationalWeilClassPushforward.pushforward π hbir
        (S.picardToWeilClassHom (Additive.ofMul (schemePicardPullbackHom π L))) =
      X.picardToWeilClassHom (Additive.ofMul L) := by
  obtain ⟨A, rfl⟩ := cartierPicardClass_surjective X.toScheme L
  let M := pullbackInvertibleSheaf π (cartierDivisorInvertibleSheaf X.toScheme A)
  obtain ⟨D, ⟨eD⟩⟩ := exists_cartierDivisor_module_iso S.toScheme M.obj
  have hM : schemePicardPullbackHom π (cartierPicardClass X.toScheme A) = M.toPic :=
    schemePicardPullbackHom_toPic π (cartierDivisorInvertibleSheaf X.toScheme A)
  have hsource :
      S.picardToWeilClassHom
          (Additive.ofMul (schemePicardPullbackHom π (cartierPicardClass X.toScheme A))) =
        S.weilClassMap (S.cartierToWeilHom D) :=
    (congrArg (fun p : S.toScheme.Pic => S.picardToWeilClassHom (Additive.ofMul p)) hM).trans
      (S.picardToWeilClassHom_of_module_iso M D eD)
  exact (congrArg (BirationalWeilClassPushforward.pushforward π hbir) hsource).trans
    ((pushforward_cartierWeilClass_of_module_iso π hbir U hU D A eD.symm).trans
      (X.picardToWeilClassHom_cartierPicardHom A).symm)

/-- The identity retains the original additive homomorphisms on the
original Picard and Weil class groups. -/
theorem pushforward_picard_pullback_hom
    (hU : ∀ C : X.PrimeCurve, C.genericPoint ∈ U) :
    (BirationalWeilClassPushforward.pushforward π hbir).comp
        (S.picardToWeilClassHom.comp (schemePicardPullbackHom π).toAdditive) =
      X.picardToWeilClassHom := by
  apply AddMonoidHom.ext
  intro L
  exact pushforward_picard_pullback π hbir U hU L.toMul

/-- The same identity for the literal pullback of an original invertible
sheaf, using its proved equality with original Picard pullback. -/
theorem pushforward_pullbackInvertibleSheaf
    (hU : ∀ C : X.PrimeCurve, C.genericPoint ∈ U) (L : InvertibleSheaf X.toScheme) :
    BirationalWeilClassPushforward.pushforward π hbir
        (S.picardToWeilClassHom (Additive.ofMul (pullbackInvertibleSheaf π L).toPic)) =
      X.picardToWeilClassHom (Additive.ofMul L.toPic) := by
  have h := pushforward_picard_pullback π hbir U hU L.toPic
  rw [schemePicardPullbackHom_toPic] at h
  exact h

end KltDP.Geometry.BirationalPicardPullbackPushforward

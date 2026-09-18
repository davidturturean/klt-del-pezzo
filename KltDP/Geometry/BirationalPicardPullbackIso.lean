import KltDP.Geometry.BirationalPicardPullbackPushforward

/-!
# An original pullback-line isomorphism computes the pushed class

This applies the proved Picard identity directly to an actual sheaf
isomorphism, for example the original ample-line pullback comparison.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.BirationalPicardPullbackPushforward

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
    (U : X.toScheme.Opens) [Nonempty U.toScheme] [IsIso (π ∣_ U)]

/-- The class of an actual source line is sent to the target line's
class whenever the given original module isomorphism identifies it with
that target line's actual pullback. -/
theorem pushforward_of_pullback_iso
    (hU : ∀ C : X.PrimeCurve, C.genericPoint ∈ U)
    (L : InvertibleSheaf X.toScheme) (M : InvertibleSheaf S.toScheme)
    (e : (schemeModulePullback π).obj L.obj ≅ M.obj) :
    BirationalWeilClassPushforward.pushforward π hbir
        (S.picardToWeilClassHom (Additive.ofMul M.toPic)) =
      X.picardToWeilClassHom (Additive.ofMul L.toPic) := by
  have hclass : (pullbackInvertibleSheaf π L).toPic = M.toPic := by
    letI := Scheme.Modules.monoidalCategory S.toScheme
    apply Units.ext
    change ((pullbackInvertibleSheaf π L).toPic : Skeleton S.toScheme.Modules) =
      (M.toPic : Skeleton S.toScheme.Modules)
    rw [InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val]
    exact Quotient.sound ⟨e⟩
  exact (congrArg (fun p : S.toScheme.Pic =>
    BirationalWeilClassPushforward.pushforward π hbir
      (S.picardToWeilClassHom (Additive.ofMul p))) hclass.symm).trans
    (pushforward_pullbackInvertibleSheaf π hbir U hU L)

end KltDP.Geometry.BirationalPicardPullbackPushforward

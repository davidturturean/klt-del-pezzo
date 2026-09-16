import KltDP.Compatibility.SchemeTwoOpenCoverIso
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed immersions from chart squares

A morphism `f : X ⟶ Y` is a closed immersion as soon as, for every member `V_i ⟶ Y` of an open
cover of the target, there is an open piece `u_i : U_i ⟶ X` with `u_i ≫ f = c_i ≫ V_i` for a closed
immersion `c_i : U_i ⟶ V_i` and `range u_i = f⁻¹(range V_i)`. The square is then a pullback
(accepted `isPullback_of_range`), so the base change of `f` to `V_i` is `c_i` up to isomorphism,
and closed immersions are local on the target (pinned `IsClosedImmersion.isLocalAtTarget`).

This is the criterion under which a chart-by-chart closed immersion (for instance the Segre map
`P¹ ×_k P¹ ⟶ P³` on the four product charts) is a closed immersion globally; no gluing of the
morphism itself is performed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism which restricts, over each member of an open cover of the target, to a closed
immersion of the corresponding open piece of the source is a closed immersion. -/
theorem isClosedImmersion_of_chartSquares (𝒱 : Y.OpenCover) (U : 𝒱.J → Scheme.{u})
    (u : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (u i)] (c : ∀ i, U i ⟶ 𝒱.obj i)
    [∀ i, IsClosedImmersion (c i)] (hcomm : ∀ i, u i ≫ f = c i ≫ 𝒱.map i)
    (hrange : ∀ i, Set.range (u i).base = f.base ⁻¹' Set.range (𝒱.map i).base) :
    IsClosedImmersion f := by
  refine (IsLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) 𝒱).mpr fun i => ?_
  have h : IsPullback (u i) (c i) f (𝒱.map i) :=
    KltDP.SchemeTwoOpenGluing.isPullback_of_range (u i) (c i) f (𝒱.map i) (hcomm i) (hrange i)
  change IsClosedImmersion (pullback.snd f (𝒱.map i))
  rw [← h.isoPullback_inv_snd]
  infer_instance

end KltDP.Geometry

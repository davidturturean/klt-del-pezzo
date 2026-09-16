import KltDP.Geometry.ExteriorPowerFrameComparisonUnit

/-!
# The original exterior sheafification unit on a frame open

The accepted frame comparison factors through the original sheafification
unit. Its proved bijectivity on each frame subopen, together with the proved
sheaf comparison isomorphism, therefore proves bijectivity of the original
unit on that subopen. The map is unchanged.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.ExteriorPowerFrameComparison

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} (M : X.Modules) {ι : Type u}
  (U : ι → X.Opens) {n : ℕ}
  (frame : ∀ (i : ι) (W : X.Opens), W ≤ U i →
    Basis (Fin n) Γ(X, W) (moduleSections M W))
  (hframe : ∀ (i : ι) {V W : X.Opens} (hVW : V ≤ W) (hW : W ≤ U i) (t : Fin n),
    moduleRestr M hVW (frame i W hW t) = frame i V (hVW.trans hW) t)
  (hU : (⨆ i, U i) = ⊤)

include frame hframe hU in
/-- The actual exterior unit is bijective on every original frame subopen. -/
theorem toSheaf_bijective (j : ι) {W : X.Opens} (hW : W ≤ U j) :
    Function.Bijective ((SchemeExteriorPower.toSheaf M n).app (op W)) := by
  let e := ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op W)).mapIso
    (sheafIso M U frame hframe hU)).toLinearEquiv
  have he (q : (SchemeExteriorPower.presheaf M n).obj (op W)) :
      e ((SchemeExteriorPower.toSheaf M n).app (op W) q) =
        (toFramePresheaf M U frame hframe).app (op W) q :=
    sheafIso_hom_toSheaf M U frame hframe hU W q
  have hb := toFramePresheaf_bijective M U frame hframe j hW
  constructor
  · intro q r hqr
    apply hb.1
    exact (he q).symm.trans ((congrArg e hqr).trans (he r))
  · intro s
    obtain ⟨q, hq⟩ := hb.2 (e s)
    refine ⟨q, e.injective ?_⟩
    exact (he q).trans hq

include frame hframe hU in
/-- The same original unit component is an isomorphism of the actual
section modules; no substitute comparison map is chosen. -/
theorem toSheaf_isIso (j : ι) {W : X.Opens} (hW : W ≤ U j) :
    IsIso ((SchemeExteriorPower.toSheaf M n).app (op W)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (toSheaf_bijective M U frame hframe hU j hW)

end KltDP.Geometry.ExteriorPowerFrameComparison

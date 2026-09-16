import KltDP.Geometry.ExteriorPowerFrameComparison

/-!
# Wedge normalization of the original exterior/frame comparison

The existing exterior-sheaf isomorphism is the adjoint of the actual
determinant-coordinate presheaf map. Thus it preserves the original wedges
of local sections, including their determinant coordinates in every frame.
No compatibility of a new comparison is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.AffineTopDifferentialFrame
open KltDP.Geometry.ChartFrameAtlasSheaf
open KltDP.Geometry.TransitionUnitGluing

universe u

namespace KltDP.Geometry.ExteriorPowerFrameComparison

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem sheafification_map_counit_homEquiv {X : Scheme.{u}}
    (P : X.PresheafOfModules) (N : X.Modules) (g : P ⟶ N.val) :
    (_root_.PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.val)).homEquiv P N
        ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map g ≫
          (_root_.PresheafOfModules.sheafificationForgetIso X.ringCatSheaf N).hom) = g :=
  ((_root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.val)).homEquiv P N).apply_symm_apply g

variable {X : Scheme.{u}} (M : X.Modules) {ι : Type u}
  (U : ι → X.Opens) {n : ℕ}
  (frame : ∀ (i : ι) (W : X.Opens), W ≤ U i →
    Basis (Fin n) Γ(X, W) (moduleSections M W))
  (hframe : ∀ (i : ι) {V W : X.Opens} (hVW : V ≤ W) (hW : W ≤ U i) (t : Fin n),
    moduleRestr M hVW (frame i W hW t) = frame i V (hVW.trans hW) t)
  (hU : (⨆ i, U i) = ⊤)

private theorem sheafIso_hom_eq :
    (sheafIso M U frame hframe hU).hom =
      (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map
          (toFramePresheaf M U frame hframe) ≫
        (_root_.PresheafOfModules.sheafificationForgetIso X.ringCatSheaf
          (moduleSheaf X U (transitionUnit U (moduleSections M) frame))).hom := rfl

/-- The actual exterior/frame isomorphism is adjoint to the original
determinant-coordinate presheaf map. -/
theorem sheafIso_homEquiv :
    SchemeExteriorPower.homEquiv M n
        (sheafOfFrames U (moduleSections M) (moduleRestr M) frame hframe hU).obj
        (sheafIso M U frame hframe hU).hom =
      toFramePresheaf M U frame hframe := by
  rw [sheafIso_hom_eq]
  exact sheafification_map_counit_homEquiv _ _ (toFramePresheaf M U frame hframe)

/-- The existing comparison sends the original sheafification unit to the
original determinant-coordinate map, as an equality of presheaf morphisms. -/
theorem toSheaf_sheafIso_hom :
    SchemeExteriorPower.toSheaf M n ≫ (sheafIso M U frame hframe hU).hom.val =
      toFramePresheaf M U frame hframe :=
  sheafIso_homEquiv M U frame hframe hU

/-- Sectionwise normalization on every original exterior-presheaf section. -/
theorem sheafIso_hom_toSheaf (W : X.Opens)
    (q : (SchemeExteriorPower.presheaf M n).obj (op W)) :
    (sheafIso M U frame hframe hU).hom.val.app (op W)
        ((SchemeExteriorPower.toSheaf M n).app (op W) q) =
      (toFramePresheaf M U frame hframe).app (op W) q := by
  exact congrArg (fun f : SchemeExteriorPower.presheaf M n ⟶
      (moduleSheaf X U (transitionUnit U (moduleSections M) frame)).val =>
        f.app (op W) q) (toSheaf_sheafIso_hom M U frame hframe hU)

/-- Every wedge in the independent exterior sheaf has its actual determinant
coordinate under the existing frame-line isomorphism and trivialization. -/
theorem trivialization_sheafIso_wedge (j : ι) {W : X.Opens} (hW : W ≤ U j)
    (v : Fin n → moduleSections M W) :
    trivialization X U (transitionUnit U (moduleSections M) frame)
        (transitionUnit_isCocycle (U := U) (L := moduleSections M)
          (restr := moduleRestr M) (frame := frame) (hframe := hframe)) j hW
        ((sheafIso M U frame hframe hU).hom.val.app (op W)
          (SchemeExteriorPower.wedge M n W v)) =
      (frame j W hW).det v := by
  change trivialization X U (transitionUnit U (moduleSections M) frame)
      (transitionUnit_isCocycle (U := U) (L := moduleSections M)
        (restr := moduleRestr M) (frame := frame) (hframe := hframe)) j hW
      ((sheafIso M U frame hframe hU).hom.val.app (op W)
        ((SchemeExteriorPower.toSheaf M n).app (op W)
          (exteriorPower.ιMulti Γ(X, W) n v))) = _
  rw [sheafIso_hom_toSheaf, trivialization_toFrame, determinantEquiv_apply_wedge]

end KltDP.Geometry.ExteriorPowerFrameComparison

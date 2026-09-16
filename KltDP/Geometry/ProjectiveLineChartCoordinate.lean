import KltDP.Geometry.OpenChartAtlasFace
import KltDP.Geometry.ProjectiveLineCanonicalFrame

/-!
# The `P¹` chart data through the coordinate face alone (E15)

Every earlier attempt on this goal — lane D's Tasks 23–28, and my E13/E14 — stated something about the
concrete `P¹` data whose **type embedded the over-site `.val.app` term**, and every such statement
exhausted 4000000 heartbeats. E14 isolated that precisely: wrapped opens, chart isomorphisms, the cover,
both `≤` lemmas and the `rfl` atlas identification all passed cheaply; only the two over-site-typed frame
restatements timed out.

This module never states one. Each concrete fact below is an equation in `Γ(X, W)` about
`openChartCoordinate`, which mentions no over-site object and carries no `LinearEquiv` coercion in its
type. The over-site content stays inside **generic** lemmas — the accepted `openChartCoordinate_app`
(through this lane's `openChartCoordinate_app_preimage`) and the accepted `chartEquiv_ofOpenCharts`,
which proves itself by `congrArg` on the morphism rather than by rewriting the over-site term.

The concrete chart is also supplied **directly** as `chartOpen k 1`, not as `V i` for a lambda `V`, so
matching lane D's compiled frame condition needs no beta-iota through `ULift` inside an over-site-typed
argument — which is what E13's monolithic application demanded.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry KltDP.Geometry.ModuleCohomology KltDP.Geometry.SchemeKaehlerSheaf
open KltDP.Geometry.SchemeKaehlerOpenRestriction KltDP.Geometry.SchemeModuleRestriction
open KltDP.Geometry.ProjectiveLineChartTriviality KltDP.Geometry.ProjectiveLineComparison
open KltDP.Geometry.ProjectiveLineSections KltDP.Geometry.ProjectiveLineSheafExponent
open KltDP.Geometry.ProjectiveLineTransitionExtension KltDP.Geometry.ProjectiveLineTransitionExponent
open KltDP.Geometry.AffineModuleTilde KltDP.Geometry.AffineKaehlerTildeDerivation
open KltDP.Geometry.ProjectiveLineCanonical KltDP.Geometry.ProjectiveLineCanonicalFrame
open KltDP.Geometry.OpenChartAtlasFace KltDP.Geometry.RationalTreePicard
open KltDP.Geometry.TransitionUnitExtraction

universe u

namespace KltDP.Geometry.ProjectiveLineChartCoordinate

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-! ### Step 1 — a generic coordinate frame lemma.  No concrete data, no over-site type. -/

/-- **The chart coordinate of a frame is `1`**, generically: if the chart trivialisation sends the
restricted section to `1`, the `Opens`-site coordinate is `1`. The over-site content is confined to the
accepted `openChartCoordinate_app`; the conclusion is an equation in `Γ(X, W)`. -/
theorem openChartCoordinate_eq_one {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅ (restriction U.ι).obj M)
    {W : X.Opens} (hW : W ≤ U) (s : M.val.obj (op W))
    (h : e.inv.val.app (op (U.ι ⁻¹ᵁ W))
        (M.val.map (homOfLE (x := U.ι ''ᵁ U.ι ⁻¹ᵁ W) (y := W)
          (Set.image_preimage_subset U.ι.base (W : Set X))).op s) =
      (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ W))) :
    openChartCoordinate M U e hW s = (1 : Γ(X, W)) := by
  have h1 : U.ι.app W (openChartCoordinate M U e hW s) = 1 :=
    (openChartCoordinate_app_preimage M U e hW s).trans h
  have h2 := congrArg (openSectionsInv U hW) h1
  rwa [openSectionsInv_app, map_one] at h2

variable (k : Type u) [Field k]

/-! ### Step 2 — the concrete facts, stated only about the coordinate -/

set_option maxHeartbeats 4000000 in
/-- **Chart `1`: the coordinate of `d s` on the overlap is `1`.** An equation in
`Γ(projectiveSpace k 1, overlapOpen k)`; nothing over-site appears in the statement. -/
theorem coord_right :
    openChartCoordinate (cotangent k) (chartOpen k 1) ((chartTriv k 1).symm)
        (overlapOpen_le_right k)
        ((baseRingDerivation (projectiveSpaceToSpec k 1)).d (rightFrame k)) = 1 :=
  openChartCoordinate_eq_one (cotangent k) (chartOpen k 1) ((chartTriv k 1).symm)
    (overlapOpen_le_right k)
    ((baseRingDerivation (projectiveSpaceToSpec k 1)).d (rightFrame k)) (atlasFrame_right k)

set_option maxHeartbeats 4000000 in
/-- **Chart `0`: the coordinate of `d t` on the overlap is `1`.** -/
theorem coord_left :
    openChartCoordinate (cotangent k) (chartOpen k 0) ((chartTriv k 0).symm)
        (overlapOpen_le_left k)
        ((baseRingDerivation (projectiveSpaceToSpec k 1)).d (leftFrame k)) = 1 :=
  openChartCoordinate_eq_one (cotangent k) (chartOpen k 0) ((chartTriv k 0).symm)
    (overlapOpen_le_left k)
    ((baseRingDerivation (projectiveSpaceToSpec k 1)).d (leftFrame k)) (atlasFrame_left k)

/-! ### Step 3 — the goal, through the accepted face -/

set_option maxHeartbeats 4000000 in
/-- **Lane D's `atlasChartEquiv_right`**, closed from the coordinate fact through the accepted
`chartEquiv_ofOpenCharts`. -/
theorem atlasChartEquiv_right_viaCoord :
    chartEquiv (projectiveSpace k 1) (cotangent k) (frameAtlas k) (⟨1⟩ : ULift.{u} (Fin 2))
        (overlapOpen_le_right k)
        ((baseRingDerivation (projectiveSpaceToSpec k 1)).d (rightFrame k)) = 1 :=
  (chartEquiv_ofOpenCharts (cotangent k) (fun i : ULift.{u} (Fin 2) => chartOpen k i.down)
    (chartOpen_cover k) (fun i => (chartTriv k i.down).symm) ⟨1⟩ (overlapOpen_le_right k)
    ((baseRingDerivation (projectiveSpaceToSpec k 1)).d (rightFrame k))).trans (coord_right k)

set_option maxHeartbeats 4000000 in
/-- **Lane D's `atlasChartEquiv_left`**, the same way. -/
theorem atlasChartEquiv_left_viaCoord :
    chartEquiv (projectiveSpace k 1) (cotangent k) (frameAtlas k) (⟨0⟩ : ULift.{u} (Fin 2))
        (overlapOpen_le_left k)
        ((baseRingDerivation (projectiveSpaceToSpec k 1)).d (leftFrame k)) = 1 :=
  (chartEquiv_ofOpenCharts (cotangent k) (fun i : ULift.{u} (Fin 2) => chartOpen k i.down)
    (chartOpen_cover k) (fun i => (chartTriv k i.down).symm) ⟨0⟩ (overlapOpen_le_left k)
    ((baseRingDerivation (projectiveSpaceToSpec k 1)).d (leftFrame k))).trans (coord_left k)

end KltDP.Geometry.ProjectiveLineChartCoordinate

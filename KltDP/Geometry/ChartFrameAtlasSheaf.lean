import KltDP.Geometry.FrameRestrictionDeterminant
import KltDP.Geometry.TransitionUnitLocalTriviality
import KltDP.Geometry.InvertibleSheafPicard

/-!
# The determinant line bundle of an atlas of chart frames

This is the scheme-level assembly of F04 §4.3 route (b).  The algebra is already in place:
`TopDifferentialFrameChange` produces the frame-change unit and its two cocycle identities,
`TopDifferentialFrameBaseChange` and `KaehlerFrameLocalization` make it natural in a scalar change,
and `FrameRestrictionDeterminant` makes it natural in a semilinear restriction.  The gluing is also
already accepted: `TransitionUnitGluing.invertibleSheaf` turns a unit cocycle on a covering into an
actual `InvertibleSheaf X`, through chart isomorphisms rather than the over-site bridge.

What is assembled here is the family in between.  The data is an atlas: a covering family of opens
`U i`, a module `L W` over each section ring `Γ(X, W)` with semilinear restriction maps, and a frame
`frame i W : Basis (Fin n) Γ(X, W) (L W)` on every open of the chart `U i`, whose restrictions are
the frames of the smaller open.  On surfaces `L` is the Kähler module of the section rings, `n = 2`,
and the frames come from submersive presentations of the charts; nothing in this module needs that,
and the transition units are determinants of frame changes for any `n`.

* **`chartUnitOn`, `transitionUnit`**: the determinant of the change from the `i`-frame to the
  `j`-frame, a unit of the section ring of the overlap;
* **`chartUnitOn_restrict`**: those units restrict correctly (`FrameRestrictionDeterminant`);
* **`transitionUnit_isCocycle`**: the two fields of `TransitionUnitGluing.IsCocycle`, from
  `frameChangeUnit_self` and `det_mul_det_cocycle` at the triple overlap;
* **`sheafOfFrames`**: the actual invertible sheaf glued from those units — for a surface atlas of
  Kähler frames this is `ω_X = ∧²Ω_X` — with `sheafOfFrames_obj` identifying its underlying module
  sheaf with the glued `moduleSheaf`, and **`classOfFrames`**, its class `K_X` in the actual Picard
  group `X.Pic`.

The atlas hypotheses are not vacuous: `structureFrame` exhibits them for the structure sheaf itself
on an arbitrary covering, with `structureTransitionUnit` computing the resulting units to be `1`.

Nothing is admitted here.  What is *not* done here: the instantiation of `L` by the Kähler modules of
the section rings of a smooth surface, which needs the chart frames on every open of a chart and hence
the localisation comparison for `Ω`; `ChartFrameAtlasJacobian` records the overlap identification that
this instantiation has to supply.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.TopDifferentialFrameChange
open KltDP.Geometry.FrameRestrictionDeterminant
open KltDP.Geometry.TransitionUnitGluing

universe u v

namespace KltDP.Geometry.ChartFrameAtlasSheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
variable (L : X.Opens → Type v) [∀ W : X.Opens, AddCommGroup (L W)]
  [∀ W : X.Opens, Module Γ(X, W) (L W)]
variable (restr : ∀ {V W : X.Opens} (h : V ≤ W), L W →ₛₗ[res X h] L V)
variable {n : ℕ}
variable (frame : ∀ (i : ι) (W : X.Opens), W ≤ U i → Basis (Fin n) Γ(X, W) (L W))
variable (hframe : ∀ (i : ι) {V W : X.Opens} (hVW : V ≤ W) (hW : W ≤ U i) (t : Fin n),
  restr hVW (frame i W hW t) = frame i V (hVW.trans hW) t)

/-- The transition unit of the two chart frames on a common open subset: the determinant of the
change of frame. -/
def chartUnitOn (i j : ι) {W : X.Opens} (hi : W ≤ U i) (hj : W ≤ U j) : Γ(X, W)ˣ :=
  frameChangeUnit (frame i W hi) (frame j W hj)

@[simp]
theorem chartUnitOn_val (i j : ι) {W : X.Opens} (hi : W ≤ U i) (hj : W ≤ U j) :
    (chartUnitOn U L frame i j hi hj : Γ(X, W)) = (frame i W hi).det (frame j W hj) := rfl

/-- The transition unit family of the atlas, on the overlaps of the covering. -/
def transitionUnit (i j : ι) : Γ(X, U i ⊓ U j)ˣ :=
  chartUnitOn U L frame i j inf_le_left inf_le_right

theorem transitionUnit_eq (i j : ι) :
    transitionUnit U L frame i j =
      chartUnitOn U L frame i j (inf_le_left : U i ⊓ U j ≤ U i)
        (inf_le_right : U i ⊓ U j ≤ U j) := rfl

include restr hframe in
/-- **The chart transition units restrict correctly**: this is the compatibility that the cocycle
law needs at a triple overlap. -/
theorem chartUnitOn_restrict {V W : X.Opens} (hVW : V ≤ W) (i j : ι)
    (hi : W ≤ U i) (hj : W ≤ U j) :
    (chartUnitOn U L frame i j (hVW.trans hi) (hVW.trans hj) : Γ(X, V)) =
      res X hVW (chartUnitOn U L frame i j hi hj : Γ(X, W)) :=
  det_restrict (frame i W hi) (frame j W hj) (frame i V (hVW.trans hi))
    (frame j V (hVW.trans hj)) (restr hVW) (hframe i hVW hi) (hframe j hVW hj)

include restr hframe in
/-- **The transition units of an atlas of chart frames form a cocycle.** -/
theorem transitionUnit_isCocycle : IsCocycle X U (transitionUnit U L frame) where
  unit_self i := by
    exact congrArg Units.val
      (frameChangeUnit_self (frame i (U i ⊓ U i) (inf_le_left : U i ⊓ U i ≤ U i)))
  mul_res i j l := by
    have hij : U i ⊓ U j ⊓ U l ≤ U i ⊓ U j := inf_le_left
    have hjl : U i ⊓ U j ⊓ U l ≤ U j ⊓ U l :=
      le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have hil : U i ⊓ U j ⊓ U l ≤ U i ⊓ U l :=
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have h₁ := chartUnitOn_restrict (U := U) (L := L) (restr := restr) (frame := frame)
      (hframe := hframe) hij i j inf_le_left inf_le_right
    have h₂ := chartUnitOn_restrict (U := U) (L := L) (restr := restr) (frame := frame)
      (hframe := hframe) hjl j l inf_le_left inf_le_right
    have h₃ := chartUnitOn_restrict (U := U) (L := L) (restr := restr) (frame := frame)
      (hframe := hframe) hil i l inf_le_left inf_le_right
    have key :
        res X hij (chartUnitOn U L frame i j inf_le_left inf_le_right : Γ(X, U i ⊓ U j)) *
            res X hjl (chartUnitOn U L frame j l inf_le_left inf_le_right : Γ(X, U j ⊓ U l)) =
          res X hil (chartUnitOn U L frame i l inf_le_left inf_le_right : Γ(X, U i ⊓ U l)) := by
      rw [← h₁, ← h₂, ← h₃]
      simp only [chartUnitOn_val]
      exact det_mul_det_cocycle _ _ _
    exact key

/-- **The actual invertible sheaf glued from an atlas of chart frames.** For a surface atlas of
Kähler frames of relative dimension two this is `ω_X = ∧²Ω_X`. -/
def sheafOfFrames (hU : (⨆ i, U i) = ⊤) : InvertibleSheaf X :=
  invertibleSheaf X U (transitionUnit U L frame)
    (transitionUnit_isCocycle (U := U) (L := L) (restr := restr) (frame := frame)
      (hframe := hframe)) hU

/-- The glued sheaf is the actual module sheaf of matching families of the transition units. -/
theorem sheafOfFrames_obj (hU : (⨆ i, U i) = ⊤) :
    (sheafOfFrames U L restr frame hframe hU).obj =
      moduleSheaf X U (transitionUnit U L frame) := rfl

/-- **The class of the atlas in the actual Picard group**: for a surface atlas of Kähler frames this
is the canonical class `K_X`. -/
def classOfFrames (hU : (⨆ i, U i) = ⊤) : X.Pic :=
  InvertibleSheaf.toPic (sheafOfFrames U L restr frame hframe hU)

section StructureSheafFrames

/-! ### Nonvacuity: the structure sheaf carries chart frames on every covering -/

/-- Restriction of sections, as a semilinear map of the section rings themselves. -/
def structureRestr {V W : X.Opens} (h : V ≤ W) : Γ(X, W) →ₛₗ[res X h] Γ(X, V) where
  toFun := res X h
  map_add' := map_add (res X h)
  map_smul' r x := map_mul (res X h) r x

/-- The structure sheaf has the rank-one frame `1` on every open of every chart. -/
def structureFrame (_i : ι) (W : X.Opens) (_hW : W ≤ U _i) :
    Basis (Fin 1) Γ(X, W) Γ(X, W) :=
  Basis.singleton (Fin 1) Γ(X, W)

/-- Those frames satisfy the restriction hypothesis of the atlas. -/
theorem structureFrame_restrict (i : ι) {V W : X.Opens} (hVW : V ≤ W) (hW : W ≤ U i)
    (t : Fin 1) :
    structureRestr hVW (structureFrame U i W hW t) = structureFrame U i V (hVW.trans hW) t := by
  show res X hVW (Basis.singleton (Fin 1) Γ(X, W) t) = Basis.singleton (Fin 1) Γ(X, V) t
  rw [Basis.singleton_apply, Basis.singleton_apply, map_one]

/-- The atlas of structure-sheaf frames has trivial transition units. -/
theorem structureTransitionUnit (i j : ι) :
    transitionUnit U (fun W => Γ(X, W)) (structureFrame U) i j = 1 :=
  frameChangeUnit_self _

end StructureSheafFrames

end KltDP.Geometry.ChartFrameAtlasSheaf

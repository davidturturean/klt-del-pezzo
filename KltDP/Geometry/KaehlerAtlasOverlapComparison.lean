import KltDP.Geometry.KaehlerChartAtlas
import KltDP.Geometry.KaehlerOverlapFrame
import KltDP.Geometry.KaehlerOverlapRefinement

/-!
# The atlas transition unit and the localization transition unit differ by a coboundary

Route 1 builds the atlas unit from a **free-sheaf** frame (`ChartKaehlerOpenFrame.chartOpenFrame`,
valid on every open below a chart); route 2 builds `KaehlerOverlapFrame.overlapTransitionUnit` from a
**localization** frame on a common basic open. These are two different bases of the *same* module —
the sections `Ω_{X/k}(V)` — so the two unit families are **not** equal, and asking for a rewrite
between them is asking for the wrong thing. Their comparison is itself a frame-change determinant,
and that determinant is the content of this module.

* **`overlapComparisonUnit i`** — the ratio: `frameChangeUnit` of the restricted free-sheaf frame
  against the transported localization frame, an honest `Γ(X, V)ˣ` with no cast, because both are
  bases of `(baseRingSheaf f).val.obj (op V)`.
* **`comparison_mul_overlapTransitionUnit`** — the identity, in inverse-free form:
  `ratio i * overlapTransitionUnit = res (atlas unit) * ratio j`.
* **`res_transitionUnit_eq`** — the same with the ratio explicit:
  `res (atlas unit i j) = ratio i * overlapTransitionUnit * (ratio j)⁻¹`.
* **`exists_overlap_comparison`** — the hypotheses are inhabited around every point of an overlap,
  by `KaehlerOverlapRefinement.exists_common_basicOpen_isAffineOpen`, so the identity is not vacuous.

**This is a cocycle-level statement, not a pointwise one.** `res_transitionUnit_eq` says the two
transition-unit families differ by the coboundary `i ↦ ratio i`; a coboundary is exactly what does
not change the glued class, which is why the two routes may be compared at all.

**No new machinery was needed.** The proof is two applications of
`TopDifferentialFrameChange.frameChangeUnit_mul`: both sides collapse to
`frameChangeUnit (free-sheaf frame of i) (localization frame of j)`. The only other inputs are
`AffineDifferentialSectionsFrame.frameChangeUnit_sectionsFrame` (the transport to sections leaves the
unit unchanged, since it is linear over `Γ(X, V)` itself) and
`ChartFrameAtlasSheaf.chartUnitOn_restrict` (the atlas unit restricts correctly), both accepted or
queued. `frameChangeUnit` occurs nowhere in the accepted tree, so no prior comparison lemma existed
to reuse.

Nothing is admitted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.SchemeKaehlerSheaf
open KltDP.Geometry.TopDifferentialFrameChange
open KltDP.Geometry.TransitionUnitGluing
open KltDP.Geometry.ChartFrameAtlasSheaf
open KltDP.Geometry.ChartKaehlerOpenFrame
open KltDP.Geometry.KaehlerChartAtlas
open KltDP.Geometry.KaehlerOverlapFrame
open KltDP.Geometry.AffineDifferentialSectionsFrame
open KltDP.Geometry.KaehlerOverlapRefinement

universe u

namespace KltDP.Geometry.KaehlerAtlasOverlapComparison

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
variable {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
variable {n : ℕ}
variable (b : ∀ i, letI := chartAlgebra f U hU i; Basis (Fin n) Γ(X, U i) (KaehlerDifferential k Γ(X, U i)))

/-- **The ratio between the two frames on a common basic open.** The free-sheaf frame of the chart
`U i`, restricted to `V`, against the localization frame of the same chart transported to the
sections over `V`. Both are bases of `Ω_{X/k}(V)`, so this is an ordinary frame-change unit: no
transport, no cast. -/
def overlapComparisonUnit (i : ι) {V : X.Opens} (hV : IsAffineOpen V)
    (r : Γ(X, U i)) (hVi : V ≤ U i) (hr : X.basicOpen r = V) : Γ(X, V)ˣ := by
  letI : Algebra k Γ(X, U i) := chartAlgebra f U hU i
  letI : Algebra k Γ(X, V) := (baseToAffineSectionsMap f hV).hom.toAlgebra
  exact frameChangeUnit (chartOpenFrame f (hU i) (b i) V hVi)
    (sectionsFrame f hV (overlapFrame f (hU i) hV r hVi hr (b i)))

/-- **The comparison identity, in inverse-free form.** Both sides are the frame-change unit from the
free-sheaf frame of `i` to the transported localization frame of `j`. -/
theorem comparison_mul_overlapTransitionUnit (i j : ι) {V : X.Opens} (hV : IsAffineOpen V)
    (r : Γ(X, U i)) (s : Γ(X, U j)) (hVij : V ≤ U i ⊓ U j)
    (hr : X.basicOpen r = V) (hs : X.basicOpen s = V) :
    overlapComparisonUnit f U hU b i hV r (hVij.trans inf_le_left) hr *
        overlapTransitionUnit f (hU i) (hU j) hV r s
          (hVij.trans inf_le_left) (hVij.trans inf_le_right) hr hs (b i) (b j) =
      Units.map (res X hVij).toMonoidHom
          (transitionUnit U (differentialSections f)
            (fun i W hW => chartOpenFrame f (hU i) (b i) W hW) i j) *
        overlapComparisonUnit f U hU b j hV s (hVij.trans inf_le_right) hs := by
  letI : Algebra k Γ(X, V) := (baseToAffineSectionsMap f hV).hom.toAlgebra
  -- the atlas unit restricted to `V` is the frame-change unit of the two restricted frames
  have hres : Units.map (res X hVij).toMonoidHom
      (transitionUnit U (differentialSections f)
        (fun i W hW => chartOpenFrame f (hU i) (b i) W hW) i j) =
      frameChangeUnit (chartOpenFrame f (hU i) (b i) V (hVij.trans inf_le_left))
        (chartOpenFrame f (hU j) (b j) V (hVij.trans inf_le_right)) := by
    apply Units.ext
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    exact (chartUnitOn_restrict (U := U) (L := differentialSections f)
      (restr := differentialRestr f)
      (frame := fun i W hW => chartOpenFrame f (hU i) (b i) W hW)
      (hframe := fun i _ _ hVW hW t => chartOpenFrame_restrict f (hU i) (b i) hVW hW t)
      hVij i j inf_le_left inf_le_right).symm
  -- the localization unit, carried to sections, is unchanged
  have hsec : overlapTransitionUnit f (hU i) (hU j) hV r s
        (hVij.trans inf_le_left) (hVij.trans inf_le_right) hr hs (b i) (b j) =
      frameChangeUnit
        (sectionsFrame f hV (overlapFrame f (hU i) hV r (hVij.trans inf_le_left) hr (b i)))
        (sectionsFrame f hV (overlapFrame f (hU j) hV s (hVij.trans inf_le_right) hs (b j))) :=
    (frameChangeUnit_sectionsFrame f hV _ _).symm
  rw [hres, hsec]
  show frameChangeUnit _ _ * frameChangeUnit _ _ = frameChangeUnit _ _ * frameChangeUnit _ _
  rw [frameChangeUnit_mul, frameChangeUnit_mul]

/-- **The comparison identity with the ratio explicit.** The atlas transition unit, restricted to a
common basic open, is the localization transition unit conjugated by the comparison ratios — that
is, the two families differ by the coboundary of `overlapComparisonUnit`. -/
theorem res_transitionUnit_eq (i j : ι) {V : X.Opens} (hV : IsAffineOpen V)
    (r : Γ(X, U i)) (s : Γ(X, U j)) (hVij : V ≤ U i ⊓ U j)
    (hr : X.basicOpen r = V) (hs : X.basicOpen s = V) :
    Units.map (res X hVij).toMonoidHom
        (transitionUnit U (differentialSections f)
          (fun i W hW => chartOpenFrame f (hU i) (b i) W hW) i j) =
      overlapComparisonUnit f U hU b i hV r (hVij.trans inf_le_left) hr *
        overlapTransitionUnit f (hU i) (hU j) hV r s
          (hVij.trans inf_le_left) (hVij.trans inf_le_right) hr hs (b i) (b j) *
        (overlapComparisonUnit f U hU b j hV s (hVij.trans inf_le_right) hs)⁻¹ := by
  rw [comparison_mul_overlapTransitionUnit f U hU b i j hV r s hVij hr hs,
    mul_inv_cancel_right]

include hU in
/-- **The hypotheses of the comparison are inhabited.** Around every point of an overlap of two
affine charts there is a common basic open on which the identity applies, so it is not vacuous. -/
theorem exists_overlap_comparison (i j : ι) (x : X) (hx : x ∈ U i ⊓ U j) :
    ∃ (r : Γ(X, U i)) (s : Γ(X, U j)), X.basicOpen s = X.basicOpen r ∧
      x ∈ X.basicOpen r ∧ X.basicOpen r ≤ U i ⊓ U j ∧ IsAffineOpen (X.basicOpen r) := by
  obtain ⟨r, s, hrs, hxr, hle, haff⟩ :=
    exists_common_basicOpen_isAffineOpen (hU i) (hU j) x hx
  exact ⟨r, s, hrs.symm, hxr, hle, haff⟩

end KltDP.Geometry.KaehlerAtlasOverlapComparison

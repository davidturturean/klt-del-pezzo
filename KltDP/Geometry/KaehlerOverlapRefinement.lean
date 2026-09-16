import KltDP.Geometry.AffineOpenRefinement

/-!
# Overlaps of affine charts are covered by opens basic in **both** charts

BRIEF33's overlap route needs, on the overlap of two affine charts, an open on which the section ring
is a localization of *each* chart ring — because only then does the chart frame promote
(`KaehlerLocalizedFrame.localizedFrame`) without any étale hypothesis and without free-sheaf sections.
An overlap of two affine opens is affine (accepted `AffineOpenRefinement.pair_affine`), but it is in
general a basic open of *neither* chart, which is exactly the gap this module closes.

The pinned `AlgebraicGeometry.exists_basicOpen_le_affine_inter` already provides the two-sided basic
open; Mathlib uses it itself in `AffineScheme.lean`.  What is added here is only the packaging the
refinement needs:

* **`exists_common_basicOpen`**: around every point of `U ⊓ V` there are `f : Γ(X, U)` and
  `g : Γ(X, V)` with `X.basicOpen f = X.basicOpen g`, containing the point and **contained in
  `U ⊓ V`** — the containment is what makes it usable as a refinement index.
* **`exists_common_basicOpen_isAffineOpen`**: the same open is affine, so it is again a legitimate
  chart for the frames.

Both section rings are then localizations of the respective chart rings by the pinned
`IsAffineOpen.isLocalization_basicOpen`, which is the hypothesis
`KaehlerLocalizedFrame.localizedFrame` consumes.  No new hypothesis enters the tree; nothing is
admitted here.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace KltDP.Geometry.KaehlerOverlapRefinement

variable {X : Scheme.{u}}

/-- **Every point of an overlap of two affine opens lies in an open that is a basic open of both**,
and that open is contained in the overlap. -/
theorem exists_common_basicOpen {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (x : X) (hx : x ∈ U ⊓ V) :
    ∃ (f : Γ(X, U)) (g : Γ(X, V)), X.basicOpen f = X.basicOpen g ∧
      x ∈ X.basicOpen f ∧ X.basicOpen f ≤ U ⊓ V := by
  obtain ⟨f, g, hfg, hxf⟩ := AlgebraicGeometry.exists_basicOpen_le_affine_inter hU hV x hx
  refine ⟨f, g, hfg, hxf, le_inf (X.basicOpen_le f) ?_⟩
  rw [hfg]
  exact X.basicOpen_le g

/-- The common basic open of the previous statement is itself an affine open. -/
theorem exists_common_basicOpen_isAffineOpen {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (x : X) (hx : x ∈ U ⊓ V) :
    ∃ (f : Γ(X, U)) (g : Γ(X, V)), X.basicOpen f = X.basicOpen g ∧
      x ∈ X.basicOpen f ∧ X.basicOpen f ≤ U ⊓ V ∧ IsAffineOpen (X.basicOpen f) := by
  obtain ⟨f, g, hfg, hxf, hle⟩ := exists_common_basicOpen hU hV x hx
  exact ⟨f, g, hfg, hxf, hle, hU.basicOpen f⟩

end KltDP.Geometry.KaehlerOverlapRefinement

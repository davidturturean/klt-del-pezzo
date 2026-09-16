import KltDP.Geometry.TransitionUnitSections
import KltDP.Geometry.TransitionUnitExtraction

/-!
# The transition unit of an atlas is the ratio of its chart generators

An invertible sheaf `M` with an atlas `t` has, on each chart `l`, a chart coordinate
`TransitionUnitExtraction.chartEquiv X M t l : M.val.obj (op W) ≃ₗ[Γ(X, W)] Γ(X, W)`, and its
transition units are characterised by the accepted `transitionUnits_mul_chart`.

When `M` carries a map `ι : M ⟶ 𝒪_X` — an ideal sheaf and its inclusion is the case of interest —
each chart has a **generator** `chartGenerator ι l := ι (chartEquiv_l⁻¹ 1)`, the section of `𝒪_X`
generating the ideal on that chart. This module proves the two facts that make generators usable:

* **`app_eq_chartEquiv_mul_chartGenerator`**: `ι s = chartEquiv_l s * chartGenerator l` for every
  section `s` — the chart coordinate *is* the coefficient against the generator;
* **`transitionUnits_mul_chartGenerator`**: `g_{ij} · d_i = d_j`, the transition unit is the ratio
  of the two generators.

Both follow from linearity alone: `s = (chartEquiv_l s) • (chartEquiv_l⁻¹ 1)`, so `ι` and the chart
equivalence do all the work, and `transitionUnits` is used only through the accepted
`transitionUnits_mul_chart`. **It is never unfolded** — unfolding it syntactically costs
`maxRecDepth 4096` even on `P¹` (accepted `ProjectiveLineCanonicalOverlap`).

Nothing here is over-site typed: every statement is an equation in `Γ(X, W)`, and all over-site
content stays inside the accepted generic `chartEquiv`/`transitionUnits` API.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.TransitionUnitGenerator

open KltDP.Geometry.TransitionUnitGluing KltDP.Geometry.TransitionUnitExtraction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) (M : X.Modules)
  (t : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M)
  (ι : M ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)

/-- The generator of `M` on chart `l`, read through `ι`: the image of the section whose chart
coordinate is `1`. -/
def chartGenerator (l : t.I) {W : X.Opens} (hWl : W ≤ t.X l) : Γ(X, W) :=
  ι.val.app (op W) ((chartEquiv X M t l hWl).symm 1)

/-- A section with chart coordinate `c` has image `c` times the chart generator. -/
theorem chartGenerator_smul (l : t.I) {W : X.Opens} (hWl : W ≤ t.X l) (c : Γ(X, W)) :
    ι.val.app (op W) ((chartEquiv X M t l hWl).symm c) =
      c * chartGenerator X M t ι l hWl := by
  have hc : (chartEquiv X M t l hWl).symm c = c • ((chartEquiv X M t l hWl).symm 1) := by
    rw [← LinearEquiv.map_smul, smul_eq_mul, mul_one]
  rw [hc]
  change (ι.val.app (op W)).hom (c • ((chartEquiv X M t l hWl).symm 1)) = _
  rw [map_smul, smul_eq_mul]
  rfl

/-- **The chart coordinate is the coefficient against the chart generator.** -/
theorem app_eq_chartEquiv_mul_chartGenerator (l : t.I) {W : X.Opens} (hWl : W ≤ t.X l)
    (s : M.val.obj (op W)) :
    ι.val.app (op W) s = chartEquiv X M t l hWl s * chartGenerator X M t ι l hWl := by
  have h := chartGenerator_smul X M t ι l hWl (chartEquiv X M t l hWl s)
  rwa [LinearEquiv.symm_apply_apply] at h

/-- **The transition unit is the ratio of the two chart generators**: `g_{ij} · d_i = d_j`. -/
theorem transitionUnits_mul_chartGenerator (i j : t.I) {W : X.Opens}
    (hWi : W ≤ t.X i) (hWj : W ≤ t.X j) :
    res X (le_inf hWi hWj) (transitionUnits X M t i j) * chartGenerator X M t ι i hWi =
      chartGenerator X M t ι j hWj := by
  have h := transitionUnits_mul_chart X M t i j hWi hWj ((chartEquiv X M t j hWj).symm 1)
  rw [LinearEquiv.apply_symm_apply, mul_one] at h
  rw [h]
  exact (app_eq_chartEquiv_mul_chartGenerator X M t ι i hWi
    ((chartEquiv X M t j hWj).symm 1)).symm

end KltDP.Geometry.TransitionUnitGenerator

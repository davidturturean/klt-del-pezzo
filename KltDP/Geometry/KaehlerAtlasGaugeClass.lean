import KltDP.Geometry.TransitionUnitPicard
import KltDP.Geometry.KaehlerAtlasOverlapComparison

/-!
# Conjugating a transition cocycle by a unit family does not move its Picard class

BRIEF41 showed that the atlas transition units and the localization transition units differ, on a
common basic open, by the ratio `overlapComparisonUnit`. This module supplies the gluing half: a
cocycle conjugated by a family of chart units glues to the same Picard class.

**What is already accepted, and is therefore not rebuilt here.** The algebraic heart —
*a coboundary does not move a glued class* — is the accepted
`TransitionUnitGluing.picardClass_eq_of_gauge`, via `IsGauge` and `gaugeIso`; refinement invariance
is the accepted `refinementIso`. Both were found by searching the tree rather than assumed absent;
`IsGauge` is the project's name for the gauge/coboundary equation `res(bᵢ)·gᵢⱼ = hᵢⱼ·res(bⱼ)`.

* **`conjugatedUnits b g i j := res(bᵢ) · gᵢⱼ · res(bⱼ)⁻¹`** — the conjugate family.
* **`conjugatedUnits_isCocycle`** — it is again a cocycle. This is the one genuinely computational
  step: the inner `res(bⱼ)⁻¹·res(bⱼ)` cancels at the triple overlap, mirroring the accepted
  `productUnits_isCocycle`.
* **`isGauge_conjugatedUnits`** — the gauge equation. **This holds by construction**: the conjugate
  is *defined* so that it holds, and the proof is cancellation. It is recorded because
  `picardClass_eq_of_gauge` consumes it, not because it carries content.
* **`picardClass_conjugatedUnits`** — hence the glued classes agree. **Also free**, being the
  accepted gauge theorem applied to the previous line.
* **`res_transitionUnit_eq_conjugated`** — the content: on a common basic open the conjugate of the
  atlas units by the comparison ratios **is** the localization transition unit of BRIEF41.

## What this does NOT prove, and why it cannot as stated

It does not exhibit a *route-2 glued sheaf* and equate it with route 1's, because **route 2 has no
glued sheaf to exhibit**. `IsCocycle` and `IsGauge` both require their unit family on **every**
pairwise intersection of a cover; `overlapTransitionUnit` exists only on opens that are basic in
*both* charts, and an intersection of two such opens is basic in neither (the obstruction recorded in
BRIEF37, which is why route 1 was needed at all). Defining a total family by conjugation and then
observing the classes agree would be true by construction and would carry no information.

So the honest statement is the one proved here: the class is unchanged under conjugation by any
chart-unit family, **and** the conjugated family agrees with route 2's units wherever route 2 is
defined. That is what makes the two routes comparable; it is not a claim that route 2 glues.

Nothing is admitted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.TransitionUnitGluing

universe u

namespace KltDP.Geometry.KaehlerAtlasGaugeClass

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
  (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ) (b : ∀ i : ι, Γ(X, U i)ˣ)

/-- **The cocycle conjugated by a family of chart units.** -/
def conjugatedUnits (i j : ι) : Γ(X, U i ⊓ U j)ˣ :=
  Units.map (res X (inf_le_left : U i ⊓ U j ≤ U i)).toMonoidHom (b i) * g i j *
    (Units.map (res X (inf_le_right : U i ⊓ U j ≤ U j)).toMonoidHom (b j))⁻¹

@[simp]
theorem conjugatedUnits_val (i j : ι) :
    (conjugatedUnits X U g b i j : Γ(X, U i ⊓ U j)) =
      res X (inf_le_left : U i ⊓ U j ≤ U i) (b i) * (g i j : Γ(X, U i ⊓ U j)) *
        res X (inf_le_right : U i ⊓ U j ≤ U j)
          (((b j)⁻¹ : Γ(X, U j)ˣ) : Γ(X, U j)) := rfl

/-- **The gauge equation for the conjugate — true by construction.** Recorded because
`picardClass_eq_of_gauge` consumes it. -/
theorem isGauge_conjugatedUnits : IsGauge X U g (conjugatedUnits X U g b) b := by
  intro i j
  rw [conjugatedUnits_val]
  have hcancel : res X (inf_le_right : U i ⊓ U j ≤ U j)
        (((b j)⁻¹ : Γ(X, U j)ˣ) : Γ(X, U j)) *
      res X (inf_le_right : U i ⊓ U j ≤ U j) ((b j : Γ(X, U j))) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  calc res X (inf_le_left : U i ⊓ U j ≤ U i) (b i) * (g i j : Γ(X, U i ⊓ U j))
      = res X (inf_le_left : U i ⊓ U j ≤ U i) (b i) * (g i j : Γ(X, U i ⊓ U j)) * 1 := by
        rw [mul_one]
    _ = res X (inf_le_left : U i ⊓ U j ≤ U i) (b i) * (g i j : Γ(X, U i ⊓ U j)) *
          (res X (inf_le_right : U i ⊓ U j ≤ U j)
              (((b j)⁻¹ : Γ(X, U j)ˣ) : Γ(X, U j)) *
            res X (inf_le_right : U i ⊓ U j ≤ U j) ((b j : Γ(X, U j)))) := by
        rw [hcancel]
    _ = res X (inf_le_left : U i ⊓ U j ≤ U i) (b i) * (g i j : Γ(X, U i ⊓ U j)) *
          res X (inf_le_right : U i ⊓ U j ≤ U j)
            (((b j)⁻¹ : Γ(X, U j)ˣ) : Γ(X, U j)) *
          res X (inf_le_right : U i ⊓ U j ≤ U j) ((b j : Γ(X, U j))) := by
        ring

/-- Pure commutative-ring cancellation, with no restriction maps in it: this is the whole
content of the conjugated cocycle law, stated so that the restriction terms are filled by
unification against the goal rather than written out. -/
private theorem conj_mul_aux {R : Type*} [CommRing R]
    (ai gij bj' bj gjl bl' gil : R) (hb : bj' * bj = 1) (hgg : gij * gjl = gil) :
    ai * gij * bj' * (bj * gjl * bl') = ai * gil * bl' := by
  calc ai * gij * bj' * (bj * gjl * bl')
      = ai * gij * (bj' * bj) * gjl * bl' := by ring
    _ = ai * gij * gjl * bl' := by rw [hb, mul_one]
    _ = ai * (gij * gjl) * bl' := by ring
    _ = ai * gil * bl' := by rw [hgg]

/-- **The conjugate of a cocycle is a cocycle.** The one computational step: the inner
`res(bⱼ)⁻¹ · res(bⱼ)` cancels at the triple overlap. -/
theorem conjugatedUnits_isCocycle (hg : IsCocycle X U g) :
    IsCocycle X U (conjugatedUnits X U g b) where
  unit_self i := by
    rw [conjugatedUnits_val, hg.unit_self i, mul_one, ← map_mul, Units.mul_inv, map_one]
  mul_res i j l := by
    simp only [conjugatedUnits_val, map_mul, res_res]
    exact conj_mul_aux _ _ _ _ _ _ _
      (by rw [← map_mul, Units.inv_mul, map_one]) (hg.mul_res i j l)

/-- **Conjugation does not move the Picard class.** Immediate from the accepted
`picardClass_eq_of_gauge`; recorded as the statement the atlas comparison consumes. -/
theorem picardClass_conjugatedUnits (hg : IsCocycle X U g) (hU : (⨆ i, U i) = ⊤) :
    picardClass X U g hg hU =
      picardClass X U (conjugatedUnits X U g b)
        (conjugatedUnits_isCocycle X U g b hg) hU :=
  picardClass_eq_of_gauge X U g hg hU (conjugatedUnits X U g b)
    (conjugatedUnits_isCocycle X U g b hg) b (isGauge_conjugatedUnits X U g b)

end KltDP.Geometry.KaehlerAtlasGaugeClass

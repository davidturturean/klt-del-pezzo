import KltDP.Examples.FrobeniusGraphGenericPointOffFiber
import KltDP.Examples.ProjectiveLinePointAtInfinity
import KltDP.Examples.FrobeniusFiberZeroInvertible

/-!
# The support of the vertical fibre is the fibre: the first coordinate (BRIEF54, blocker 1)

BRIEF53 named the count as the one thing blocking `B · a = 1` once the class is available, and named
its missing half precisely: **the support of `verticalFiberDivisorAt c` on the product is identified
nowhere.** That claim is re-checked and stands — every `.support` statement in this lane's queued
modules (`genericPoint_not_mem_support_verticalFiberAt`,
`graphGenericPoint_not_mem_support_verticalFiberAt`,
`fiberGenericPoint_not_mem_support_verticalFiberAt`) is a **non-membership at a single generic
point**, never an identification of the support as a set. What *is* available is the bridge
`mem_support_pullbackDivisor_iff`, which relates the two pullback layers but says nothing about the
bottom one.

This module supplies the missing direction: a point **in** the support has first coordinate `x = c`.

## The lever, and why it costs nothing

`verticalZeroDivisor` is glued from `x` on `rulingOpen 0 0` and **`1`** on `rulingOpen 0 1`, and
`verticalZeroRulingChart` already packages the second as a regular chart with coefficient `1`. So
every point of `rulingOpen 0 1` is off the support because the germ of `1` is a unit — no `.app`, no
stalk computation. That is this lane's rule 1 ("check whether the divisor already has a chart whose
equation is `1`") used a second time.

The queued `not_mem_support_verticalZero_of_fst_generic` proves exactly this but **only for a generic
first coordinate**, because that is all its caller needed. Stated for an arbitrary point of
`rulingOpen 0 1` it gives the whole containment, by contraposition:
`rulingOpen 0 1 = rulingProjection 0 ⁻¹ᵁ chartOpen k 1`, so a point of the support has first
coordinate outside `chartOpen k 1`, and `P¹ ∖ {X₁ ≠ 0} = {[1:0]}`.

That last fact is the mirror of the accepted `eq_infinityPoint_of_not_mem_chart` with the two chart
indices swapped; `otherIndex_zero` is accepted, so the mirror is the same proof.

* **`eq_point_zero_of_not_mem_chartOpen_one`** — `P¹ ∖ chartOpen k 1 = {point 0}`;
* **`not_mem_support_verticalZero_of_mem_rulingOpen_one`** — the general form of the queued lemma;
* **`mem_support_verticalZero_fst`** — a point of `Supp(x = 0)` has first coordinate `point 0`;
* **`mem_support_verticalFiberAt_fst`** — a point of `Supp(x = c)` has first coordinate `point c`,
  by `mem_support_pullbackDivisor_iff` and `productTranslation_fst`, undoing the translation with the
  accepted `projectiveTranslation_comp_neg`.

## What this does NOT give

**No row, and not yet the count.** The count needs `B ∩ Supp D` to be a *singleton*:

* the **subsingleton** half still needs the other inclusion — that a stage point of `Supp` lies in
  `Set.range (verticalLift c hc (n+1)).base`, which is what
  `graphStrictPrimeCurve_inter_vertical_subsingleton` is stated against. This module gives the first
  coordinate of such a point; turning that into membership of the *lift's range* needs the range of
  `verticalLift`, which is not characterised anywhere;
* the **nonempty** half is untouched here. It looks reachable from BRIEF52 rather than from geometry:
  the germ of the divisor's coefficient at the crossing point maps to `localParameter c`, which is
  irreducible hence a non-unit, and a ring homomorphism carries units to units — so the germ upstairs
  cannot be a unit either, which is exactly support membership by `mem_support_iff_not_isUnit_germ`.
  That is a route, not a proof, and it is not attempted here.

Characteristic-free and primality-free; `c` arbitrary, including `c = 0`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusVerticalSupportFibre

open KltDP.Geometry
open KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
open KltDP.Geometry.ProjectiveLineComparison
open KltDP.Geometry.ProjectiveLineTranslation
open FrobeniusProjectivePoints FrobeniusGraphClosed
open FrobeniusGraphStalkContact
open FrobeniusGraphPicardClassPowerCharts FrobeniusGraphPicardClassMixedOverlap
open FrobeniusGraphPicardClassRulingCoordinates FrobeniusGraphPicardClassRulingDivisors
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusFiberZeroInvertible
open ProjectiveProductTranslation
open ProjectiveLinePointAtInfinity
open FrobeniusGraphGenericPointOffFiber

variable {k : Type u} [Field k]

/-- `mem_support_iff_not_isUnit_germ` carries `[IsIntegral Y]` in its statement, so the instance is
needed to elaborate the types below, not merely the proofs. -/
local instance supportFibreProductIntegral : IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- **`P¹ ∖ chartOpen k 1 = {[1:0]}`.** The mirror of the accepted `eq_infinityPoint_of_not_mem_chart`
with the chart indices swapped: a point off the second chart lies on the first at a prime containing
`X`, and the only such prime of `k[X]` is `(X)`. -/
theorem eq_point_zero_of_not_mem_chartOpen_one (y : projectiveSpace k 1)
    (hy : y ∉ chartOpen k 1) : y = point (0 : k) := by
  obtain ⟨z, hz⟩ := (polynomialAffineCover k).covers y
  have key : ∀ i : Fin 2, (polynomialChartMap k i).base z = y → y = point (0 : k) := by
    intro i hi
    have hi2 : i = 0 ∨ i = 1 := by fin_cases i <;> decide
    rcases hi2 with rfl | rfl
    · have h := polynomialChart_mem_other_iff (k := k) 0 z
      rw [otherIndex_zero, hi] at h
      have hX : (Polynomial.X : Polynomial k) ∈ z.asIdeal := by
        by_contra hnot
        exact hy (h.mpr hnot)
      rw [← hi, eq_parameterSchemePoint_zero_of_X_mem z hX, ← point_eq_chart]
    · exfalso
      apply hy
      rw [← hi]
      have h : (polynomialChartMap k 1).base z ∈ (polynomialChartMap k 1).opensRange := ⟨z, rfl⟩
      rwa [polynomialChartMap_opensRange] at h
  exact key _ hz

/-- **Every point of `rulingOpen 0 1` is off the support of the fibre `x = 0`** — the general form of
the queued `not_mem_support_verticalZero_of_fst_generic`, which assumes the first coordinate generic.
On that open the divisor's regular coefficient is literally `1`, whose germ is a unit. -/
theorem not_mem_support_verticalZero_of_mem_rulingOpen_one (w : projectiveProduct k)
    (hw : w ∈ rulingOpen (k := k) 0 1) :
    w ∉ (effectiveCartierIdealDataOfRegularEquations (projectiveProduct k)
      (verticalZeroDivisor (k := k)) verticalZeroDivisor_hasRegularEquations).support := by
  intro h
  rw [mem_support_iff_not_isUnit_germ (verticalZeroDivisor (k := k))
    verticalZeroDivisor_hasRegularEquations (verticalZeroRulingChart (k := k)) w hw] at h
  apply h
  show IsUnit ((projectiveProduct k).presheaf.germ (rulingOpen (k := k) 0 1) w hw
    (1 : Γ(projectiveProduct k, rulingOpen (k := k) 0 1)))
  have h1 : (projectiveProduct k).presheaf.germ (rulingOpen (k := k) 0 1) w hw
      (1 : Γ(projectiveProduct k, rulingOpen (k := k) 0 1)) = 1 := by simp
  rw [h1]
  exact isUnit_one

/-- **A point of `Supp(x = 0)` has first coordinate `[1:0]`.** -/
theorem mem_support_verticalZero_fst (w : projectiveProduct k)
    (hw : w ∈ (effectiveCartierIdealDataOfRegularEquations (projectiveProduct k)
      (verticalZeroDivisor (k := k)) verticalZeroDivisor_hasRegularEquations).support) :
    (firstProjection (k := k)).base w = point (0 : k) := by
  apply eq_point_zero_of_not_mem_chartOpen_one
  intro hmem
  exact not_mem_support_verticalZero_of_mem_rulingOpen_one w hmem hw

/-- The inverse vertical translation is injective on points: it is an isomorphism, with inverse
`projectiveTranslation c` on the first factor. -/
theorem projectiveTranslation_neg_base_injective (c : k) (a b : projectiveSpace k 1)
    (hab : (projectiveTranslation (k := k) (-c)).base a =
      (projectiveTranslation (k := k) (-c)).base b) : a = b := by
  have h1 : (projectiveTranslation (k := k) (-c) ≫ projectiveTranslation c).base a =
      (projectiveTranslation (k := k) (-c) ≫ projectiveTranslation c).base b := by
    rw [Scheme.comp_base_apply, Scheme.comp_base_apply, hab]
  rw [projectiveTranslation_comp_neg] at h1
  simpa using h1

/-- **A point of `Supp(x = c)` has first coordinate `[1:c]`**, for every `c`. The fibre `x = c` is a
`pullbackDivisor` along the translation, so `mem_support_pullbackDivisor_iff` reduces to `x = 0`, and
`productTranslation_fst` moves the first coordinate by `projectiveTranslation (-c)`. -/
theorem mem_support_verticalFiberAt_fst (c : k) (w : projectiveProduct k)
    (hw : w ∈ (effectiveCartierIdealDataOfRegularEquations (projectiveProduct k)
      (verticalFiberDivisorAt (k := k) c)
      (verticalFiberDivisorAt_hasRegularEquations c)).support) :
    (firstProjection (k := k)).base w = point c := by
  -- `verticalFiberDivisorAt c` *is* a `pullbackDivisor` by definition, so `.mp` applies to `hw`
  -- through the folded `def` where `rw` would need equation lemmas it does not supply.
  have h' := (mem_support_pullbackDivisor_iff (verticalTranslation (k := k) c).inv
    (verticalZeroDivisor (k := k)) verticalZeroDivisor_hasRegularEquations w).mp hw
  have hfst := mem_support_verticalZero_fst _ h'
  have hmor : (verticalTranslation (k := k) c).inv ≫ firstProjection =
      firstProjection ≫ projectiveTranslation (-c) := by
    rw [verticalTranslation_inv]
    exact productTranslation_fst (-c) (-(0 : k))
  have hpt := congrArg (fun m : projectiveProduct k ⟶ projectiveSpace k 1 => m.base w) hmor
  simp only [Scheme.comp_base_apply] at hpt
  rw [hpt] at hfst
  have hc0 : (projectiveTranslation (k := k) (-c)).base (point c) = point (0 : k) := by
    change fieldMorphismPoint (pointMorphism c ≫ projectiveTranslation (-c)) = point (0 : k)
    rw [pointMorphism_projectiveTranslation, add_neg_cancel]
    rfl
  exact projectiveTranslation_neg_base_injective c _ _ (hfst.trans hc0.symm)

end KltDP.Examples.FrobeniusVerticalSupportFibre

namespace KltDP.Examples

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusGraphClosed
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusVerticalSupportFibre

local instance supportFibreProductIntegralTop {k : Type u} [Field k] :
    IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- **F29: a point of the support of the vertical fibre `x = c` has first coordinate `[1:c]`.**
The containment `Supp(x = c) ⊆ (x = c)` that the intersection count needs, produced from the chart on
which the divisor's equation is literally `1` — not assumed, and not previously available: every other
support statement in this development is a non-membership at a single generic point. -/
theorem f29_vertical_support_first_coordinate (k : Type u) [Field k] (c : k)
    (w : projectiveProduct k)
    (hw : w ∈ (effectiveCartierIdealDataOfRegularEquations (projectiveProduct k)
      (verticalFiberDivisorAt (k := k) c)
      (verticalFiberDivisorAt_hasRegularEquations c)).support) :
    (firstProjection (k := k)).base w = point c :=
  mem_support_verticalFiberAt_fst c w hw

/-- The statement has exactly one universe parameter. -/
theorem f29_vertical_support_first_coordinate_universe_check (k : Type u) [Field k] (c : k)
    (w : projectiveProduct k)
    (hw : w ∈ (effectiveCartierIdealDataOfRegularEquations (projectiveProduct k)
      (verticalFiberDivisorAt (k := k) c)
      (verticalFiberDivisorAt_hasRegularEquations c)).support) : True := by
  have _ := f29_vertical_support_first_coordinate.{u} k c w hw
  trivial

end KltDP.Examples

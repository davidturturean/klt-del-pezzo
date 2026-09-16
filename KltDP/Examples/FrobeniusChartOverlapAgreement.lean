import KltDP.Examples.FrobeniusSecondChartOrder
import KltDP.Examples.FrobeniusBlowupDifferentialOverlap
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.GroupWithZero.Associated

/-!
# Agreement of the two chart orders on the overlap

Globalisation piece 2 of 3. The first chart gives `σ^*f = u^(ord f)·g₁` with `u ∤ g₁`
(`FrobeniusChartOrderExact.chartOrderExact`) and the second gives `ς^*f = u^(ord f)·g₂` with `u ∤ g₂`
(`FrobeniusSecondChartOrder.secondChartOrderExact`). This module proves that those two factorisations
are the *same* factorisation, seen on the intersection of the two charts.

## What the agreement actually asserts, and what would be vacuous

Both queued statements are phrased with the **same** exponent `centerOrder f`, because both were
derived from the one adic order of the plane. So "the exponents agree" is, as those two statements
stand, true by construction and carries no geometry. It is recorded here in the form that does carry
some:

* `chartExponent_eq_centerOrder` and `secondChartExponent_eq_centerOrder` — for **any** `a` and any
  factorisation `σ^*f = u^a·g` with `u ∤ g` (respectively on the second chart), `a = centerOrder f`.
  The exponent is *forced*, not chosen; the cofactor being prime to `u` is what forces it.
* `chart_exponents_agree` — hence two factorisations produced independently on the two charts, with
  no mention of the order in their hypotheses, have equal exponents.

The substantive half is the comparison of the **cofactors**, which genuinely needs the overlap:

* `cofactor_transition_of_factorizations` — `g₁` and `g₂` become associates on the overlap, the unit
  being exactly the `n`-th power of the chart ratio `overlapT`.

## The obligation had moved: nothing about the overlap was built here

Re-deriving against the API that exists now, rather than following the route recorded when the caveat
was written, removed the whole of the expected construction. Already accepted, and used verbatim:

* the overlap ring `conormalOverlapRing centerIdeal centerU centerV` with **both** restriction maps
  `conormalOverlapLeft`, `conormalOverlapRight` and the common base map `conormalOverlapBaseMap`;
* the coordinate identities `overlapU * overlapT = overlapV`, `overlapV * overlapS = overlapU` and
  `overlapT * overlapS = 1` (`FrobeniusBlowupDifferentialOverlap`);
* `conormalOverlapEquationLeft_regular`, which is precisely the statement that `overlapU` is a
  nonzerodivisor — the cancellation this comparison turns on.

**No transition ring map between the two charts was constructed, and none is needed.** The two
polynomial models are pushed into the one accepted overlap ring, where the point is that the two
blowdowns land on the same element: `firstChartToOverlap ∘ chartSubstitution = overlapBaseMap =
secondChartToOverlap ∘ secondSubstitution`. Building a transition isomorphism and conjugating by it
would prove the same thing with an extra localisation API in between.

## The structural point, in the corrected orientation

`secondSubstitution` is `u ↦ u·v`, `v ↦ u`, so the second chart's exceptional coordinate is `uCoord`
**again**, not `vCoord` — the chart is relabelled, not mirrored. Under the two maps into the overlap
the *same* symbol `uCoord` therefore goes to two *different* elements:

`firstChartToOverlap uCoord = overlapU`   and   `secondChartToOverlap uCoord = overlapV`,

and those differ by the unit `overlapT`. Reading the second chart as "the first with `u` and `v`
exchanged" makes this step look trivial and gives the wrong target.

## What this does not prove

This is not the comparison of the local factorisation with the Weil coefficient at the exceptional
curve. That remains piece 3, and it identifies a coefficient with an order rather than composing two
identities, so it is a genuine theorem and is untouched here. Everything Weil-side is still blocked
upstream: no Weil-side pullback exists anywhere in the tree, and the point blowup's `normal` and
`dimension_two` are unbuilt (`integral` is accepted).
-/

noncomputable section

universe u

namespace KltDP.Examples.FrobeniusChartOverlapAgreement

open KltDP.Geometry.AffineBlowup
open KltDP.RingTheory.LocalAdicOrder
open KltDP.Examples.FrobeniusBlowupContact
open KltDP.Examples.FrobeniusBlowupSmooth
open KltDP.Examples.FrobeniusTowerSecondChart
open KltDP.Examples.FrobeniusBlowupDifferentialOverlap
open KltDP.Examples.FrobeniusChartPullbackOrder
open KltDP.Examples.FrobeniusChartOrderExact
open KltDP.Examples.FrobeniusSecondChartOrder

variable {k : Type u} [Field k]

/-! ## The exponent is forced on each chart separately -/

/-- **On the first chart the exponent is forced.** Any factorisation of the chart pullback with
cofactor prime to the exceptional coordinate has exponent the adic order — the exponent is not a
choice, and in particular `chartOrderExact`'s exponent is the only possible one. -/
theorem chartExponent_eq_centerOrder {a : ℕ} {f g : planeRing k} (hf : f ≠ 0)
    (h : chartSubstitution f = uCoord ^ a * g) (hg : ¬ (uCoord ∣ g)) :
    a = centerOrder f := by
  have hbdd := bddAbove_center f hf
  have hdvd : (uCoord (k := k)) ^ a ∣ chartSubstitution f := ⟨g, h⟩
  have hle : a ≤ centerOrder f :=
    (le_adicOrder_iff_mem hbdd a).mpr ((mem_centerIdeal_pow_iff_uCoord_pow_dvd a f).mpr hdvd)
  by_contra hne
  have hsucc : a + 1 ≤ centerOrder f := lt_of_le_of_ne hle hne
  have hmem : f ∈ centerIdeal ^ (a + 1) := (le_adicOrder_iff_mem hbdd (a + 1)).mp hsucc
  obtain ⟨c, hc⟩ := (mem_centerIdeal_pow_iff_uCoord_pow_dvd (a + 1) f).mp hmem
  have hcancel : (uCoord (k := k)) ^ a * g = uCoord ^ a * (uCoord * c) := by
    rw [← h, hc, pow_succ]
    ring
  have hupow : (uCoord (k := k)) ^ a ≠ 0 := pow_ne_zero _ uCoord_ne_zero
  exact hg ⟨c, mul_left_cancel₀ hupow hcancel⟩

/-- **On the second chart the exponent is forced**, by the same argument through the second chart's
equivalence. -/
theorem secondChartExponent_eq_centerOrder {a : ℕ} {f g : planeRing k} (hf : f ≠ 0)
    (h : secondSubstitution f = uCoord ^ a * g) (hg : ¬ (uCoord ∣ g)) :
    a = centerOrder f := by
  have hbdd := bddAbove_center f hf
  have hdvd : (uCoord (k := k)) ^ a ∣ secondSubstitution f := ⟨g, h⟩
  have hle : a ≤ centerOrder f :=
    (le_adicOrder_iff_mem hbdd a).mpr ((mem_centerIdeal_pow_iff_uCoord_pow_dvd_second a f).mpr hdvd)
  by_contra hne
  have hsucc : a + 1 ≤ centerOrder f := lt_of_le_of_ne hle hne
  have hmem : f ∈ centerIdeal ^ (a + 1) := (le_adicOrder_iff_mem hbdd (a + 1)).mp hsucc
  obtain ⟨c, hc⟩ := (mem_centerIdeal_pow_iff_uCoord_pow_dvd_second (a + 1) f).mp hmem
  have hcancel : (uCoord (k := k)) ^ a * g = uCoord ^ a * (uCoord * c) := by
    rw [← h, hc, pow_succ]
    ring
  have hupow : (uCoord (k := k)) ^ a ≠ 0 := pow_ne_zero _ uCoord_ne_zero
  exact hg ⟨c, mul_left_cancel₀ hupow hcancel⟩

/-- **The two chart orders agree.** Two factorisations produced independently on the two charts,
neither hypothesis mentioning the order, have the same exponent. -/
theorem chart_exponents_agree {a b : ℕ} {f g₁ g₂ : planeRing k} (hf : f ≠ 0)
    (h₁ : chartSubstitution f = uCoord ^ a * g₁) (hg₁ : ¬ (uCoord ∣ g₁))
    (h₂ : secondSubstitution f = uCoord ^ b * g₂) (hg₂ : ¬ (uCoord ∣ g₂)) :
    a = b :=
  (chartExponent_eq_centerOrder hf h₁ hg₁).trans
    (secondChartExponent_eq_centerOrder hf h₂ hg₂).symm

/-! ## The two polynomial models inside the accepted overlap ring -/

/-- The first chart's polynomial model, restricted to the two-chart overlap. -/
def firstChartToOverlap : planeRing k →+* overlapRing k :=
  (overlapLeft (k := k)).comp polynomialToChart

/-- The second chart's polynomial model, restricted to the same overlap. -/
def secondChartToOverlap : planeRing k →+* overlapRing k :=
  (overlapRight (k := k)).comp (vChartPolynomialEquiv (k := k)).symm.toRingHom

/-- **The first blowdown becomes the overlap's base map.** -/
theorem firstChartToOverlap_chartSubstitution (f : planeRing k) :
    firstChartToOverlap (chartSubstitution f) = overlapBaseMap f := by
  have h : polynomialToChart (chartSubstitution f) = baseMap f :=
    RingHom.congr_fun polynomialToChart_comp_substitution f
  show overlapLeft (polynomialToChart (chartSubstitution f)) = overlapBaseMap f
  rw [h]
  exact conormalOverlapLeft_baseMap (centerIdeal (k := k)) centerU centerV f

/-- **The second blowdown becomes the very same base map** — this is the sense in which the two
charts blow down compatibly, and it replaces any transition isomorphism. -/
theorem secondChartToOverlap_secondSubstitution (f : planeRing k) :
    secondChartToOverlap (secondSubstitution f) = overlapBaseMap f := by
  have hfwd : vChartPolynomialEquiv (chartBaseMap centerIdeal (centerV (k := k)) f)
      = secondSubstitution f := rfl
  have h : (vChartPolynomialEquiv (k := k)).symm (secondSubstitution f)
      = chartBaseMap centerIdeal centerV f := by
    rw [← hfwd]
    exact (vChartPolynomialEquiv (k := k)).symm_apply_apply _
  show overlapRight ((vChartPolynomialEquiv (k := k)).symm (secondSubstitution f))
      = overlapBaseMap f
  rw [h]
  exact conormalOverlapRight_baseMap (centerIdeal (k := k)) centerU centerV f

/-- The first chart's exceptional coordinate on the overlap. -/
theorem firstChartToOverlap_uCoord :
    firstChartToOverlap (uCoord (k := k)) = overlapU := by
  have h := firstChartToOverlap_chartSubstitution (uCoord (k := k))
  rw [chartSubstitution_u] at h
  exact h

/-- The second chart's exceptional coordinate on the overlap. **It is `overlapV`, not `overlapU`**:
the second chart is relabelled, so the same symbol `uCoord` names a different element there. -/
theorem secondChartToOverlap_uCoord :
    secondChartToOverlap (uCoord (k := k)) = overlapV := by
  have h := secondChartToOverlap_secondSubstitution (vCoord (k := k))
  rw [secondSubstitution_v] at h
  exact h

/-- **The two exceptional coordinates differ by the chart ratio on the overlap.** -/
theorem secondChartToOverlap_uCoord_eq :
    secondChartToOverlap (uCoord (k := k))
      = firstChartToOverlap (uCoord (k := k)) * (overlapT (k := k)) := by
  rw [firstChartToOverlap_uCoord, secondChartToOverlap_uCoord]
  exact overlapU_mul_overlapT.symm

/-- The chart ratio is a unit on the overlap. -/
theorem isUnit_overlapT : IsUnit (overlapT (k := k)) :=
  isUnit_of_mul_eq_one _ _ overlapT_mul_overlapS

/-- Hence so is each of its powers. -/
theorem isUnit_overlapT_pow (n : ℕ) : IsUnit ((overlapT (k := k)) ^ n) :=
  (isUnit_overlapT (k := k)).pow n

/-- **The first chart's exceptional coordinate is a nonzerodivisor on the overlap.** This is the
accepted `conormalOverlapEquationLeft_regular` at the plane's centre, and it is what licenses the
cancellation in the cofactor comparison. -/
theorem overlapU_mem_nonZeroDivisors :
    (overlapU (k := k)) ∈ nonZeroDivisors (overlapRing k) := by
  have h := conormalOverlapEquationLeft_regular (centerIdeal (k := k)) centerU centerV
  exact h

/-! ## The cofactors agree up to a unit -/

/-- **The comparison of the two local factorisations on the overlap.** Given exceptional
factorisations with a common exponent on the two charts, the cofactors differ by the unit
`overlapT ^ n`. No hypothesis on `f` beyond the two factorisations is used. -/
theorem cofactor_transition_of_factorizations {n : ℕ} {f g₁ g₂ : planeRing k}
    (h₁ : chartSubstitution f = uCoord ^ n * g₁)
    (h₂ : secondSubstitution f = uCoord ^ n * g₂) :
    firstChartToOverlap g₁ = (overlapT (k := k)) ^ n * secondChartToOverlap g₂ := by
  have e₁ : overlapBaseMap f = (overlapU (k := k)) ^ n * firstChartToOverlap g₁ := by
    have hb := firstChartToOverlap_chartSubstitution f
    rw [h₁] at hb
    rw [map_mul, map_pow, firstChartToOverlap_uCoord] at hb
    exact hb.symm
  have e₂ : overlapBaseMap f = (overlapV (k := k)) ^ n * secondChartToOverlap g₂ := by
    have hb := secondChartToOverlap_secondSubstitution f
    rw [h₂] at hb
    rw [map_mul, map_pow, secondChartToOverlap_uCoord] at hb
    exact hb.symm
  have hV : (overlapV (k := k)) ^ n
      = (overlapU (k := k)) ^ n * (overlapT (k := k)) ^ n := by
    rw [← mul_pow, overlapU_mul_overlapT]
  have hcancel : (overlapU (k := k)) ^ n * firstChartToOverlap g₁
      = (overlapU (k := k)) ^ n
        * ((overlapT (k := k)) ^ n * secondChartToOverlap g₂) := by
    rw [← e₁, e₂, hV, mul_assoc]
  exact (mul_cancel_left_mem_nonZeroDivisors
    (Submonoid.pow_mem _ (overlapU_mem_nonZeroDivisors (k := k)) n)).mp hcancel

/-- The same comparison packaged as associatedness in the overlap ring. -/
theorem associated_cofactors_overlap {n : ℕ} {f g₁ g₂ : planeRing k}
    (h₁ : chartSubstitution f = uCoord ^ n * g₁)
    (h₂ : secondSubstitution f = uCoord ^ n * g₂) :
    Associated (secondChartToOverlap g₂) (firstChartToOverlap g₁) := by
  have hu : IsUnit ((overlapT (k := k)) ^ n) := isUnit_overlapT_pow n
  refine ⟨hu.unit, ?_⟩
  have hspec : ((hu.unit : (overlapRing k)ˣ) : overlapRing k)
      = (overlapT (k := k)) ^ n := hu.unit_spec
  rw [hspec, cofactor_transition_of_factorizations h₁ h₂]
  exact mul_comm _ _

/-! ## The agreement at the order itself -/

/-- **The two chart factorisations at the adic order agree on the overlap.** Both charts remove
`centerOrder f` exceptional factors; the cofactors they leave — the strict transform's equations in
the two coordinate systems — differ by the unit `overlapT ^ centerOrder f`. -/
theorem exists_factorizations_overlap_agreement (f : planeRing k) (hf : f ≠ 0) :
    ∃ g₁ g₂ : planeRing k,
      chartSubstitution f = uCoord ^ centerOrder f * g₁ ∧ ¬ (uCoord ∣ g₁) ∧
      secondSubstitution f = uCoord ^ centerOrder f * g₂ ∧ ¬ (uCoord ∣ g₂) ∧
      firstChartToOverlap g₁
        = (overlapT (k := k)) ^ centerOrder f * secondChartToOverlap g₂ ∧
      Associated (secondChartToOverlap g₂) (firstChartToOverlap g₁) := by
  obtain ⟨g₁, h₁, hn₁⟩ := chartOrderExact f hf
  obtain ⟨g₂, h₂, hn₂⟩ := secondChartOrderExact f hf
  exact ⟨g₁, g₂, h₁, hn₁, h₂, hn₂, cofactor_transition_of_factorizations h₁ h₂,
    associated_cofactors_overlap h₁ h₂⟩

end KltDP.Examples.FrobeniusChartOverlapAgreement

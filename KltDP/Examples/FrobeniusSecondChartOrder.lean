import KltDP.Examples.FrobeniusChartContactOrder
import KltDP.Examples.FrobeniusTowerSecondChart
import KltDP.Examples.FrobeniusBlowupSmooth
import KltDP.Examples.FrobeniusStageOneEmbedding

/-!
# The order of vanishing on the second Rees chart

BRIEF46, the first of the three pieces of globalisation. The second chart's blowdown carries the same
contact order as the first: for every nonzero `f` in the polynomial plane,

`ς^*f = u^(ord f) · g`  with `u ∤ g`,

where `ς = secondSubstitution` and `ord` is the **same** `centerOrder` — the adic order at the centre of
the plane, which is chart-independent by construction.

## The obligation moved, and the reduction

Two things were already accepted and neither was rebuilt:

* **`secondSubstitution` exists** (`FrobeniusTowerSecondChart`), with `u ↦ u·v`, `v ↦ u`. Note the
  relabelling: the exceptional coordinate on the second chart is `uCoord` **again**, not `vCoord`, so this
  statement is parallel to the first chart's rather than a mirror image of it.
* **`coordinateSwap`** (`FrobeniusBlowupSmooth`) is the coordinate exchange, and
  `coordinateSwap_center` already proves it fixes the centre ideal.

Those two collapse the task. On generators, `secondSubstitution = chartSubstitution ∘ coordinateSwap`
(`secondSubstitution_comp_swap`, by a nested `Polynomial.ringHom_ext`), and the swap preserves membership
in every power of the centre (`coordinateSwap_mem_centerIdeal_pow_iff`, from `coordinateSwap_center` and
its `symm` companion). So the queued first-chart equivalence transports verbatim:

`f ∈ centerIdeal ^ n ↔ uCoord ^ n ∣ secondSubstitution f`.

**No coefficient computation is repeated.** A direct proof on this chart would need the convolution
`(ς^*f).coeff d = Σ_{a+j=d} …`, because `u ↦ u·v` is not coefficientwise — the first chart's
`coeff_chartSubstitution` has no analogue here. Conjugating by the swap avoids it entirely.

## The contact family

`secondSubstitution (v - u^(m+1)) = u · (1 - u^m·v^(m+1))`, whose cofactor is prime to `u` (its constant
term is `1`). With `centerOrder (v - u^(m+1)) = 1` from `FrobeniusChartContactOrder`, the second chart
therefore removes **exactly one** exceptional factor from the contact equation — the same number as the
first chart, where the cofactor is the residual equation `v - u^m`. The two cofactors differ, as they must,
being the strict transform's equations in two different coordinate systems; the exponents agree.

## What this is NOT

This is the second chart's order **alone**. It does **not** prove the agreement of the two chart orders on
the overlap: that the exponents coincide here is proved for this one family by computing both, not in
general, and a general statement needs the overlap ring and the transition map. Nor does it touch the
comparison of the local factorisation with the Weil coefficient at the exceptional curve, which identifies
a coefficient with an order and is a genuine theorem rather than a composition. Both remain open, as does
everything Weil-side (no Weil pullback exists in the tree; the point blowup's `normal` and `dimension_two`
are unbuilt).
-/

noncomputable section

universe u

namespace KltDP.Examples.FrobeniusSecondChartOrder

open KltDP.RingTheory.LocalAdicOrder
open KltDP.Examples.FrobeniusBlowupContact
open KltDP.Examples.FrobeniusBlowupSmooth
open KltDP.Examples.FrobeniusTowerSecondChart
open KltDP.Examples.FrobeniusChartPullbackOrder
open KltDP.Examples.FrobeniusChartOrderExact
open KltDP.Examples.FrobeniusChartContactOrder

variable {k : Type u} [Field k]

/-! ## The inverse coordinate swap -/

theorem coordinateSwap_symm_u : (coordinateSwap (k := k)).symm uCoord = vCoord :=
  (coordinateSwap (k := k)).symm_apply_eq.mpr coordinateSwap_v.symm

theorem coordinateSwap_symm_v : (coordinateSwap (k := k)).symm vCoord = uCoord :=
  (coordinateSwap (k := k)).symm_apply_eq.mpr coordinateSwap_u.symm

/-- The inverse swap fixes the centre, exactly as the accepted `coordinateSwap_center` does. -/
theorem coordinateSwap_symm_center :
    Ideal.map (coordinateSwap (k := k)).symm.toRingHom centerIdeal = centerIdeal := by
  rw [centerIdeal, Ideal.map_span, Set.image_pair]
  change Ideal.span {(coordinateSwap (k := k)).symm uCoord, (coordinateSwap (k := k)).symm vCoord}
      = Ideal.span {uCoord, vCoord}
  rw [coordinateSwap_symm_u, coordinateSwap_symm_v, Ideal.span_pair_comm]

/-- **The swap preserves membership in every power of the centre.** -/
theorem coordinateSwap_mem_centerIdeal_pow_iff (n : ℕ) (f : planeRing k) :
    coordinateSwap f ∈ centerIdeal ^ n ↔ f ∈ centerIdeal ^ n := by
  have hfwd : Ideal.map (coordinateSwap (k := k)).toRingHom (centerIdeal ^ n)
      = centerIdeal ^ n := by
    rw [Ideal.map_pow, coordinateSwap_center]
  have hbwd : Ideal.map (coordinateSwap (k := k)).symm.toRingHom (centerIdeal ^ n)
      = centerIdeal ^ n := by
    rw [Ideal.map_pow, coordinateSwap_symm_center]
  constructor
  · intro h
    have hmem := Ideal.mem_map_of_mem (coordinateSwap (k := k)).symm.toRingHom h
    rw [hbwd] at hmem
    change (coordinateSwap (k := k)).symm (coordinateSwap f) ∈ centerIdeal ^ n at hmem
    rwa [AlgEquiv.symm_apply_apply] at hmem
  · intro h
    have hmem := Ideal.mem_map_of_mem (coordinateSwap (k := k)).toRingHom h
    rw [hfwd] at hmem
    exact hmem

/-! ## The second chart is the first one conjugated by the swap -/

/-- **`secondSubstitution = chartSubstitution ∘ coordinateSwap`.** -/
theorem secondSubstitution_comp_swap :
    secondSubstitution (k := k)
      = chartSubstitution.comp (coordinateSwap (k := k)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    have hcomp : (secondSubstitution (k := k)).comp Polynomial.C
        = (chartSubstitution.comp (coordinateSwap (k := k)).toRingHom).comp Polynomial.C := by
      apply Polynomial.ringHom_ext
      · intro r
        show secondSubstitution (planeConstants r)
            = chartSubstitution (coordinateSwap (planeConstants r))
        rw [KltDP.Examples.FrobeniusStageOneEmbedding.secondSubstitution_constants,
          coordinateSwap_constants]
        exact (chartSubstitution_C (Polynomial.C r)).symm
      · show secondSubstitution (uCoord (k := k)) = chartSubstitution (coordinateSwap uCoord)
        rw [secondSubstitution_u, coordinateSwap_u, chartSubstitution_v]
    exact RingHom.congr_fun hcomp a
  · show secondSubstitution (vCoord (k := k)) = chartSubstitution (coordinateSwap vCoord)
    rw [secondSubstitution_v, coordinateSwap_v, chartSubstitution_u]

theorem secondSubstitution_eq_chartSubstitution_swap (f : planeRing k) :
    secondSubstitution f = chartSubstitution (coordinateSwap f) :=
  RingHom.congr_fun secondSubstitution_comp_swap f

/-! ## The order on the second chart -/

/-- **Membership in a power of the centre is exactly divisibility of the second chart's pullback.** -/
theorem mem_centerIdeal_pow_iff_uCoord_pow_dvd_second (n : ℕ) (f : planeRing k) :
    f ∈ centerIdeal ^ n ↔ uCoord ^ n ∣ secondSubstitution f := by
  rw [secondSubstitution_eq_chartSubstitution_swap]
  exact ((coordinateSwap_mem_centerIdeal_pow_iff n f).symm).trans
    (mem_centerIdeal_pow_iff_uCoord_pow_dvd n (coordinateSwap f))

/-- The exceptional coordinate divides the second chart's pullback to the order of the curve. -/
theorem uCoord_pow_centerOrder_dvd_secondSubstitution (f : planeRing k) (hf : f ≠ 0) :
    uCoord ^ centerOrder f ∣ secondSubstitution f :=
  (mem_centerIdeal_pow_iff_uCoord_pow_dvd_second _ f).mp
    (mem_pow_adicOrder (bddAbove_center f hf))

/-- **Exactness on the second chart**: the pullback factors as `u^(ord f)` times something prime to `u`. -/
theorem secondChartOrderExact (f : planeRing k) (hf : f ≠ 0) :
    ∃ g : planeRing k, secondSubstitution f = uCoord ^ centerOrder f * g ∧ ¬ (uCoord ∣ g) := by
  obtain ⟨g, hg⟩ := uCoord_pow_centerOrder_dvd_secondSubstitution f hf
  refine ⟨g, hg, ?_⟩
  rintro ⟨c, rfl⟩
  have hdvd : uCoord ^ (centerOrder f + 1) ∣ secondSubstitution f := by
    refine ⟨c, ?_⟩
    rw [hg, pow_succ]
    ring
  exact not_mem_pow_succ (bddAbove_center f hf)
    ((mem_centerIdeal_pow_iff_uCoord_pow_dvd_second (centerOrder f + 1) f).mpr hdvd)

/-! ## The contact family on the second chart -/

/-- The second chart's pullback of the contact equation. -/
theorem secondSubstitution_firstEquationPoly (m : ℕ) :
    secondSubstitution (vCoord - uCoord ^ (m + 1) : planeRing k)
      = uCoord * (1 - uCoord ^ m * vCoord ^ (m + 1)) := by
  rw [map_sub, map_pow, secondSubstitution_u, secondSubstitution_v, mul_pow, pow_succ']
  ring

/-- The cofactor has constant term `1`. -/
theorem coeff_zero_secondCofactor (m : ℕ) :
    (1 - uCoord ^ m * vCoord ^ (m + 1) : planeRing k).coeff 0 = 1 := by
  have hu : (uCoord (k := k)) ^ m = Polynomial.C (Polynomial.X ^ m) := by
    show (Polynomial.C Polynomial.X : planeRing k) ^ m = _
    rw [← Polynomial.C_pow]
  have hv : ((vCoord (k := k)) ^ (m + 1)).coeff 0 = 0 := by
    show ((Polynomial.X : planeRing k) ^ (m + 1)).coeff 0 = 0
    rw [Polynomial.coeff_X_pow]
    exact if_neg (by omega)
  rw [Polynomial.coeff_sub, hu, Polynomial.coeff_C_mul, hv, Polynomial.coeff_one]
  simp

/-- **The second chart's cofactor is prime to the exceptional coordinate.** -/
theorem not_uCoord_dvd_secondCofactor (m : ℕ) :
    ¬ (uCoord ∣ (1 - uCoord ^ m * vCoord ^ (m + 1) : planeRing k)) := by
  intro hdvd
  have hpow : (uCoord (k := k)) ^ 1 ∣ (1 - uCoord ^ m * vCoord ^ (m + 1) : planeRing k) := by
    rwa [pow_one]
  have hcoeff := (uCoord_pow_dvd_iff 1 _).mp hpow 0
  rw [coeff_zero_secondCofactor, pow_one] at hcoeff
  exact Polynomial.not_isUnit_X (isUnit_of_dvd_one hcoeff)

/-- **The second chart removes exactly one exceptional factor from the contact equation** — the same
exponent as the first chart, where the cofactor is instead the residual equation `v - u^m`. -/
theorem secondChartOrder_firstEquationPoly (m : ℕ) :
    secondSubstitution (vCoord - uCoord ^ (m + 1) : planeRing k)
        = uCoord ^ centerOrder (vCoord - uCoord ^ (m + 1) : planeRing k)
          * (1 - uCoord ^ m * vCoord ^ (m + 1))
      ∧ ¬ (uCoord ∣ (1 - uCoord ^ m * vCoord ^ (m + 1) : planeRing k)) := by
  refine ⟨?_, not_uCoord_dvd_secondCofactor m⟩
  rw [centerOrder_firstEquationPoly, pow_one]
  exact secondSubstitution_firstEquationPoly m

end KltDP.Examples.FrobeniusSecondChartOrder

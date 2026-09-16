import KltDP.Examples.FrobeniusTowerGraphCases

/-!
# The centre-complement case of the graph identity

Part of item 3 of BRIEF38: the third piece of the three-piece cover. Over the complement of the
current centre the blowdown is an isomorphism, so both sides of `π^*Γ = B̃ + Σ_j E_j^tot` are the
transports of their stage-`n` counterparts.

* `totalGraphIdeal_puncture` is the graph analogue of the accepted `totalFiberIdeal_puncture`; the
  accepted proof is generic in the regular chart, so the supporting lemmas
  (`image_puncture_le_preimage`, `image_puncture_le_preimage_step`, `stepProjection_appLE_eq_appIso`)
  are reused unchanged.
* `graphTowerRHS_puncture` is the analogue of the accepted `towerRHS_puncture`: the exceptional
  factors transport by the accepted `oldIdealAt_birth_transport` / `oldIdealAt_step_transport` /
  `stepExceptionalIdeal_puncture` (all curve-independent), and the strict-graph factor transports by
  `strictIdeal_puncture_transport` of `FrobeniusGraphStrictCartier`.
* `graph_puncture_case` combines them with the induction hypothesis, generically in a chosen
  regular chart `c` of the graph divisor on the base (the chart is supplied by the caller, which is
  what lets the cover of stage `n+1` be indexed by charts that actually exist).

The index convention is the accepted one: stage `n+1` carries residual exponent `m + (n+1)` and
stage `n` carries `(m+1) + n`, which are the same total exponent.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusTowerGraphPuncture

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
open FrobeniusGlobalStrictTransform
open FrobeniusExceptionalCartier
open FrobeniusGraphPicardClassIntegral
open FrobeniusGraphZeroCartier FrobeniusGraphStrictCartier
open FrobeniusFiberStrictCartier
open FrobeniusStrictTransformStepPuncture
open FrobeniusTowerFiberPullback FrobeniusTowerCartierIdentity
open FrobeniusTowerGraphPullback FrobeniusTowerGraphCases

variable {k : Type u} [Field k]

local instance graphPunctureProductIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

local instance graphPunctureInitialIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  projectiveProduct_isIntegral

set_option maxHeartbeats 4000000 in
/-- Over the centre complement the ideal of the total transform of the graph on stage `n+1` is the
transport of the one on stage `n`. -/
theorem totalGraphIdeal_puncture (n p : ℕ)
    (c : RegularCartierEquationChart (projectiveContactStage (k := k) 0) (graphZeroDivisor p))
    (W₀ : (nextPuncture (k := k) n).toScheme.affineOpens) [Nonempty W₀.1]
    (hW : (nextPuncture n).ι ''ᵁ W₀.1 ≤
      between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1)) ⁻¹ᵁ c.chart.openSet) :
    (totalGraphIdeal (n + 1) p).ideal
        ⟨(nextPuncture n).ι ''ᵁ W₀.1, W₀.2.image_of_isOpenImmersion _⟩ =
      ((totalGraphIdeal n p).ideal ⟨(currentPuncture n).ι ''ᵁ (punctureIso n ''ᵁ W₀.1),
          (W₀.2.image_of_isOpenImmersion (punctureIso n)).image_of_isOpenImmersion _⟩).map
        ((punctureIso n).appIso W₀.1).hom.hom := by
  haveI : Nonempty ((currentPuncture (k := k) n).ι ''ᵁ (punctureIso n ''ᵁ W₀.1)) := by
    obtain ⟨⟨w, hw⟩⟩ := (inferInstance : Nonempty W₀.1)
    exact ⟨⟨_, ⟨_, ⟨w, hw, rfl⟩, rfl⟩⟩⟩
  haveI : Nonempty ((nextPuncture (k := k) n).ι ''ᵁ W₀.1) := by
    obtain ⟨⟨w, hw⟩⟩ := (inferInstance : Nonempty W₀.1)
    exact ⟨⟨_, ⟨w, hw, rfl⟩⟩⟩
  rw [totalGraphIdeal_ideal (n + 1) p c _ hW,
    totalGraphIdeal_ideal n p c _ (image_puncture_le_preimage n W₀.1 _ hW), Ideal.map_span,
    Set.image_singleton,
    appLE_congr_hom (between_succ (projectiveProductInitial (k := k)) (Nat.zero_le n)),
    ← Scheme.appLE_comp_appLE _ _ _ _ _ (image_puncture_le_preimage n W₀.1 _ hW)
      (image_puncture_le_preimage_step n W₀.1),
    CommRingCat.comp_apply, stepProjection_appLE_eq_appIso]
  rfl

set_option maxHeartbeats 4000000 in
/-- The right-hand side transports over the centre complement in the same way. -/
theorem graphTowerRHS_puncture (n m : ℕ) (W₀ : (nextPuncture (k := k) n).toScheme.affineOpens) :
    (graphTowerRHS (n + 1) m).ideal
        ⟨(nextPuncture n).ι ''ᵁ W₀.1, W₀.2.image_of_isOpenImmersion _⟩ =
      ((graphTowerRHS n (m + 1)).ideal ⟨(currentPuncture n).ι ''ᵁ (punctureIso n ''ᵁ W₀.1),
          (W₀.2.image_of_isOpenImmersion (punctureIso n)).image_of_isOpenImmersion _⟩).map
        ((punctureIso n).appIso W₀.1).hom.hom := by
  show (strictTransformIdeal (k := k) (n + 1) (m + (n + 1))).ideal _ *
      (idealSheafDataFinProd (fun j => idealSheafDataPow (oldIdealAt (n + 1) j) (j + 1)) n).ideal _ *
      (idealSheafDataPow (stepExceptionalIdeal n) (n + 1)).ideal _ = _
  rw [idealSheafDataPow_ideal,
    stepExceptionalIdeal_puncture n ⟨(nextPuncture n).ι ''ᵁ W₀.1, W₀.2.image_of_isOpenImmersion _⟩
      (image_le_nextPuncture n W₀.1),
    Ideal.span_singleton_one, Ideal.top_pow, Ideal.mul_top,
    strictIdeal_puncture_transport n m W₀, Ideal.comap_inv_eq_map_hom]
  cases n with
  | zero =>
    show Ideal.map _ _ * (⊤ : Ideal _) =
      Ideal.map _ ((strictTransformIdeal (k := k) 0 ((m + 1) + 0)).ideal _)
    rw [Ideal.mul_top]
  | succ q =>
    show Ideal.map _ _ *
        ((idealSheafDataFinProd
            (fun j => idealSheafDataPow (oldIdealAt (q + 1 + 1) j) (j + 1)) q).ideal _ *
          (idealSheafDataPow (oldIdealAt (q + 1 + 1) q) (q + 1)).ideal _) =
      Ideal.map _ ((strictTransformIdeal (k := k) (q + 1) ((m + 1) + (q + 1))).ideal _ *
        (idealSheafDataFinProd (fun j => idealSheafDataPow (oldIdealAt (q + 1) j) (j + 1)) q).ideal _ *
        (idealSheafDataPow (stepExceptionalIdeal q) (q + 1)).ideal _)
    rw [Ideal.map_mul, Ideal.map_mul, idealSheafDataPow_ideal, idealSheafDataPow_ideal,
      Ideal.map_pow, oldIdealAt_birth_transport q W₀, mul_assoc]
    congr 2
    exact idealSheafDataFinProd_ideal_map _ _ _ _ _ q (fun j hj => by
      rw [idealSheafDataPow_ideal, idealSheafDataPow_ideal, Ideal.map_pow,
        oldIdealAt_step_transport q j hj W₀])

set_option maxHeartbeats 4000000 in
/-- **The centre-complement case of the graph identity.** -/
theorem graph_puncture_case (n m : ℕ)
    (c : RegularCartierEquationChart (projectiveContactStage (k := k) 0)
      (graphZeroDivisor (m + (n + 1))))
    (ih : totalGraphIdeal (k := k) n (m + (n + 1)) = graphTowerRHS n (m + 1))
    (W : (projectiveContactStage (k := k) (n + 1)).affineOpens)
    (hW : W.1 ≤ nextPuncture n ⊓
      between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1)) ⁻¹ᵁ c.chart.openSet) :
    (totalGraphIdeal (n + 1) (m + (n + 1))).ideal W = (graphTowerRHS (n + 1) m).ideal W := by
  refine IdealSheafData.ideal_eq_of_image' (nextPuncture n) _ _ _ (fun W₀ hW₀ => ?_) W hW
  refine IdealSheafData.ideal_eq_of_nonempty _ _ _ (fun hne => ?_)
  obtain ⟨⟨_, ⟨w, hw, rfl⟩⟩⟩ := hne
  haveI : Nonempty W₀.1 := ⟨⟨w, hw⟩⟩
  rw [graphTowerRHS_puncture n m W₀, ← ih]
  exact totalGraphIdeal_puncture n (m + (n + 1)) c W₀ hW₀

end KltDP.Examples.FrobeniusTowerGraphPuncture

import KltDP.Examples.FrobeniusTowerFiberPullback

/-!
# The Cartier-level identity `π^*(y = 0) = F̃ + Σ_j (j+1)·C_j + (N+1)·P` on the origin contact tower

On stage `N+1` of the origin contact tower, the total transform `totalFiberDivisor (N+1)` of the
fibre `y = 0` (BRIEF19, `FrobeniusTowerFiberPullback`) equals, as an effective Cartier divisor,
`fiberStrictDivisor (N+1) + Σ_{j<N} (j+1) • oldFinalDivisor (N+1) j + (N+1) • stepExceptionalDivisor N`
(`totalFiberDivisor_eq`, exported as `f29_tower_fiber_relation`), and hence the Picard relation
holds between the classes of these divisors (`totalFiberDivisor_picard`).

Route: by the generic `cartierDivisorOfIdeal_tower` and the uniqueness `eq_cartierDivisorOfIdeal`,
the identity reduces to the identity of ideal-sheaf data
`totalFiberIdeal (N+1) = F̃ · Π_{j<N} C_j^{j+1} · P^{N+1}` (`totalFiberIdeal_eq`, with `towerRHS`),
proved by induction over the stages and locality on affine opens
(`IdealSheafData.ext_of_affine_cover`) for the cover of stage `n+1` by the selected chart open, the
second Rees open of the last blowup, and the pieces of the centre complement lying over the four
product charts of `P¹ × P¹`: on the two chart opens all ideals are principal with the generators
`u^{n+1} v`, `v`, `u`, `1` resp. `(u/v)^n v^{n+1}`, `1`, `v'`, `u/v`, `1` computed from the
accepted chart-ideal lemmas and the chart squares; over the centre complement every ideal is the
transport of the corresponding stage-`n` ideal along the restricted blowdown (the strict fibre and
the birth of `C_{n-1}` from `P_n` through lane A2's pullback squares, the earlier `C_j` through the
one-step pullback square `oldFinalMap_step_isPullback` pasted from the accepted
`finalOldMap_isPullback`, and `P_{n+1}` misses the complement), so the identity follows from the
induction hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusTowerCartierIdentity

open KltDP.Geometry
open FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
  FrobeniusStrictTransformStepPuncture FrobeniusStrictTransformInvertible
  FrobeniusStrictTransformSecondChartFrame FrobeniusStrictTransformSecondChart
  FrobeniusFiberTotalProduct FrobeniusStrictTransformFirstChartTensorFrame
  FrobeniusStrictTransformSecondChartTensorFrame FrobeniusOldExceptionalSecondChartFrame
  FrobeniusExceptionalSuccessorChart FrobeniusBlowupChartIteration
  FrobeniusGraphPicardClassCharts FrobeniusGraphPicardClassMixedCoordinates
  FrobeniusFiberZeroClass FrobeniusFiberZeroInvertible FrobeniusFiberStrictCartier
  FrobeniusExceptionalCartier FrobeniusOldExceptionalLaterCartier
  FrobeniusOldExceptionalBirthCartier FrobeniusOldExceptionalLaterStages
  FrobeniusOldExceptionalChartIdeals FrobeniusExceptionalLaterStages
  FrobeniusTowerFunctionField FrobeniusGraphPicardClassIntegral FrobeniusProductPlaneChart
  FrobeniusBlowupContact KltDP.Geometry.AffineBlowup FrobeniusExceptionalCharts
  FrobeniusBlowupSmooth FrobeniusTowerFiberPullback FrobeniusFiberPicard FrobeniusStrictTransformProductCover
  FrobeniusStrictTransformProductKernel

variable {k : Type u} [Field k]

local instance initialIntegral : IsIntegral (projectiveProductInitial (k := k)).carrier :=
  projectiveProduct_isIntegral

/-! ## One-step transport of the old exceptional curves over the centre complement -/

/-- The one-step square of `C_j` (for `j + 2 ≤ N`) is a pullback, by pasting the accepted global
pullback squares `finalOldMap_isPullback` of stages `N+1` and `N`. -/
theorem oldFinalMap_step_isPullback (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    IsPullback (oldFinalMap (k := k) (N + 1) j (by omega)) (𝟙 _)
      ((projectiveProductInitial (k := k)).stepProjection N) (oldFinalMap N j h) := by
  have hs : IsPullback (oldFinalMap (k := k) (N + 1) j (by omega)) (𝟙 _ ≫ 𝟙 _)
      ((projectiveProductInitial (k := k)).stepProjection N ≫ oldBetween N j h)
      (oldExceptionalStrictι j) := by
    have := finalOldMap_isPullback (projectiveProductInitial (k := k)) (N + 1) j (by omega)
    rw [Category.id_comp, ← between_succ (projectiveProductInitial (k := k)) h]
    exact this
  refine IsPullback.of_bot hs ?_ (finalOldMap_isPullback (projectiveProductInitial (k := k)) N j h)
  rw [Category.id_comp, ← between_step (projectiveProductInitial (k := k)) N]
  exact finalOldMap_between (projectiveProductInitial (k := k)) h (Nat.le_succ N)

theorem oldFinalIdeal_step_transport (N j : ℕ) (h : j + 1 + 1 ≤ N)
    (W₀ : (nextPuncture (k := k) N).toScheme.affineOpens) :
    (oldFinalIdeal (k := k) (N + 1) j (by omega)).ideal
        ⟨(nextPuncture N).ι ''ᵁ W₀.1, W₀.2.image_of_isOpenImmersion _⟩ =
      ((oldFinalIdeal N j h).ideal ⟨(currentPuncture N).ι ''ᵁ (punctureIso N ''ᵁ W₀.1),
          (W₀.2.image_of_isOpenImmersion (punctureIso N)).image_of_isOpenImmersion _⟩).map
        ((punctureIso N).appIso W₀.1).hom.hom := by
  rw [← Ideal.comap_inv_eq_map_hom]
  exact ker_ideal_of_isPullback_id_restrict _ _ _ (oldFinalMap_step_isPullback N j h)
    (currentPuncture N) W₀

/-- On its birth stage `C_j` is the strict transform `oldExceptionalStrictι j`. -/
theorem oldFinalIdeal_birth (m : ℕ) :
    oldFinalIdeal (k := k) (m + 1 + 1) m (le_refl _) = oldStrictIdeal m :=
  congrArg Scheme.Hom.ker (finalOldMap_birth (projectiveProductInitial (k := k)) m)

/-- The ideal sheaf of `C_j` on stage `N` for every `j` (the unit ideal when `C_j` is not yet
born). -/
def oldIdealAt (N j : ℕ) : (projectiveContactStage (k := k) N).IdealSheafData :=
  if h : j + 1 + 1 ≤ N then oldFinalIdeal N j h else ⊤

theorem oldIdealAt_of_le (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    oldIdealAt (k := k) N j = oldFinalIdeal N j h := dif_pos h

theorem oldIdealAt_locallyPrincipalRegular (N j : ℕ) :
    IdealLocallyPrincipalRegular (oldIdealAt (k := k) N j) := by
  unfold oldIdealAt
  split_ifs with h
  · exact oldFinalIdeal_locallyPrincipalRegular N j h
  · exact top_locallyPrincipalRegular _

theorem oldIdealAt_birth_transport (m : ℕ)
    (W₀ : (nextPuncture (k := k) (m + 1)).toScheme.affineOpens) :
    (oldIdealAt (k := k) (m + 1 + 1) m).ideal
        ⟨(nextPuncture (m + 1)).ι ''ᵁ W₀.1, W₀.2.image_of_isOpenImmersion _⟩ =
      ((stepExceptionalIdeal m).ideal
          ⟨(currentPuncture (m + 1)).ι ''ᵁ (punctureIso (m + 1) ''ᵁ W₀.1),
            (W₀.2.image_of_isOpenImmersion (punctureIso (m + 1))).image_of_isOpenImmersion _⟩).map
        ((punctureIso (m + 1)).appIso W₀.1).hom.hom := by
  rw [oldIdealAt_of_le (m + 1 + 1) m (le_refl _), oldFinalIdeal_birth, ← Ideal.comap_inv_eq_map_hom]
  exact oldStrictIdeal_puncture_transport m W₀

theorem oldIdealAt_step_transport (m j : ℕ) (hj : j < m)
    (W₀ : (nextPuncture (k := k) (m + 1)).toScheme.affineOpens) :
    (oldIdealAt (k := k) (m + 1 + 1) j).ideal
        ⟨(nextPuncture (m + 1)).ι ''ᵁ W₀.1, W₀.2.image_of_isOpenImmersion _⟩ =
      ((oldIdealAt (m + 1) j).ideal
          ⟨(currentPuncture (m + 1)).ι ''ᵁ (punctureIso (m + 1) ''ᵁ W₀.1),
            (W₀.2.image_of_isOpenImmersion (punctureIso (m + 1))).image_of_isOpenImmersion _⟩).map
        ((punctureIso (m + 1)).appIso W₀.1).hom.hom := by
  rw [oldIdealAt_of_le (m + 1 + 1) j (by omega), oldIdealAt_of_le (m + 1) j (by omega)]
  exact oldFinalIdeal_step_transport (m + 1) j (by omega) W₀

/-! ## The old exceptional curves miss the two chart opens of the last blowup -/

theorem oldFinalIdeal_first (N j : ℕ) (h : j + 1 + 1 ≤ N)
    (W : (projectiveContactStage (k := k) N).affineOpens) (hW : W.1 ≤ (firstAffineOpen N).1) :
    (oldFinalIdeal (k := k) N j h).ideal W = Ideal.span {1} := by
  apply ker_ideal_eq_top_of_preimage_eq_bot
  apply Opens.ext
  rw [Opens.coe_bot]
  apply Set.eq_empty_of_forall_not_mem
  intro z hz
  obtain ⟨y, -, hy⟩ := hW hz
  exact finalOldMap_avoids_chart (projectiveProductInitial (k := k)) N j h z ⟨y, hy⟩

theorem oldFinalIdeal_second (n j : ℕ) (h : j + 1 + 1 ≤ n)
    (W : (projectiveContactStage (k := k) (n + 1)).affineOpens)
    (hW : W.1 ≤ (secondAffineOpen n).1) :
    (oldFinalIdeal (k := k) (n + 1) j (by omega)).ideal W = Ideal.span {1} := by
  apply ker_ideal_eq_top_of_preimage_eq_bot
  apply Opens.ext
  rw [Opens.coe_bot]
  apply Set.eq_empty_of_forall_not_mem
  intro z hz
  have h2 := secondAffineOpen_le_preimage_first n (hW hz)
  have h3 : ((projectiveProductInitial (k := k)).stepProjection n).base
      ((oldFinalMap (n + 1) j (by omega)).base z) = (oldFinalMap n j h).base z := by
    rw [← TopCat.comp_app, ← Scheme.comp_base, ← between_step (projectiveProductInitial (k := k)) n,
      finalOldMap_between (projectiveProductInitial (k := k)) h (Nat.le_succ n)]
  have h2' : ((projectiveProductInitial (k := k)).stepProjection n).base
      ((oldFinalMap (n + 1) j (by omega)).base z) ∈ (firstAffineOpen n).1 := h2
  rw [h3] at h2'
  obtain ⟨y, -, hy⟩ := h2'
  exact finalOldMap_avoids_chart (projectiveProductInitial (k := k)) n j h z ⟨y, hy⟩

/-! ## Finite products of ideal sheaves on an affine open -/

theorem idealSheafDataFinProd_ideal_eq_top {X : Scheme.{u}} (J : ℕ → X.IdealSheafData)
    (W : X.affineOpens) :
    ∀ q : ℕ, (∀ j < q, (J j).ideal W = ⊤) → (idealSheafDataFinProd J q).ideal W = ⊤
  | 0, _ => rfl
  | q + 1, h => by
    show (idealSheafDataFinProd J q).ideal W * (J q).ideal W = ⊤
    rw [idealSheafDataFinProd_ideal_eq_top J W q (fun j hj => h j (by omega)), h q (by omega),
      Ideal.mul_top]

theorem idealSheafDataFinProd_ideal_map {X Y : Scheme.{u}} (J : ℕ → X.IdealSheafData)
    (J' : ℕ → Y.IdealSheafData) (W : X.affineOpens) (W' : Y.affineOpens)
    (φ : Γ(X, W.1) →+* Γ(Y, W'.1)) :
    ∀ q : ℕ, (∀ j < q, (J' j).ideal W' = ((J j).ideal W).map φ) →
      (idealSheafDataFinProd J' q).ideal W' = ((idealSheafDataFinProd J q).ideal W).map φ
  | 0, _ => by
    show (⊤ : Ideal _) = Ideal.map φ ⊤
    rw [Ideal.map_top]
  | q + 1, h => by
    show (idealSheafDataFinProd J' q).ideal W' * (J' q).ideal W' =
      ((idealSheafDataFinProd J q).ideal W * (J q).ideal W).map φ
    rw [Ideal.map_mul, idealSheafDataFinProd_ideal_map J J' W W' φ q (fun j hj => h j (by omega)),
      h q (by omega)]

/-! ## The right-hand side `F̃ · Π_j C_j^{j+1} · P^{n+1}` and its transport -/

/-- The ideal sheaf `F̃_n · Π_{j<n-1} C_j^{j+1} · P_n^n` on stage `n` (`F̃_0` on stage `0`). -/
def towerRHS : (n : ℕ) → (projectiveContactStage (k := k) n).IdealSheafData
  | 0 => fiberStrictIdeal 0
  | n + 1 => idealSheafDataMul (idealSheafDataMul (fiberStrictIdeal (n + 1))
      (idealSheafDataFinProd (fun j => idealSheafDataPow (oldIdealAt (n + 1) j) (j + 1)) n))
      (idealSheafDataPow (stepExceptionalIdeal n) (n + 1))

theorem image_le_nextPuncture (n : ℕ) (W₀ : (nextPuncture (k := k) n).toScheme.Opens) :
    (nextPuncture n).ι ''ᵁ W₀ ≤ nextPuncture n := by
  rintro _ ⟨w, -, rfl⟩
  exact w.2

theorem towerRHS_puncture (n : ℕ) (W₀ : (nextPuncture (k := k) n).toScheme.affineOpens) :
    (towerRHS (n + 1)).ideal ⟨(nextPuncture n).ι ''ᵁ W₀.1, W₀.2.image_of_isOpenImmersion _⟩ =
      ((towerRHS n).ideal ⟨(currentPuncture n).ι ''ᵁ (punctureIso n ''ᵁ W₀.1),
          (W₀.2.image_of_isOpenImmersion (punctureIso n)).image_of_isOpenImmersion _⟩).map
        ((punctureIso n).appIso W₀.1).hom.hom := by
  show (fiberStrictIdeal (n + 1)).ideal _ *
      (idealSheafDataFinProd (fun j => idealSheafDataPow (oldIdealAt (n + 1) j) (j + 1)) n).ideal _ *
      (idealSheafDataPow (stepExceptionalIdeal n) (n + 1)).ideal _ = _
  rw [idealSheafDataPow_ideal,
    stepExceptionalIdeal_puncture n ⟨(nextPuncture n).ι ''ᵁ W₀.1, W₀.2.image_of_isOpenImmersion _⟩
      (image_le_nextPuncture n W₀.1),
    Ideal.span_singleton_one, Ideal.top_pow, Ideal.mul_top, fiberStrictIdeal_puncture_transport n W₀,
    Ideal.comap_inv_eq_map_hom]
  cases n with
  | zero =>
    show Ideal.map _ _ * (⊤ : Ideal _) = Ideal.map _ ((fiberStrictIdeal 0).ideal _)
    rw [Ideal.mul_top]
  | succ m =>
    show Ideal.map _ _ *
        ((idealSheafDataFinProd (fun j => idealSheafDataPow (oldIdealAt (m + 1 + 1) j) (j + 1)) m).ideal _ *
          (idealSheafDataPow (oldIdealAt (m + 1 + 1) m) (m + 1)).ideal _) =
      Ideal.map _ ((fiberStrictIdeal (m + 1)).ideal _ *
        (idealSheafDataFinProd (fun j => idealSheafDataPow (oldIdealAt (m + 1) j) (j + 1)) m).ideal _ *
        (idealSheafDataPow (stepExceptionalIdeal m) (m + 1)).ideal _)
    rw [Ideal.map_mul, Ideal.map_mul, idealSheafDataPow_ideal, idealSheafDataPow_ideal,
      Ideal.map_pow, oldIdealAt_birth_transport m W₀, mul_assoc]
    congr 2
    exact idealSheafDataFinProd_ideal_map _ _ _ _ _ m (fun j hj => by
      rw [idealSheafDataPow_ideal, idealSheafDataPow_ideal, Ideal.map_pow,
        oldIdealAt_step_transport m j hj W₀])

/-! ## The three cases of the cover of stage `n+1` -/

theorem first_case (n : ℕ) (W : (projectiveContactStage (k := k) (n + 1)).affineOpens)
    (hW : W.1 ≤ (firstAffineOpen (n + 1)).1) :
    (totalFiberIdeal (n + 1)).ideal W = (towerRHS (n + 1)).ideal W := by
  refine IdealSheafData.ideal_eq_of_nonempty _ _ W (fun hne => ?_)
  have hW' : W.1 ≤ between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1)) ⁻¹ᵁ
      productOpen 0 0 := hW.trans (firstAffineOpen_le_preimage (n + 1))
  have hres := congrArg (fun m => m (fiberZeroChartEquation 0))
    (Scheme.Hom.appLE_map (f := between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1)))
      (firstAffineOpen_le_preimage (n + 1)) (homOfLE hW).op)
  simp only [CommRingCat.comp_apply] at hres
  have hgen : (between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1))).appLE
      (productOpen 0 0) W.1 hW' (fiberZeroChartEquation 0) =
      ((projectiveContactStage (k := k) (n + 1)).presheaf.map (homOfLE hW).op).hom
          (fiberFirstAmbientEquation (n + 1)) *
        ((projectiveContactStage (k := k) (n + 1)).presheaf.map (homOfLE hW).op).hom
          (firstExceptionalAmbientEquation n) ^ (n + 1) := by
    rw [← hres, between_appLE_first']
    show ((projectiveContactStage (k := k) (n + 1)).presheaf.map (homOfLE hW).op).hom
      (firstExceptionalAmbientEquation n ^ (n + 1) * fiberFirstAmbientEquation (n + 1)) = _
    rw [map_mul, map_pow, mul_comm]
  have hFP : (idealSheafDataFinProd
      (fun j => idealSheafDataPow (oldIdealAt (k := k) (n + 1) j) (j + 1)) n).ideal W = ⊤ :=
    idealSheafDataFinProd_ideal_eq_top _ W n (fun j hj => by
      rw [idealSheafDataPow_ideal, oldIdealAt_of_le (n + 1) j (by omega),
        oldFinalIdeal_first (n + 1) j (by omega) W hW, Ideal.span_singleton_one, Ideal.top_pow])
  rw [totalFiberIdeal_ideal (n + 1) (fiberChartZero 0) W hW']
  show Ideal.span {(between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1))).appLE
    (productOpen 0 0) W.1 hW' (fiberZeroChartEquation 0)} = _
  rw [hgen]
  show _ = (fiberStrictIdeal (n + 1)).ideal W *
      (idealSheafDataFinProd (fun j => idealSheafDataPow (oldIdealAt (n + 1) j) (j + 1)) n).ideal W *
      (idealSheafDataPow (stepExceptionalIdeal n) (n + 1)).ideal W
  rw [hFP, idealSheafDataPow_ideal, ← (fiberStrictIdeal (n + 1)).map_ideal hW,
    fiberStrictIdeal_firstOpen, ← (stepExceptionalIdeal n).map_ideal hW,
    stepExceptionalIdeal_firstOpen, Ideal.map_span, Ideal.map_span, Set.image_singleton,
    Set.image_singleton, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.span_singleton_mul_span_singleton]
  rfl

theorem secondExceptionalAmbientEquation_eq (n : ℕ) :
    secondExceptionalAmbientEquation (k := k) n = secondSectionsEquiv n vEquation := rfl

theorem oldStrictSecondAmbientEquation_eq (j : ℕ) :
    oldStrictSecondAmbientEquation (k := k) j = secondSectionsEquiv (j + 1) oldRatio := rfl

theorem oldIdealAt_birth (m : ℕ) : oldIdealAt (k := k) (m + 1 + 1) m = oldStrictIdeal m :=
  (oldIdealAt_of_le (m + 1 + 1) m (le_refl _)).trans (oldFinalIdeal_birth m)

/-- On the second Rees open the strict fibre is the unit ideal. -/
theorem second_case_fiber (n : ℕ) (W : (projectiveContactStage (k := k) (n + 1)).affineOpens)
    (hW : W.1 ≤ (secondAffineOpen n).1) : (fiberStrictIdeal (k := k) (n + 1)).ideal W = ⊤ := by
  rw [← (fiberStrictIdeal (n + 1)).map_ideal hW, fiberStrictIdeal_secondOpen,
    Ideal.span_singleton_one, Ideal.map_top]

/-- On the second Rees open `P^{n+1}` is generated by `v'^{n+1}`. -/
theorem second_case_exceptional (n : ℕ)
    (W : (projectiveContactStage (k := k) (n + 1)).affineOpens)
    (hW : W.1 ≤ (secondAffineOpen n).1) :
    (idealSheafDataPow (stepExceptionalIdeal (k := k) n) (n + 1)).ideal W =
      Ideal.span {((projectiveContactStage (k := k) (n + 1)).presheaf.map (homOfLE hW).op).hom
        (secondSectionsEquiv n vEquation) ^ (n + 1)} := by
  rw [idealSheafDataPow_ideal, ← (stepExceptionalIdeal n).map_ideal hW,
    stepExceptionalIdeal_secondOpen, Ideal.map_span, Set.image_singleton,
    secondExceptionalAmbientEquation_eq]
  exact Ideal.span_singleton_pow _ _

/-- On the second Rees open `Π_{j<n} C_j^{j+1}` is generated by `(u/v)^n` (only `C_{n-1}` meets
the open). -/
theorem second_case_old (n : ℕ) (W : (projectiveContactStage (k := k) (n + 1)).affineOpens)
    (hW : W.1 ≤ (secondAffineOpen n).1) :
    (idealSheafDataFinProd
        (fun j => idealSheafDataPow (oldIdealAt (k := k) (n + 1) j) (j + 1)) n).ideal W =
      Ideal.span {((projectiveContactStage (k := k) (n + 1)).presheaf.map (homOfLE hW).op).hom
        (secondSectionsEquiv n oldRatio) ^ n} := by
  cases n with
  | zero =>
    rw [pow_zero, Ideal.span_singleton_one]
    exact idealSheafDataFinProd_ideal_eq_top _ W 0 (fun j hj => absurd hj (Nat.not_lt_zero j))
  | succ m =>
    have hFP : (idealSheafDataFinProd
        (fun j => idealSheafDataPow (oldIdealAt (k := k) (m + 1 + 1) j) (j + 1)) m).ideal W = ⊤ :=
      idealSheafDataFinProd_ideal_eq_top _ W m (fun j hj => by
        rw [idealSheafDataPow_ideal, oldIdealAt_of_le (m + 1 + 1) j (by omega),
          oldFinalIdeal_second (m + 1) j (by omega) W hW, Ideal.span_singleton_one, Ideal.top_pow])
    show (idealSheafDataFinProd
        (fun j => idealSheafDataPow (oldIdealAt (m + 1 + 1) j) (j + 1)) m).ideal W *
      (idealSheafDataPow (oldIdealAt (m + 1 + 1) m) (m + 1)).ideal W = _
    rw [hFP, Ideal.top_mul, idealSheafDataPow_ideal, oldIdealAt_birth,
      ← (oldStrictIdeal m).map_ideal hW, oldStrictIdeal_secondOpen, Ideal.map_span,
      Set.image_singleton, oldStrictSecondAmbientEquation_eq]
    exact Ideal.span_singleton_pow _ _

theorem second_case (n : ℕ) (W : (projectiveContactStage (k := k) (n + 1)).affineOpens)
    (hW : W.1 ≤ (secondAffineOpen n).1) :
    (totalFiberIdeal (n + 1)).ideal W = (towerRHS (n + 1)).ideal W := by
  refine IdealSheafData.ideal_eq_of_nonempty _ _ W (fun hne => ?_)
  have hW' : W.1 ≤ between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1)) ⁻¹ᵁ
      productOpen 0 0 := hW.trans (secondAffineOpen_le_preimage n)
  have hres := congrArg (fun m => m (fiberZeroChartEquation 0))
    (Scheme.Hom.appLE_map (f := between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1)))
      (secondAffineOpen_le_preimage n) (homOfLE hW).op)
  simp only [CommRingCat.comp_apply] at hres
  have hgen : (between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1))).appLE
      (productOpen 0 0) W.1 hW' (fiberZeroChartEquation 0) =
      ((projectiveContactStage (k := k) (n + 1)).presheaf.map (homOfLE hW).op).hom
          (secondSectionsEquiv n oldRatio) ^ n *
        ((projectiveContactStage (k := k) (n + 1)).presheaf.map (homOfLE hW).op).hom
          (secondSectionsEquiv n vEquation) ^ (n + 1) := by
    rw [← hres, between_appLE_second']
    show ((projectiveContactStage (k := k) (n + 1)).presheaf.map (homOfLE hW).op).hom
      (secondSectionsEquiv n oldRatio ^ n * secondSectionsEquiv n vEquation ^ (n + 1)) = _
    rw [map_mul, map_pow, map_pow]
  rw [totalFiberIdeal_ideal (n + 1) (fiberChartZero 0) W hW']
  show Ideal.span {(between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1))).appLE
    (productOpen 0 0) W.1 hW' (fiberZeroChartEquation 0)} = _
  rw [hgen]
  show _ = (fiberStrictIdeal (n + 1)).ideal W *
      (idealSheafDataFinProd (fun j => idealSheafDataPow (oldIdealAt (n + 1) j) (j + 1)) n).ideal W *
      (idealSheafDataPow (stepExceptionalIdeal n) (n + 1)).ideal W
  rw [second_case_fiber n W hW, second_case_old n W hW, second_case_exceptional n W hW,
    Ideal.top_mul]
  exact (Ideal.span_singleton_mul_span_singleton _ _).symm

theorem puncture_case (n : ℕ) (i j : Fin 2) (ih : totalFiberIdeal (k := k) n = towerRHS n)
    (W : (projectiveContactStage (k := k) (n + 1)).affineOpens)
    (hW : W.1 ≤ nextPuncture n ⊓
      between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1)) ⁻¹ᵁ productOpen i j) :
    (totalFiberIdeal (n + 1)).ideal W = (towerRHS (n + 1)).ideal W := by
  refine IdealSheafData.ideal_eq_of_image' (nextPuncture n) _ _ _ (fun W₀ hW₀ => ?_) W hW
  refine IdealSheafData.ideal_eq_of_nonempty _ _ _ (fun hne => ?_)
  obtain ⟨⟨_, ⟨w, hw, rfl⟩⟩⟩ := hne
  haveI : Nonempty W₀.1 := ⟨⟨w, hw⟩⟩
  rw [towerRHS_puncture n W₀, ← ih]
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  · exact totalFiberIdeal_puncture n (fiberChartZero i) W₀ hW₀
  · exact totalFiberIdeal_puncture n (fiberChartOne i) W₀ hW₀

/-! ## Stage `0` -/

theorem zero_case : totalFiberIdeal (k := k) 0 = towerRHS 0 := by
  apply IdealSheafData.ext_of_affine_cover _ _
    (fun p : Fin 2 × Fin 2 =>
      between (projectiveProductInitial (k := k)) (Nat.zero_le 0) ⁻¹ᵁ productOpen p.1 p.2)
    (fun x => by
      obtain ⟨i, j, h⟩ := productCharts_cover
        ((between (projectiveProductInitial (k := k)) (Nat.zero_le 0)).base x)
      exact ⟨(i, j), mem_productOpen_of_mem_range i j _ h⟩)
  rintro ⟨i, j⟩ W hW
  refine IdealSheafData.ideal_eq_of_nonempty _ _ W (fun hne => ?_)
  have hW' : W.1 ≤ productOpen i j := by
    intro x hx
    have := hW hx
    rwa [between_refl (projectiveProductInitial (k := k)) 0] at this
  have hW'' : W ≤ fiberChartAffineOpen i j := hW'
  show _ = (FrobeniusFiberClosure.liftedFiberClosureIdeal (projectiveProductInitial (k := k)) 0).ideal W
  rw [fiberStrictIdeal_zero,
    ← (FrobeniusGraphPicardClassZeroFiber.horizontalFiberMorphism (0 : k)).ker.map_ideal hW'']
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  · have hgen : (between (projectiveProductInitial (k := k)) (Nat.zero_le 0)).appLE
        (productOpen i 0) W.1 hW (fiberZeroChartEquation i) =
        ((projectiveContactStage (k := k) 0).presheaf.map (homOfLE hW'').op).hom
          (fiberZeroChartEquation i) := by
      rw [appLE_congr_hom (between_refl (projectiveProductInitial (k := k)) 0), Scheme.Hom.appLE,
        Scheme.id_app, Category.id_comp]
      rfl
    rw [totalFiberIdeal_ideal 0 (fiberChartZero i) W hW, horizontalFiber_ideal_chart_zero,
      Ideal.map_span, Set.image_singleton]
    exact congrArg (fun s => Ideal.span {s}) hgen
  · rw [totalFiberIdeal_ideal 0 (fiberChartOne i) W hW, horizontalFiber_ideal_chart_one,
      Ideal.span_singleton_one, Ideal.map_top, Ideal.eq_top_iff_one]
    have hone : ((between (projectiveProductInitial (k := k)) (Nat.zero_le 0)).appLE
        (fiberChartOne i).chart.openSet W.1 hW) (fiberChartOne i).coefficient = 1 :=
      map_one ((between (projectiveProductInitial (k := k)) (Nat.zero_le 0)).appLE
        (fiberChartOne i).chart.openSet W.1 hW).hom
    rw [hone]
    exact Ideal.mem_span_singleton_self 1

/-! ## The identity of ideal sheaves and the Cartier identity -/

/-- The cover of stage `n+1`: the selected chart open, the second Rees open, and the pieces of the
centre complement over the four product charts. -/
def coverOpen (n : ℕ) : Bool ⊕ (Fin 2 × Fin 2) → (projectiveContactStage (k := k) (n + 1)).Opens :=
  Sum.elim (fun b => bif b then (firstAffineOpen (n + 1)).1 else (secondAffineOpen n).1)
    (fun p => nextPuncture n ⊓
      between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1)) ⁻¹ᵁ productOpen p.1 p.2)

theorem coverOpen_covers (n : ℕ) (x : projectiveContactStage (k := k) (n + 1)) :
    ∃ i, x ∈ coverOpen n i := by
  rcases strictProductStage_cover n x with h | h | h
  · exact ⟨Sum.inl true, h⟩
  · exact ⟨Sum.inl false, h⟩
  · obtain ⟨i, j, hij⟩ := productCharts_cover
      ((between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1))).base x)
    exact ⟨Sum.inr (i, j), h, mem_productOpen_of_mem_range i j _ hij⟩

/-- **The identity of ideal sheaves** `π^*(y = 0) = F̃ · Π_{j<n} C_j^{j+1} · P^{n+1}` on every stage. -/
theorem totalFiberIdeal_eq : ∀ n : ℕ, totalFiberIdeal (k := k) n = towerRHS n
  | 0 => zero_case
  | n + 1 => by
    apply IdealSheafData.ext_of_affine_cover _ _ (coverOpen n) (coverOpen_covers n)
    rintro (b | ⟨i, j⟩) W hW
    · cases b
      · exact second_case n W hW
      · exact first_case n W hW
    · exact puncture_case n i j (totalFiberIdeal_eq n) W hW

/-- **The Cartier-level identity** on stage `N+1`:
`π^*(y = 0) = F̃ + Σ_{j<N} (j+1)·C_j + (N+1)·P`. -/
theorem totalFiberDivisor_eq (N : ℕ) :
    totalFiberDivisor (k := k) (N + 1) =
      fiberStrictDivisor (N + 1) +
        ∑ j : Fin N, (j.val + 1) • oldFinalDivisor (N + 1) j.val (by omega) +
        (N + 1) • stepExceptionalDivisor N := by
  have hI : IdealLocallyPrincipalRegular (totalFiberIdeal (k := k) (N + 1)) := by
    rw [totalFiberIdeal_eq]
    exact idealSheafDataMul_locallyPrincipalRegular
      (idealSheafDataMul_locallyPrincipalRegular (fiberStrictIdeal_locallyPrincipalRegular _)
        (idealSheafDataFinProd_locallyPrincipalRegular _
          (fun j => idealSheafDataPow_locallyPrincipalRegular
            (oldIdealAt_locallyPrincipalRegular _ _) _) _))
      (idealSheafDataPow_locallyPrincipalRegular (stepExceptionalIdeal_locallyPrincipalRegular _) _)
  have h := cartierDivisorOfIdeal_tower _ (totalFiberIdeal (N + 1)) (fiberStrictIdeal (N + 1))
    (stepExceptionalIdeal N) (oldIdealAt (N + 1)) N (N + 1) hI
    (fiberStrictIdeal_locallyPrincipalRegular _) (stepExceptionalIdeal_locallyPrincipalRegular N)
    (oldIdealAt_locallyPrincipalRegular (N + 1)) (totalFiberIdeal_eq (N + 1))
  rw [← eq_cartierDivisorOfIdeal _ _ hI (totalFiberDivisor (N + 1))
    (totalFiberDivisor_hasRegularEquations (N + 1)) rfl] at h
  rw [h, fiberStrictDivisor, stepExceptionalDivisor]
  congr 2
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [oldFinalDivisor]
  congr 1
  exact cartierDivisorOfIdeal_congr _ _ _ (oldIdealAt_of_le (N + 1) j.val (by omega)) _

/-- The Picard relation between the classes of the actual Cartier divisors. -/
theorem totalFiberDivisor_picard (N : ℕ) :
    cartierPicardHom _ (totalFiberDivisor (k := k) (N + 1)) =
      cartierPicardHom _ (fiberStrictDivisor (N + 1)) +
        ∑ j : Fin N, (j.val + 1) • cartierPicardHom _ (oldFinalDivisor (N + 1) j.val (by omega)) +
        (N + 1) • cartierPicardHom _ (stepExceptionalDivisor N) :=
  cartierPicardHom_fiber_relation _ _ _ _ (fun j : Fin N => oldFinalDivisor (N + 1) j.val (by omega))
    (N + 1) (totalFiberDivisor_eq N)

end KltDP.Examples.FrobeniusTowerCartierIdentity

namespace KltDP.Examples

open KltDP.Geometry FrobeniusTowerFiberPullback FrobeniusTowerCartierIdentity
  FrobeniusFiberStrictCartier FrobeniusOldExceptionalLaterCartier FrobeniusExceptionalCartier

/-- **F29, task 19.2 (Cartier level).** On stage `N+1` of the origin contact tower of the fibre
`y = 0` of `P¹ × P¹`, the total transform of the fibre, as an effective Cartier divisor, is
`F̃ + Σ_{j<N} (j+1)·C_j + (N+1)·P`. -/
theorem f29_tower_fiber_relation (k : Type u) [Field k] (N : ℕ) :
    totalFiberDivisor (k := k) (N + 1) =
      fiberStrictDivisor (N + 1) +
        ∑ j : Fin N, (j.val + 1) • oldFinalDivisor (N + 1) j.val (by omega) +
        (N + 1) • stepExceptionalDivisor N :=
  totalFiberDivisor_eq N

theorem f29_tower_fiber_relation_universe_check (k : Type u) [Field k] : True := by
  have := f29_tower_fiber_relation.{u} k
  trivial

end KltDP.Examples

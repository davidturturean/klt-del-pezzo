import KltDP.Geometry.CartierDivisorPullback
import KltDP.Geometry.KernelIdealIsoTransport
import KltDP.Examples.FrobeniusFiberZeroClass
import KltDP.Examples.FrobeniusFiberStrictCartier
import KltDP.Examples.FrobeniusExceptionalCartier
import KltDP.Examples.FrobeniusOldExceptionalLaterCartier

/-!
# The total transform of the fibre `y = 0` on the origin contact tower

The composite blowdown `π_N = between (Nat.zero_le N) : S_N ⟶ S_0 = P¹ × P¹` of the origin contact
tower sends the generic point to the generic point (`between_genericPoint`: each step is an
isomorphism over the centre complement), so BRIEF18's effective Cartier divisor `fiberZeroDivisor`
of the fibre `y = 0` pulls back (generic `pullbackDivisor`) to the effective Cartier divisor
`totalFiberDivisor N = π_N^*(y = 0)` on stage `N`, with regular equations and ideal-sheaf data
`totalFiberIdeal N`. On an affine open inside `π_N ⁻¹ᵁ (productOpen i j)` this ideal is generated
by `π_N.appLE _ _ c` for the chart coefficient `c` (`totalFiberIdeal_ideal`); through the chart
squares this generator is computed on the selected chart open of stage `N`
(`u^N v`: `between_appLE_first'`), on the second Rees open of the last blowup of stage `n+1`
(`(u/v)^n v^{n+1}`: `between_appLE_second'`), and over the centre complement it is the transport
of the stage-`n` generator along the restricted blowdown (`totalFiberIdeal_puncture`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusTowerFiberPullback

open KltDP.Geometry
open FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
  FrobeniusStrictTransformStepPuncture FrobeniusStrictTransformInvertible
  FrobeniusStrictTransformSecondChartFrame FrobeniusStrictTransformSecondChart
  FrobeniusFiberTotalProduct FrobeniusStrictTransformFirstChartTensorFrame
  FrobeniusStrictTransformSecondChartTensorFrame FrobeniusOldExceptionalSecondChartFrame
  FrobeniusExceptionalSuccessorChart FrobeniusBlowupChartIteration
  FrobeniusGraphPicardClassCharts FrobeniusGraphPicardClassMixedCoordinates
  FrobeniusFiberZeroClass FrobeniusFiberZeroInvertible FrobeniusFiberStrictCartier
  FrobeniusTowerFunctionField FrobeniusGraphPicardClassIntegral FrobeniusProductPlaneChart
  FrobeniusBlowupContact KltDP.Geometry.AffineBlowup FrobeniusExceptionalCharts
  FrobeniusBlowupSmooth

variable {k : Type u} [Field k]

local instance initialIntegral : IsIntegral (projectiveProductInitial (k := k)).carrier :=
  projectiveProduct_isIntegral

/-! ## The blowdowns preserve the generic point -/

local instance currentPuncture_nonempty (n : ℕ) :
    Nonempty (currentPuncture (k := k) n).toScheme :=
  PlaneChartedScheme.initialPuncture_nonempty ((projectiveProductInitial (k := k)).stage n)

local instance currentPuncture_isIntegral (n : ℕ) :
    IsIntegral (currentPuncture (k := k) n).toScheme :=
  PlaneChartedScheme.initialPuncture_isIntegral ((projectiveProductInitial (k := k)).stage n)

local instance nextPuncture_nonempty (n : ℕ) : Nonempty (nextPuncture (k := k) n).toScheme :=
  ⟨(inv (punctureIso (k := k) n)).base (Classical.choice (currentPuncture_nonempty n))⟩

local instance nextPuncture_isIntegral (n : ℕ) : IsIntegral (nextPuncture (k := k) n).toScheme :=
  isIntegral_of_isOpenImmersion (nextPuncture (k := k) n).ι

theorem punctureIso_base (n : ℕ) (w : (nextPuncture (k := k) n).toScheme) :
    (currentPuncture (k := k) n).ι.base ((punctureIso n).base w) =
      ((projectiveProductInitial (k := k)).stepProjection n).base ((nextPuncture n).ι.base w) := by
  rw [← TopCat.comp_app, ← Scheme.comp_base, morphismRestrict_ι]
  rfl

theorem stepProjection_genericPoint (n : ℕ) :
    ((projectiveProductInitial (k := k)).stepProjection n).base
        (genericPoint (projectiveContactStage (k := k) (n + 1))) =
      genericPoint (projectiveContactStage (k := k) n) := by
  rw [← genericPoint_eq_of_isOpenImmersion (nextPuncture (k := k) n).ι,
    ← genericPoint_eq_of_isOpenImmersion (currentPuncture (k := k) n).ι,
    ← genericPoint_eq_of_isOpenImmersion (punctureIso (k := k) n), punctureIso_base]

theorem between_genericPoint : ∀ N : ℕ,
    (between (projectiveProductInitial (k := k)) (Nat.zero_le N)).base
        (genericPoint (projectiveContactStage (k := k) N)) =
      genericPoint (projectiveContactStage (k := k) 0)
  | 0 => by rw [between_refl (projectiveProductInitial (k := k))]; rfl
  | N + 1 => by
    rw [between_succ (projectiveProductInitial (k := k)) (Nat.zero_le N), Scheme.comp_base, TopCat.comp_app,
      stepProjection_genericPoint, between_genericPoint N]

instance between_genericPointPreserving (N : ℕ) :
    GenericPointPreserving (between (projectiveProductInitial (k := k)) (Nat.zero_le N)) :=
  ⟨between_genericPoint N⟩

theorem between_succ_base (n : ℕ) (x : projectiveContactStage (k := k) (n + 1)) :
    (between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1))).base x =
      (between (projectiveProductInitial (k := k)) (Nat.zero_le n)).base
        (((projectiveProductInitial (k := k)).stepProjection n).base x) := by
  rw [between_succ (projectiveProductInitial (k := k)) (Nat.zero_le n), Scheme.comp_base, TopCat.comp_app]

/-! ## The total transform of the fibre -/

/-- The total transform `π_N^*(y = 0)` of the fibre on stage `N`, as an effective Cartier divisor. -/
def totalFiberDivisor (N : ℕ) : CartierDivisor (projectiveContactStage (k := k) N) :=
  pullbackDivisor (between (projectiveProductInitial (k := k)) (Nat.zero_le N)) fiberZeroDivisor
    fiberZeroDivisor_hasRegularEquations

theorem totalFiberDivisor_hasRegularEquations (N : ℕ) :
    HasRegularCartierEquations _ (totalFiberDivisor (k := k) N) :=
  pullbackDivisor_hasRegularEquations _ _ _

/-- The ideal-sheaf data of the total transform. -/
def totalFiberIdeal (N : ℕ) : (projectiveContactStage (k := k) N).IdealSheafData :=
  pullbackIdealData (between (projectiveProductInitial (k := k)) (Nat.zero_le N)) fiberZeroDivisor
    fiberZeroDivisor_hasRegularEquations

/-- BRIEF18's regular chart of `y = 0` on the product chart `(i, 0)` (coefficient `v`), regarded
on stage `0` of the tower. -/
def fiberChartZero (i : Fin 2) :
    RegularCartierEquationChart (projectiveContactStage (k := k) 0) fiberZeroDivisor :=
  fiberZeroChartZero i

/-- BRIEF18's regular chart of `y = 0` on the product chart `(i, 1)` (coefficient `1`), regarded
on stage `0` of the tower. -/
def fiberChartOne (i : Fin 2) :
    RegularCartierEquationChart (projectiveContactStage (k := k) 0) fiberZeroDivisor :=
  fiberZeroChartOne i

theorem fiberChartZero_openSet (i : Fin 2) :
    (fiberChartZero (k := k) i).chart.openSet = productOpen i 0 := rfl

theorem fiberChartZero_coefficient (i : Fin 2) :
    (fiberChartZero (k := k) i).coefficient = fiberZeroChartEquation i := rfl

theorem fiberChartOne_openSet (i : Fin 2) :
    (fiberChartOne (k := k) i).chart.openSet = productOpen i 1 := rfl

theorem fiberChartOne_coefficient (i : Fin 2) : (fiberChartOne (k := k) i).coefficient = 1 := rfl

theorem totalFiberIdeal_eq_idealData (N : ℕ) :
    totalFiberIdeal (k := k) N =
      effectiveCartierIdealDataOfRegularEquations _ (totalFiberDivisor N)
        (totalFiberDivisor_hasRegularEquations N) := rfl

/-- On an affine open inside the preimage of a regular chart `c` of the fibre, the ideal of the
total transform is generated by the pulled-back coefficient. -/
theorem totalFiberIdeal_ideal (N : ℕ)
    (c : RegularCartierEquationChart (projectiveContactStage (k := k) 0) fiberZeroDivisor)
    (W : (projectiveContactStage (k := k) N).affineOpens) [Nonempty W.1]
    (hW : W.1 ≤ between (projectiveProductInitial (k := k)) (Nat.zero_le N) ⁻¹ᵁ c.chart.openSet) :
    (totalFiberIdeal N).ideal W =
      Ideal.span {(between (projectiveProductInitial (k := k)) (Nat.zero_le N)).appLE
        c.chart.openSet W.1 hW c.coefficient} :=
  pullbackIdealData_ideal _ _ _ c W hW

/-! ## The selected chart open -/

theorem firstAffineOpen_le_preimage (N : ℕ) :
    (firstAffineOpen (k := k) N).1 ≤
      between (projectiveProductInitial (k := k)) (Nat.zero_le N) ⁻¹ᵁ productOpen 0 0 := by
  rintro _ ⟨z, -, rfl⟩
  show (between (projectiveProductInitial (k := k)) (Nat.zero_le N)).base
    (((projectiveProductInitial (k := k)).stage N).chart.base z) ∈ productOpen 0 0
  rw [between_zero (projectiveProductInitial (k := k)), ← TopCat.comp_app, ← Scheme.comp_base,
    PlaneChartedScheme.stage_chart_toInitial]
  refine ⟨(stageProjection N).base z, trivial, ?_⟩
  rw [productChart_zero_zero, Scheme.comp_base, TopCat.comp_app]
  rfl

theorem chart_between_square (N : ℕ) :
    ((projectiveProductInitial (k := k)).stage N).chart ≫
        between (projectiveProductInitial (k := k)) (Nat.zero_le N) =
      Spec.map (CommRingCat.ofHom (stageSubstitution N)) ≫ productChart 0 0 := by
  rw [between_zero (projectiveProductInitial (k := k)), PlaneChartedScheme.stage_chart_toInitial, stageProjection_eq,
    productChart_zero_zero]
  rfl

theorem between_appLE_first (N : ℕ) :
    (between (projectiveProductInitial (k := k)) (Nat.zero_le N)).appLE (productOpen 0 0)
        (firstAffineOpen N).1 (firstAffineOpen_le_preimage N) (fiberZeroChartEquation 0) =
      (((projectiveProductInitial (k := k)).stage N).chart.appIso ⊤).inv
        ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv (stageSubstitution N vCoord)) :=
  appLE_of_chart_square _ (productChart 0 0) _ (CommRingCat.ofHom (stageSubstitution N))
    (chart_between_square N) (firstAffineOpen_le_preimage N) vCoord

/-- `π_{N+1}^* v = u^{N+1} v` on the selected chart open of stage `N+1`. -/
theorem between_appLE_first' (N : ℕ) :
    (between (projectiveProductInitial (k := k)) (Nat.zero_le (N + 1))).appLE (productOpen 0 0)
        (firstAffineOpen (N + 1)).1 (firstAffineOpen_le_preimage (N + 1))
        (fiberZeroChartEquation 0) =
      firstExceptionalAmbientEquation N ^ (N + 1) * fiberFirstAmbientEquation (N + 1) := by
  rw [between_appLE_first, stageSubstitution_v]
  change (((projectiveProductInitial (k := k)).stage (N + 1)).chart.appIso ⊤).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv.hom (uCoord ^ (N + 1) * vCoord)) = _
  rw [map_mul, map_pow, map_mul, map_pow]
  rfl

/-! ## The second Rees open of the last blowup -/

theorem secondAffineOpen_le_preimage_first (n : ℕ) :
    (secondAffineOpen (k := k) n).1 ≤
      (projectiveProductInitial (k := k)).stepProjection n ⁻¹ᵁ (firstAffineOpen n).1 := by
  rintro _ ⟨z, -, rfl⟩
  show ((projectiveProductInitial (k := k)).stepProjection n).base
    ((secondStageChart n).base z) ∈ (firstAffineOpen n).1
  rw [← TopCat.comp_app, ← Scheme.comp_base]
  change (secondStageChart n ≫ ((projectiveProductInitial (k := k)).stage n).nextProjection).base z
    ∈ (firstAffineOpen n).1
  rw [secondStageChart_projection, Scheme.comp_base, TopCat.comp_app]
  exact ⟨_, trivial, rfl⟩

theorem secondAffineOpen_le_preimage (n : ℕ) :
    (secondAffineOpen (k := k) n).1 ≤
      between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1)) ⁻¹ᵁ productOpen 0 0 := by
  intro x hx
  have h2 := firstAffineOpen_le_preimage n (secondAffineOpen_le_preimage_first n hx)
  show (between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1))).base x ∈ productOpen 0 0
  rw [between_succ_base]
  exact h2

theorem secondChart_between_square (n : ℕ) :
    secondStageChart (k := k) n ≫ between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1)) =
      Spec.map (CommRingCat.ofHom
        ((chartBaseMap (centerIdeal (k := k)) centerV).comp (stageSubstitution n))) ≫
        productChart 0 0 := by
  rw [between_succ (projectiveProductInitial (k := k)) (Nat.zero_le n), ← Category.assoc]
  change (secondStageChart n ≫ ((projectiveProductInitial (k := k)).stage n).nextProjection) ≫
    between (projectiveProductInitial (k := k)) (Nat.zero_le n) = _
  rw [secondStageChart_projection, Category.assoc, between_zero (projectiveProductInitial (k := k)),
    PlaneChartedScheme.stage_chart_toInitial, stageProjection_eq, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, productChart_zero_zero]
  rfl

theorem secondSectionsEquiv_apply (n : ℕ) (x : reesVChartRing k) :
    secondSectionsEquiv n x =
      ((secondStageChart n).appIso ⊤).inv
        ((Scheme.ΓSpecIso (CommRingCat.of (reesVChartRing k))).inv x) := rfl

theorem between_appLE_second (n : ℕ) :
    (between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1))).appLE (productOpen 0 0)
        (secondAffineOpen n).1 (secondAffineOpen_le_preimage n) (fiberZeroChartEquation 0) =
      secondSectionsEquiv n
        (chartBaseMap (centerIdeal (k := k)) centerV (stageSubstitution n vCoord)) := by
  rw [secondSectionsEquiv_apply]
  exact appLE_of_chart_square (secondStageChart n) (productChart 0 0) _
    (CommRingCat.ofHom ((chartBaseMap (centerIdeal (k := k)) centerV).comp (stageSubstitution n)))
    (secondChart_between_square n) (secondAffineOpen_le_preimage n) vCoord

/-- `π_{n+1}^* v = (u/v)^n · v^{n+1}` on the second Rees open of the last blowup of stage `n+1`. -/
theorem between_appLE_second' (n : ℕ) :
    (between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1))).appLE (productOpen 0 0)
        (secondAffineOpen n).1 (secondAffineOpen_le_preimage n) (fiberZeroChartEquation 0) =
      secondSectionsEquiv n oldRatio ^ n * secondSectionsEquiv n vEquation ^ (n + 1) := by
  rw [between_appLE_second, stageSubstitution_v, map_mul, map_pow, ← vEquation_mul_oldRatio]
  change secondSectionsEquiv n ((vEquation * oldRatio) ^ n * vEquation) = _
  rw [map_mul, map_pow, map_mul]
  ring

/-! ## Transport over the centre complement -/

theorem image_puncture_le_preimage (n : ℕ) (W₀ : (nextPuncture (k := k) n).toScheme.Opens)
    (U : (projectiveContactStage (k := k) 0).Opens)
    (hW : (nextPuncture n).ι ''ᵁ W₀ ≤
      between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1)) ⁻¹ᵁ U) :
    (currentPuncture n).ι ''ᵁ (punctureIso n ''ᵁ W₀) ≤
      between (projectiveProductInitial (k := k)) (Nat.zero_le n) ⁻¹ᵁ U := by
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  have hmem : (nextPuncture n).ι.base w ∈ (nextPuncture n).ι ''ᵁ W₀ := ⟨w, hw, rfl⟩
  have := hW hmem
  show (between (projectiveProductInitial (k := k)) (Nat.zero_le n)).base
    ((currentPuncture n).ι.base ((punctureIso n).base w)) ∈ U
  rw [punctureIso_base, ← between_succ_base]
  exact this

theorem image_puncture_le_preimage_step (n : ℕ) (W₀ : (nextPuncture (k := k) n).toScheme.Opens) :
    (nextPuncture n).ι ''ᵁ W₀ ≤
      (projectiveProductInitial (k := k)).stepProjection n ⁻¹ᵁ
        ((currentPuncture n).ι ''ᵁ (punctureIso n ''ᵁ W₀)) := by
  rintro _ ⟨w, hw, rfl⟩
  show ((projectiveProductInitial (k := k)).stepProjection n).base ((nextPuncture n).ι.base w) ∈
    (currentPuncture n).ι ''ᵁ (punctureIso n ''ᵁ W₀)
  rw [← punctureIso_base]
  exact ⟨_, ⟨w, hw, rfl⟩, rfl⟩

theorem stepProjection_appLE_eq_appIso (n : ℕ) (W₀ : (nextPuncture (k := k) n).toScheme.Opens) :
    ((projectiveProductInitial (k := k)).stepProjection n).appLE
        ((currentPuncture n).ι ''ᵁ (punctureIso n ''ᵁ W₀)) ((nextPuncture n).ι ''ᵁ W₀)
        (image_puncture_le_preimage_step n W₀) =
      ((punctureIso n).appIso W₀).hom := by
  rw [Scheme.Hom.appIso_hom', morphismRestrict_appLE]

/-- Over the centre complement of the last blowup, the ideal of the total transform on stage
`n+1` is the transport of the ideal of the total transform on stage `n`. -/
theorem totalFiberIdeal_puncture (n : ℕ)
    (c : RegularCartierEquationChart (projectiveContactStage (k := k) 0) fiberZeroDivisor)
    (W₀ : (nextPuncture (k := k) n).toScheme.affineOpens) [Nonempty W₀.1]
    (hW : (nextPuncture n).ι ''ᵁ W₀.1 ≤
      between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1)) ⁻¹ᵁ c.chart.openSet) :
    (totalFiberIdeal (n + 1)).ideal ⟨(nextPuncture n).ι ''ᵁ W₀.1, W₀.2.image_of_isOpenImmersion _⟩ =
      ((totalFiberIdeal n).ideal ⟨(currentPuncture n).ι ''ᵁ (punctureIso n ''ᵁ W₀.1),
          (W₀.2.image_of_isOpenImmersion (punctureIso n)).image_of_isOpenImmersion _⟩).map
        ((punctureIso n).appIso W₀.1).hom.hom := by
  haveI : Nonempty ((currentPuncture (k := k) n).ι ''ᵁ (punctureIso n ''ᵁ W₀.1)) := by
    obtain ⟨⟨w, hw⟩⟩ := (inferInstance : Nonempty W₀.1)
    exact ⟨⟨_, ⟨_, ⟨w, hw, rfl⟩, rfl⟩⟩⟩
  haveI : Nonempty ((nextPuncture (k := k) n).ι ''ᵁ W₀.1) := by
    obtain ⟨⟨w, hw⟩⟩ := (inferInstance : Nonempty W₀.1)
    exact ⟨⟨_, ⟨w, hw, rfl⟩⟩⟩
  rw [totalFiberIdeal_ideal (n + 1) c _ hW,
    totalFiberIdeal_ideal n c _ (image_puncture_le_preimage n W₀.1 _ hW), Ideal.map_span,
    Set.image_singleton, appLE_congr_hom (between_succ (projectiveProductInitial (k := k)) (Nat.zero_le n)),
    ← Scheme.appLE_comp_appLE _ _ _ _ _ (image_puncture_le_preimage n W₀.1 _ hW)
      (image_puncture_le_preimage_step n W₀.1),
    CommRingCat.comp_apply, stepProjection_appLE_eq_appIso]
  rfl

end KltDP.Examples.FrobeniusTowerFiberPullback

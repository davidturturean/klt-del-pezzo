import KltDP.Examples.FrobeniusFiberTotalProduct
import KltDP.Examples.FrobeniusFiberTranslation
import KltDP.Examples.FrobeniusStrictTransformClassesTower
import KltDP.Examples.FrobeniusOldExceptionalLaterStages
import KltDP.Geometry.SchemeInvertibleSheafPullback
import KltDP.Geometry.ProjectiveSpaceIntegral

/-!
# The Picard class of the strict `b`-fibre along the contact tower

The whole-stage isomorphism `π^* I(F_n) ≅ I(E_n) ⊗ I(F_{n+1})` of `FrobeniusFiberTotalProduct`
propagates invertibility of the strict-fibre ideal up the tower (`fiberKernel_isInvertible_succ`:
`I(F_{n+1})` is a tensor factor of the invertible pulled line, the other factor `I(E_n)` being
invertible) and gives the Picard step

  `F_{n+1} = π^* F_n − E_n`   on stage `n+1`   (`fiberPicardClass_succ`),

hence, by iteration, `F_N = F_0^{(N)} − Σ_{j<N} E_j^{(N)}` in terms of the tower's total exceptional
classes and the total transform `F_0^{(N)}` of the stage-`0` fibre (`fiberPicardClass_tower`).

All Picard statements are relative to the stage-`0` hypothesis `FiberKernelInvertible 0` (the ideal
of the stage-`0` strict fibre is invertible), which is carried as an explicit argument: the
stage-`0` strict fibre has the ideal sheaf of the accepted horizontal fibre `y = 0`
(`fiberStrictIdeal_zero`, the fibre `horizontalFiberMorphism 0` of `FrobeniusGraphPicardClassZeroFiber`),
but neither the invertibility of that ideal nor the identification of its class with the accepted
`b`-fibre class `secondFiberClass` (the class of the fibre `y = 1`) is proved in this lane, so the
manuscript's `F_N = b^{(N)} − Σ_{j<N} E_j^{(N)}` and the full bundle
`strictTransformClasses_tower_full` are not exported. The bundle `strictTransformClasses_tower_fiber`
records B, `C_j`, P and the conditional fibre chain together.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusFiberPicard

open KltDP.Geometry
open FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
open FrobeniusStrictTransformProductKernel FrobeniusStrictTransformPicardStep
open FrobeniusStrictTransformClassesTower FrobeniusOldExceptionalLaterStages
open FrobeniusGraphPicardClassTotalTransform
open FrobeniusFiberClosure FrobeniusFiberTranslation FrobeniusFiberPuncture
open FrobeniusFiberTotalProduct FrobeniusProductPlaneChart FrobeniusGraphPicardClassZeroFiber

attribute [local instance] Types.instFunLike Types.instConcreteCategory

-- No module-level monoidal instance: the Picard group operations must all come from the accepted
-- instances on `X.Pic`, and the tensor products below are taken under explicit `letI`.

variable {k : Type u} [Field k]

/-! ### The stage-`0` strict fibre is the horizontal fibre `y = 0` -/

/-- The chart line of stage `0` is the horizontal fibre `y = 0` through the polynomial chart of the
projective line. -/
theorem fiberResidual_zero :
    @Eq (Spec (CommRingCat.of (Polynomial k)) ⟶ projectiveContactStage (k := k) 0)
      (fiberResidual (projectiveProductInitial (k := k)) 0)
      (ProjectiveLineComparison.polynomialChartMap k 0 ≫ horizontalFiberMorphism 0) := by
  have h : fiberCurve (k := k) = fiberCurveAt 0 := by
    unfold fiberCurve fiberCurveAt
    rw [Polynomial.C_0]
  change fiberCurve ≫ planeChart = _
  rw [h]
  exact fiberCurveAt_planeChart 0

/-- The stage-`0` strict fibre has the ideal sheaf of the horizontal fibre `y = 0`. -/
theorem fiberStrictIdeal_zero :
    @Eq (projectiveContactStage (k := k) 0).IdealSheafData
      (liftedFiberClosureIdeal (projectiveProductInitial (k := k)) 0)
      (horizontalFiberMorphism (0 : k)).ker := by
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  rw [liftedFiberClosureIdeal_eq, fiberResidual_zero]
  exact SchematicImageOpenImmersion.ker_precompose_openImmersion
    (ProjectiveLineComparison.polynomialChartMap k 0) (horizontalFiberMorphism 0)

/-! ### Invertibility propagates up the tower -/

/-- Invertibility of the strict-fibre ideal sheaf on stage `n`. -/
abbrev FiberKernelInvertible (n : ℕ) : Prop :=
  KltDP.SheafOfModules.IsInvertible (R := (projectiveContactStage (k := k) n).ringCatSheaf)
    (schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) n))

/-- The tensor line is the tensor of the exceptional line and of the kernel of `F_{n+1}`, in the
monoidal structure fixed by the accepted Picard machinery. -/
theorem fiberExceptionalTensor_eq (n : ℕ) :
    letI := Scheme.Modules.monoidalCategory (projectiveContactStage (k := k) (n + 1))
    fiberExceptionalTensor (k := k) n =
      (stepExceptionalIdealLine (k := k) n).obj ⊗
        schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)) :=
  rfl

/-- The ideal line of the strict fibre `F_n`, pulled back to stage `n+1`. -/
def fiberPulledLine (n : ℕ) (h : FiberKernelInvertible (k := k) n) :
    InvertibleSheaf (projectiveContactStage (k := k) (n + 1)) :=
  pullbackInvertibleSheaf ((projectiveProductInitial (k := k)).stepProjection n)
    ⟨schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) n), h⟩

/-- The whole-stage comparison, read on the underlying module sheaf of the pulled line. -/
def fiberPulledLineIso (n : ℕ) (h : FiberKernelInvertible (k := k) n) :
    (fiberPulledLine n h).obj ≅ fiberExceptionalTensor (k := k) n :=
  fiberTotalProductIso n

/-- Invertibility of the strict-fibre ideal propagates to the next stage: `I(F_{n+1})` is a tensor
factor of the invertible pulled line, the other factor being the invertible exceptional line. -/
theorem fiberKernel_isInvertible_succ (n : ℕ) (h : FiberKernelInvertible (k := k) n) :
    FiberKernelInvertible (k := k) (n + 1) := by
  refine SchemeTensorPairing.isInvertible_of_isUnit_toSkeleton _ ?_
  letI := Scheme.Modules.monoidalCategory (projectiveContactStage (k := k) (n + 1))
  have hE := (stepExceptionalIdealLine (k := k) n).isUnit_toSkeleton
  have hmul : IsUnit (toSkeleton ((stepExceptionalIdealLine (k := k) n).obj ⊗
      schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)))) := by
    have e : toSkeleton ((stepExceptionalIdealLine (k := k) n).obj ⊗
        schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))) =
          toSkeleton (fiberPulledLine n h).obj := by
      rw [← fiberExceptionalTensor_eq]
      exact Quotient.sound ⟨(fiberPulledLineIso n h).symm⟩
    rw [e]
    exact (fiberPulledLine n h).isUnit_toSkeleton
  rw [Skeleton.toSkeleton_tensorObj] at hmul
  have hmul' : IsUnit ((hE.unit : Skeleton (projectiveContactStage (k := k) (n + 1)).Modules) *
      toSkeleton (schemeKernelIdeal
        (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)))) := by
    rw [IsUnit.unit_spec]
    exact hmul
  exact (Units.isUnit_units_mul hE.unit _).mp hmul'

/-- Given the stage-`0` invertibility, the strict-fibre ideal is invertible on every stage. -/
theorem fiberKernel_isInvertible (h0 : FiberKernelInvertible (k := k) 0) :
    ∀ n : ℕ, FiberKernelInvertible (k := k) n
  | 0 => h0
  | n + 1 => fiberKernel_isInvertible_succ n (fiberKernel_isInvertible h0 n)

/-! ### The Picard step -/

/-- The ideal of the strict fibre `F_n` as an invertible sheaf on stage `n`. -/
def fiberKernelLine (h0 : FiberKernelInvertible (k := k) 0) (n : ℕ) :
    InvertibleSheaf (projectiveContactStage (k := k) n) :=
  ⟨schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) n),
    fiberKernel_isInvertible h0 n⟩

@[simp] theorem fiberKernelLine_obj (h0 : FiberKernelInvertible (k := k) 0) (n : ℕ) :
    (fiberKernelLine h0 n).obj =
      schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) n) := rfl

/-- The pulled-back class of the ideal of `F_n` is the product of the ideal classes of `E_n` and
of `F_{n+1}`. -/
theorem fiberPulledLine_picard (h0 : FiberKernelInvertible (k := k) 0) (n : ℕ) :
    (pullbackInvertibleSheaf ((projectiveProductInitial (k := k)).stepProjection n)
        (fiberKernelLine h0 n)).toPic =
      (stepExceptionalIdealLine n).toPic * (fiberKernelLine h0 (n + 1)).toPic := by
  letI := Scheme.Modules.monoidalCategory (projectiveContactStage (k := k) (n + 1))
  apply Units.ext
  change ((pullbackInvertibleSheaf ((projectiveProductInitial (k := k)).stepProjection n)
        (fiberKernelLine h0 n)).toPic :
      Skeleton (projectiveContactStage (k := k) (n + 1)).Modules) =
    ((stepExceptionalIdealLine (k := k) n).toPic :
      Skeleton (projectiveContactStage (k := k) (n + 1)).Modules) *
      ((fiberKernelLine h0 (n + 1)).toPic :
        Skeleton (projectiveContactStage (k := k) (n + 1)).Modules)
  rw [InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val,
    ← Skeleton.toSkeleton_tensorObj, fiberKernelLine_obj, ← fiberExceptionalTensor_eq]
  exact Quotient.sound ⟨fiberTotalProductIso n⟩

/-- Pullback of the ideal class of `F_n` along the blowdown is exceptional times `F_{n+1}`. -/
theorem fiberKernelLine_picard_step (h0 : FiberKernelInvertible (k := k) 0) (n : ℕ) :
    schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n)
        (fiberKernelLine h0 n).toPic =
      (stepExceptionalIdealLine n).toPic * (fiberKernelLine h0 (n + 1)).toPic := by
  rw [schemePicardPullbackHom_toPic]
  exact fiberPulledLine_picard h0 n

/-- The additive form of the multiplicative step, isolated so that only rewriting is needed. -/
private theorem neg_ofMul_mul_step (h0 : FiberKernelInvertible (k := k) 0) (n : ℕ) :
    -Additive.ofMul ((stepExceptionalIdealLine (k := k) n).toPic *
        (fiberKernelLine h0 (n + 1)).toPic) =
      -Additive.ofMul (stepExceptionalIdealLine (k := k) n).toPic +
        -Additive.ofMul (fiberKernelLine h0 (n + 1)).toPic := by
  rw [ofMul_mul, neg_add]

/-- The Picard class of the strict fibre `F_n` on stage `n`, in the lane's ideal-sheaf sign
convention (a curve's class is minus the class of its ideal line). -/
def fiberPicardClass (h0 : FiberKernelInvertible (k := k) 0) (n : ℕ) :
    Additive (projectiveContactStage (k := k) n).Pic :=
  -Additive.ofMul (fiberKernelLine h0 n).toPic

/-- The Picard pullback of the class of `F_n` is the class of `E_n` plus that of `F_{n+1}`. -/
theorem fiberPicardClass_pullback (h0 : FiberKernelInvertible (k := k) 0) (n : ℕ) :
    (schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n)).toAdditive
        (fiberPicardClass h0 n) =
      stepExceptionalPicardClass n + fiberPicardClass h0 (n + 1) := by
  change (schemePicardPullbackHom
      ((projectiveProductInitial (k := k)).stepProjection n)).toAdditive
        (-Additive.ofMul (fiberKernelLine h0 n).toPic) = _
  rw [map_neg]
  change -Additive.ofMul
      (schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n)
        (fiberKernelLine h0 n).toPic) =
    -Additive.ofMul (stepExceptionalIdealLine n).toPic +
      -Additive.ofMul (fiberKernelLine h0 (n + 1)).toPic
  rw [fiberKernelLine_picard_step]
  exact neg_ofMul_mul_step h0 n

/-- `F_{n+1} = π^* F_n − E_n` on stage `n+1`. -/
theorem fiberPicardClass_succ (h0 : FiberKernelInvertible (k := k) 0) (n : ℕ) :
    fiberPicardClass h0 (n + 1) =
      (schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n)).toAdditive
        (fiberPicardClass h0 n) - stepExceptionalPicardClass (k := k) n := by
  have h := fiberPicardClass_pullback h0 n
  revert h
  generalize (schemePicardPullbackHom
    ((projectiveProductInitial (k := k)).stepProjection n)).toAdditive (fiberPicardClass h0 n) = A
  generalize stepExceptionalPicardClass (k := k) n = B
  generalize fiberPicardClass h0 (n + 1) = C
  intro h
  exact eq_sub_iff_add_eq'.mpr h.symm

/-! ### Iteration along the tower -/

/-- The total transform, on stage `N`, of the stage-`0` strict fibre `F_0`. -/
def fiberTotalClass (h0 : FiberKernelInvertible (k := k) 0) (N : ℕ) :
    Additive (projectiveContactStage (k := k) N).Pic :=
  (schemePicardPullbackHom (between (projectiveProductInitial (k := k)) (Nat.zero_le N))).toAdditive
    (fiberPicardClass h0 0)

theorem fiberTotalClass_zero (h0 : FiberKernelInvertible (k := k) 0) :
    fiberTotalClass h0 0 = fiberPicardClass h0 0 := by
  have hb : between (projectiveProductInitial (k := k)) (Nat.zero_le 0) = 𝟙 _ :=
    between_refl (projectiveProductInitial (k := k)) 0
  have hid : @Eq ((projectiveContactStage (k := k) 0).Pic →*
      (projectiveContactStage (k := k) 0).Pic)
      (schemePicardPullbackHom (between (projectiveProductInitial (k := k)) (Nat.zero_le 0)))
      (MonoidHom.id _) := by
    rw [hb]
    exact schemePicardPullbackHom_id _
  unfold fiberTotalClass
  rw [hid]
  rfl

/-- The total fibre class on the next stage is the one-step pullback. -/
theorem fiberTotalClass_succ (h0 : FiberKernelInvertible (k := k) 0) (N : ℕ) :
    fiberTotalClass h0 (N + 1) =
      (schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection N)).toAdditive
        (fiberTotalClass h0 N) := by
  have h : between (projectiveProductInitial (k := k)) (Nat.zero_le (N + 1)) =
      (projectiveProductInitial (k := k)).stepProjection N ≫
        between (projectiveProductInitial (k := k)) (Nat.zero_le N) :=
    between_succ (projectiveProductInitial (k := k)) (Nat.zero_le N)
  unfold fiberTotalClass
  rw [h, schemePicardPullbackHom_comp]
  rfl

/-- `F_N = F_0^{(N)} − Σ_{j<N} E_j^{(N)}` on stage `N`, in terms of the total transform of the
stage-`0` fibre and the tower's total exceptional classes. -/
theorem fiberPicardClass_tower (h0 : FiberKernelInvertible (k := k) 0) (N : ℕ) :
    fiberPicardClass h0 N = fiberTotalClass h0 N - ∑ j : Fin N, totalExceptionalClass N j := by
  induction N with
  | zero => rw [fiberTotalClass_zero, Fin.sum_univ_zero, sub_zero]
  | succ N ih =>
    rw [fiberPicardClass_succ, ih, map_sub, map_sum, ← fiberTotalClass_succ,
      Fin.sum_univ_castSucc, totalExceptionalClass_last]
    simp only [totalExceptionalClass_castSucc]
    rw [sub_sub]

/-- Bundle: the fibre chain under the stage-`0` invertibility hypothesis — the one-step relation
and the iteration — together with the graph relation `B`, the older exceptional curves `C_j` and the
newest exceptional class `P = E_{N-1}` on every stage. The classes live in
`Additive (projectiveContactStage N).Pic : Type u` for `k : Type u`. The base case `F_0 = b` is not
part of this bundle (see the module docstring). -/
theorem strictTransformClasses_tower_fiber (h0 : FiberKernelInvertible (k := k) 0) :
    (∀ n : ℕ, fiberPicardClass h0 (n + 1) =
      (schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n)).toAdditive
        (fiberPicardClass h0 n) - stepExceptionalPicardClass n) ∧
    (∀ N : ℕ, fiberPicardClass h0 N =
      fiberTotalClass h0 N - ∑ j : Fin N, totalExceptionalClass N j) ∧
    (∀ N m : ℕ, strictCurvePicardClass (k := k) N m =
      (m + N) • firstFiberTotalClass N + secondFiberTotalClass N -
        ∑ j : Fin N, totalExceptionalClass N j) ∧
    (∀ (N j : ℕ) (h : j + 1 + 1 ≤ N),
      oldExceptionalStrictClass (k := k) N j h =
        totalExceptionalClass N ⟨j, by omega⟩ - totalExceptionalClass N ⟨j + 1, by omega⟩) ∧
    (∀ N : ℕ, totalExceptionalClass (k := k) (N + 1) (Fin.last N) =
      stepExceptionalPicardClass N) :=
  ⟨fiberPicardClass_succ h0, fiberPicardClass_tower h0, strictCurvePicardClass_tower,
    oldExceptionalStrictClasses_tower, totalExceptionalClass_last⟩

end KltDP.Examples.FrobeniusFiberPicard

import KltDP.Examples.FrobeniusStrictTransformClassesFull
import KltDP.Examples.FrobeniusTowerTransportCurves
import KltDP.Examples.ProjectiveProductTranslationFibres
import KltDP.Geometry.SchemeKernelIdealIsoTransport

/-!
# The class table of the translated contact towers

Lane A2's class table (`strictTransformClasses_tower_full`) lives on the stages of the contact
tower over the origin `(0, 0)` of `P¹ × P¹`.  The translated tower over the point `(a, a^p)`
(`translatedInitial p a`, stages `selectedStage p a n`) is isomorphic to the origin tower stage by
stage (`stageTranslationIso`), and every curve of the table is carried onto the corresponding
curve of the translated tower (BRIEF24: `fiberClosureTranslationIso`, `graphClosureTranslationIso`,
`finalOldMap_translation`, `stageTranslationIso_previousFiber`; the fibres `x = 1`, `y = 1` go to
`x = 1 + a`, `y = 1 + a^p` by `ProjectiveProductTranslationFibres`).

This module defines the classes of the translated tower from its **own** curves — the kernel ideal
lines of the actual inclusions `closureInclusion (translatedInitial p a) n m` (`B`),
`finalOldMap (translatedInitial p a) N j h` (`C_j`),
`fiberClosureInclusion (translatedInitial p a) N` (`F̃`), the centre fibre of each blowup (`E_n`), and the total transforms along
`selectedProjection p a n` of the ideal lines of the translated fibres `x = 1 + a`, `y = 1 + a^p`
(`a`, `b`) — proves that each is the image of the corresponding origin class under the Picard
isomorphism `schemePicardPullbackHom (stageTranslationIso p a n).inv`
(lane A1's `picardEquivOfIso`), and derives the class table on every stage of the translated tower
(`strictTransformClasses_translated_tower`).

The kernel transport is the generic `SchemeKernelIdealIsoTransport`; the strict transform of the
whole graph and the closure of the local graph `v = u^m` have the same ideal on the origin tower
(accepted `strictTransformIdeal_eq_local`), which identifies lane A2's `strictKernelLine` with the
kernel line of `closureInclusion`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusTowerTransportClasses

open KltDP.Geometry KltDP.Geometry.SchemeKernelIdealIsoTransport
open FrobeniusGlobalBlowupStages FrobeniusBlowupChartIteration FrobeniusContactTowerSelectedPoint
  FrobeniusTowerTransport FrobeniusTowerTransportCurves FrobeniusGlobalExceptionalSuccessor
  FrobeniusExceptionalFinalConfiguration FrobeniusStrictTransformPicardStep
  FrobeniusStrictTransformClassesTower FrobeniusOldExceptionalLaterStages
  FrobeniusGraphPicardClassTotalTransform FrobeniusStrictTransformClassesFull
  FrobeniusFiberPicard FrobeniusFiberZeroInvertible FrobeniusStrictTransformInvertible
  FrobeniusStrictTransformProductKernel FrobeniusGlobalStrictTransform FrobeniusFiberClosure
  FrobeniusStrictTransformClosure FrobeniusGraphPicardClassFiberClasses
  FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassZeroFiber FrobeniusUnaffectedFibers
  FrobeniusProjectivePoints FrobeniusGraphClosed FrobeniusProjectiveMorphism
  FrobeniusTranslatedCharts ProjectiveProductTranslation ProjectiveProductTranslationFibres
open KltDP.Geometry.ProjectiveLineTranslation

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

/-- The centre of a chart is a maximal ideal (the accepted witness). -/
local instance towerTransportClassesOriginMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-! ## The exceptional curve `E_n` of the translated tower -/

/-- The ideal line of the exceptional curve `E_n` of the translated tower on stage `n + 1`
(the accepted centre-fibre ideal line of the `(n+1)`-st blowup). -/
def translatedStepExceptionalIdealLine (p : ℕ) (a : k) (n : ℕ) :
    InvertibleSheaf (selectedStage p a (n + 1)) :=
  PointBlowupGluing.globalCenterFiberIdealLine ((translatedInitial p a).stage n).chart
    (originPoint (k := k)) ((translatedInitial p a).stage n).center_closed

theorem translatedStepExceptionalIdealLine_obj (p : ℕ) (a : k) (n : ℕ) :
    (translatedStepExceptionalIdealLine p a n).obj =
      schemeKernelIdeal (previousFiberι ((translatedInitial p a).stage n)) := rfl

/-- `E_n` on stage `n + 1` of the translated tower (ideal-sheaf sign convention). -/
def translatedStepExceptionalClass (p : ℕ) (a : k) (n : ℕ) :
    Additive (selectedStage p a (n + 1)).Pic :=
  -Additive.ofMul (translatedStepExceptionalIdealLine p a n).toPic

theorem translatedStepExceptionalClass_eq (p : ℕ) (a : k) (n : ℕ) :
    translatedStepExceptionalClass p a n =
      (schemePicardPullbackHom (stageTranslationIso p a (n + 1)).inv).toAdditive
        (stepExceptionalPicardClass n) :=
  neg_kernelLine_toPic_transport (previousFiberι ((projectiveProductInitial (k := k)).stage n))
    (stageTranslationIso p a (n + 1)) (previousFiberι ((translatedInitial p a).stage n))
    ((translationChartedIso p a).stage n).previousFiberIso (stageTranslationIso_previousFiber p a n)
    (PointBlowupGluing.globalCenterFiberIdeal_isInvertible _ _ _)
    (PointBlowupGluing.globalCenterFiberIdeal_isInvertible _ _ _)

/-! ## The older exceptional curves `C_j` -/

/-- The ideal line of `C_j` on stage `N` of the translated tower. -/
def translatedOldFinalKernelLine (p : ℕ) (a : k) (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    InvertibleSheaf (selectedStage p a N) :=
  kernelLineTransport (oldFinalMap N j h) (stageTranslationIso p a N)
    (finalOldMap (translatedInitial p a) N j h)
    ((translationChartedIso p a).stage j).previousStrictIso (finalOldMap_translation p a N j h)
    (oldFinalKernel_isInvertible N j h)

theorem translatedOldFinalKernelLine_obj (p : ℕ) (a : k) (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    (translatedOldFinalKernelLine p a N j h).obj =
      schemeKernelIdeal (finalOldMap (translatedInitial p a) N j h) := rfl

/-- `C_j` on stage `N` of the translated tower. -/
def translatedOldExceptionalStrictClass (p : ℕ) (a : k) (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    Additive (selectedStage p a N).Pic :=
  -Additive.ofMul (translatedOldFinalKernelLine p a N j h).toPic

theorem translatedOldExceptionalStrictClass_eq (p : ℕ) (a : k) (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    translatedOldExceptionalStrictClass p a N j h =
      (schemePicardPullbackHom (stageTranslationIso p a N).inv).toAdditive
        (oldExceptionalStrictClass N j h) :=
  neg_kernelLine_toPic_transport (oldFinalMap N j h) (stageTranslationIso p a N)
    (finalOldMap (translatedInitial p a) N j h)
    ((translationChartedIso p a).stage j).previousStrictIso (finalOldMap_translation p a N j h)
    (oldFinalKernel_isInvertible N j h) (translatedOldFinalKernelLine p a N j h).property

/-! ## The strict fibre `F̃` -/

/-- The ideal line of the strict transform of the fibre through the centre on stage `N` of the
translated tower. -/
def translatedFiberKernelLine (p : ℕ) (a : k) (N : ℕ) : InvertibleSheaf (selectedStage p a N) :=
  kernelLineTransport (fiberClosureInclusion (projectiveProductInitial (k := k)) N)
    (stageTranslationIso p a N) (fiberClosureInclusion (translatedInitial p a) N)
    (fiberClosureTranslationIso p a N) (fiberClosureTranslationIso_hom p a N)
    (fiberKernel_isInvertible fiberKernel_zero_isInvertible N)

theorem translatedFiberKernelLine_obj (p : ℕ) (a : k) (N : ℕ) :
    (translatedFiberKernelLine p a N).obj =
      schemeKernelIdeal (fiberClosureInclusion (translatedInitial p a) N) := rfl

/-- `F_N` on stage `N` of the translated tower. -/
def translatedFiberClass (p : ℕ) (a : k) (N : ℕ) : Additive (selectedStage p a N).Pic :=
  -Additive.ofMul (translatedFiberKernelLine p a N).toPic

theorem translatedFiberClass_eq (p : ℕ) (a : k) (N : ℕ) :
    translatedFiberClass p a N =
      (schemePicardPullbackHom (stageTranslationIso p a N).inv).toAdditive (fiberClass N) :=
  neg_kernelLine_toPic_transport (fiberClosureInclusion (projectiveProductInitial (k := k)) N)
    (stageTranslationIso p a N) (fiberClosureInclusion (translatedInitial p a) N)
    (fiberClosureTranslationIso p a N) (fiberClosureTranslationIso_hom p a N)
    (fiberKernel_isInvertible fiberKernel_zero_isInvertible N)
    (translatedFiberKernelLine p a N).property

/-! ## The strict transform `B` of the graph -/

/-- On the origin tower the strict transform of the whole graph and the closure of the local graph
`v = u^m` have the same kernel module (accepted `strictTransformIdeal_eq_local`). -/
def strictKernelLocalIso (n m : ℕ) :
    schemeKernelIdeal (strictTransformι (k := k) n (m + n)) ≅
      schemeKernelIdeal (closureInclusion (projectiveProductInitial (k := k)) n m) :=
  eqToIso (congrArg (fun I : (projectiveContactStage (k := k) n).IdealSheafData =>
    schemeKernelIdeal I.gluedTo) (strictTransformIdeal_eq_local n m))

theorem closureKernel_isInvertible (n m : ℕ) :
    KltDP.SheafOfModules.IsInvertible (R := (projectiveContactStage (k := k) n).ringCatSheaf)
      (schemeKernelIdeal (closureInclusion (projectiveProductInitial (k := k)) n m)) :=
  isInvertible_of_iso (strictKernel_isInvertible n m) (strictKernelLocalIso n m)

/-- The kernel line of the closure of the local graph on the origin tower. -/
def closureKernelLine (n m : ℕ) : InvertibleSheaf (projectiveContactStage (k := k) n) :=
  ⟨schemeKernelIdeal (closureInclusion (projectiveProductInitial (k := k)) n m),
    closureKernel_isInvertible n m⟩

theorem closureKernelLine_toPic (n m : ℕ) :
    (closureKernelLine (k := k) n m).toPic = (strictKernelLine n m).toPic :=
  toPic_eq_of_iso _ _ (strictKernelLocalIso n m).symm

/-- The ideal line of the strict transform of the local graph `v = u^m` on stage `n` of the
translated tower. -/
def translatedStrictKernelLine (p : ℕ) (a : k) (n m : ℕ) :
    InvertibleSheaf (selectedStage p a n) :=
  kernelLineTransport (closureInclusion (projectiveProductInitial (k := k)) n m)
    (stageTranslationIso p a n) (closureInclusion (translatedInitial p a) n m)
    (graphClosureTranslationIso p a n m) (graphClosureTranslationIso_hom p a n m)
    (closureKernel_isInvertible n m)

theorem translatedStrictKernelLine_obj (p : ℕ) (a : k) (n m : ℕ) :
    (translatedStrictKernelLine p a n m).obj =
      schemeKernelIdeal (closureInclusion (translatedInitial p a) n m) := rfl

/-- `B` (residual exponent `m`) on stage `n` of the translated tower. -/
def translatedStrictCurveClass (p : ℕ) (a : k) (n m : ℕ) : Additive (selectedStage p a n).Pic :=
  -Additive.ofMul (translatedStrictKernelLine p a n m).toPic

theorem translatedStrictCurveClass_eq (p : ℕ) (a : k) (n m : ℕ) :
    translatedStrictCurveClass p a n m =
      (schemePicardPullbackHom (stageTranslationIso p a n).inv).toAdditive
        (strictCurvePicardClass n m) := by
  rw [strictCurvePicardClass, ← closureKernelLine_toPic]
  exact neg_kernelLine_toPic_transport (closureInclusion (projectiveProductInitial (k := k)) n m)
    (stageTranslationIso p a n) (closureInclusion (translatedInitial p a) n m)
    (graphClosureTranslationIso p a n m) (graphClosureTranslationIso_hom p a n m)
    (closureKernel_isInvertible n m) (translatedStrictKernelLine p a n m).property

/-! ## The fibres `a`, `b`: `x = 1 + a` and `y = 1 + a^p` -/

/-- The accepted embedding of the fibre `x = 1` is the fibre embedding at the point `1`. -/
theorem verticalFiberMorphism_eq_at_one :
    verticalFiberMorphism (k := k) = verticalFiberMorphismAt 1 := by
  apply pullback.hom_ext
  · exact verticalFiberMorphism_fst.trans (verticalFiberMorphismAt_fst 1).symm
  · exact verticalFiberMorphism_snd.trans (verticalFiberMorphismAt_snd 1).symm

theorem verticalFiber_translation_square (p : ℕ) (a : k) :
    (projectiveTranslationIso (a ^ p)).hom ≫ verticalFiberMorphismAt (1 + a) =
      verticalFiberMorphism ≫ (productTranslationIso a (a ^ p)).hom := by
  change projectiveTranslation (a ^ p) ≫ verticalFiberMorphismAt (1 + a) =
    verticalFiberMorphism ≫ productTranslation a (a ^ p)
  rw [verticalFiberMorphism_eq_at_one, verticalFiberMorphismAt_productTranslation]

theorem horizontalFiber_translation_square (p : ℕ) (a : k) :
    (projectiveTranslationIso a).hom ≫ horizontalFiberMorphism (1 + a ^ p) =
      projectiveGraphMorphism 0 ≫ (productTranslationIso a (a ^ p)).hom := by
  change projectiveTranslation a ≫ horizontalFiberMorphism (1 + a ^ p) =
    projectiveGraphMorphism 0 ≫ productTranslation a (a ^ p)
  rw [projectiveGraphMorphism_zero_eq_horizontalFiber, horizontalFiberMorphism_productTranslation]

/-- The ideal line of the fibre `x = 1 + a`. -/
def translatedVerticalIdealLine (p : ℕ) (a : k) : InvertibleSheaf (projectiveProduct k) :=
  kernelLineTransport verticalFiberMorphism (productTranslationIso a (a ^ p))
    (verticalFiberMorphismAt (1 + a)) (projectiveTranslationIso (a ^ p))
    (verticalFiber_translation_square p a) (verticalFiberIdealLine (k := k)).property

theorem translatedVerticalIdealLine_obj (p : ℕ) (a : k) :
    (translatedVerticalIdealLine p a).obj = schemeKernelIdeal (verticalFiberMorphismAt (1 + a)) :=
  rfl

theorem translatedVerticalIdealLine_toPic (p : ℕ) (a : k) :
    (translatedVerticalIdealLine p a).toPic =
      schemePicardPullbackHom (productTranslationIso a (a ^ p)).inv
        (verticalFiberIdealLine (k := k)).toPic :=
  kernelLine_toPic_transport verticalFiberMorphism (productTranslationIso a (a ^ p))
    (verticalFiberMorphismAt (1 + a)) (projectiveTranslationIso (a ^ p))
    (verticalFiber_translation_square p a) (verticalFiberIdealLine (k := k)).property
    (translatedVerticalIdealLine p a).property

/-- The ideal line of the fibre `y = 1 + a^p`. -/
def translatedHorizontalIdealLine (p : ℕ) (a : k) : InvertibleSheaf (projectiveProduct k) :=
  kernelLineTransport (projectiveGraphMorphism 0) (productTranslationIso a (a ^ p))
    (horizontalFiberMorphism (1 + a ^ p)) (projectiveTranslationIso a)
    (horizontalFiber_translation_square p a) (graphIdealLine (k := k) 0).property

theorem translatedHorizontalIdealLine_obj (p : ℕ) (a : k) :
    (translatedHorizontalIdealLine p a).obj =
      schemeKernelIdeal (horizontalFiberMorphism (1 + a ^ p)) := rfl

theorem translatedHorizontalIdealLine_toPic (p : ℕ) (a : k) :
    (translatedHorizontalIdealLine p a).toPic =
      schemePicardPullbackHom (productTranslationIso a (a ^ p)).inv
        (graphIdealLine (k := k) 0).toPic :=
  kernelLine_toPic_transport (projectiveGraphMorphism 0) (productTranslationIso a (a ^ p))
    (horizontalFiberMorphism (1 + a ^ p)) (projectiveTranslationIso a)
    (horizontalFiber_translation_square p a) (graphIdealLine (k := k) 0).property
    (translatedHorizontalIdealLine p a).property

/-- The total transform `a` on stage `n` of the translated tower: the inverse of the class of the
pullback of the ideal of `x = 1 + a`. -/
def translatedFirstFiberTotalClass (p : ℕ) (a : k) (n : ℕ) :
    Additive (selectedStage p a n).Pic :=
  -Additive.ofMul
    (pullbackInvertibleSheaf (selectedProjection p a n) (translatedVerticalIdealLine p a)).toPic

/-- The total transform `b` on stage `n` of the translated tower: the inverse of the class of the
pullback of the ideal of `y = 1 + a^p`. -/
def translatedSecondFiberTotalClass (p : ℕ) (a : k) (n : ℕ) :
    Additive (selectedStage p a n).Pic :=
  -Additive.ofMul
    (pullbackInvertibleSheaf (selectedProjection p a n) (translatedHorizontalIdealLine p a)).toPic

theorem stageTranslationIso_hom_projection' (p : ℕ) (a : k) (n : ℕ) :
    (stageTranslationIso p a n).hom ≫ selectedProjection p a n =
      projectiveContactProjection n ≫ (productTranslationIso a (a ^ p)).hom :=
  stageTranslationIso_hom_projection p a n

theorem translatedFirstFiberTotalClass_eq (p : ℕ) (a : k) (n : ℕ) :
    translatedFirstFiberTotalClass p a n =
      (schemePicardPullbackHom (stageTranslationIso p a n).inv).toAdditive
        (firstFiberTotalClass n) := by
  unfold translatedFirstFiberTotalClass firstFiberTotalClass
  rw [map_neg, ← schemePicardPullbackHom_toPic, ← schemePicardPullbackHom_toPic,
    translatedVerticalIdealLine_toPic]
  change -Additive.ofMul (schemePicardPullbackHom (selectedProjection p a n)
      (schemePicardPullbackHom (productTranslationIso a (a ^ p)).inv
        (verticalFiberIdealLine (k := k)).toPic)) =
    -Additive.ofMul (schemePicardPullbackHom (stageTranslationIso p a n).inv
      (schemePicardPullbackHom (projectiveContactProjection n)
        (verticalFiberIdealLine (k := k)).toPic))
  rw [picardPullback_inv_square (projectiveContactProjection n) (selectedProjection p a n)
    (productTranslationIso a (a ^ p)) (stageTranslationIso p a n)
    (stageTranslationIso_hom_projection' p a n)]

theorem translatedSecondFiberTotalClass_eq (p : ℕ) (a : k) (n : ℕ) :
    translatedSecondFiberTotalClass p a n =
      (schemePicardPullbackHom (stageTranslationIso p a n).inv).toAdditive
        (secondFiberTotalClass n) := by
  unfold translatedSecondFiberTotalClass secondFiberTotalClass graphTotalIdealLine
  rw [map_neg, ← schemePicardPullbackHom_toPic, ← schemePicardPullbackHom_toPic,
    translatedHorizontalIdealLine_toPic]
  change -Additive.ofMul (schemePicardPullbackHom (selectedProjection p a n)
      (schemePicardPullbackHom (productTranslationIso a (a ^ p)).inv
        (graphIdealLine (k := k) 0).toPic)) =
    -Additive.ofMul (schemePicardPullbackHom (stageTranslationIso p a n).inv
      (schemePicardPullbackHom (projectiveContactProjection n)
        (graphIdealLine (k := k) 0).toPic))
  rw [picardPullback_inv_square (projectiveContactProjection n) (selectedProjection p a n)
    (productTranslationIso a (a ^ p)) (stageTranslationIso p a n)
    (stageTranslationIso_hom_projection' p a n)]

/-! ## Total transforms of the exceptional curves and of the fibre -/

/-- The total transform on stage `N` of `E_j` of the translated tower. -/
def translatedTotalExceptionalClass (p : ℕ) (a : k) (N : ℕ) (j : Fin N) :
    Additive (selectedStage p a N).Pic :=
  (schemePicardPullbackHom (between (translatedInitial p a) j.isLt)).toAdditive
    (translatedStepExceptionalClass p a j)

theorem translatedTotalExceptionalClass_eq (p : ℕ) (a : k) (N : ℕ) (j : Fin N) :
    translatedTotalExceptionalClass p a N j =
      (schemePicardPullbackHom (stageTranslationIso p a N).inv).toAdditive
        (totalExceptionalClass N j) := by
  unfold translatedTotalExceptionalClass totalExceptionalClass
  rw [translatedStepExceptionalClass_eq]
  exact (picardPullback_inv_square_toAdditive _ _ _ _
    (stageTranslationIso_hom_between p a j.isLt) _).symm

/-- The total transform on stage `N` of the class of the stage-`0` fibre `y = a^p` of the
translated tower. -/
def translatedFiberZeroTotalClass (p : ℕ) (a : k) (N : ℕ) :
    Additive (selectedStage p a N).Pic :=
  (schemePicardPullbackHom (between (translatedInitial p a) (Nat.zero_le N))).toAdditive
    (translatedFiberClass p a 0)

theorem translatedFiberZeroTotalClass_eq (p : ℕ) (a : k) (N : ℕ) :
    translatedFiberZeroTotalClass p a N =
      (schemePicardPullbackHom (stageTranslationIso p a N).inv).toAdditive
        (fiberZeroTotalClass N) := by
  unfold translatedFiberZeroTotalClass fiberZeroTotalClass fiberTotalClass
  rw [translatedFiberClass_eq]
  exact (picardPullback_inv_square_toAdditive _ _ _ _
    (stageTranslationIso_hom_between p a (Nat.zero_le N)) _).symm

/-! ## The class table of the translated tower -/

/-- `B = (m + N) a + b − Σ_{j<N} E_j^{(N)}` on stage `N` of the translated tower. -/
theorem translatedStrictCurveClass_tower (p : ℕ) (a : k) (N m : ℕ) :
    translatedStrictCurveClass p a N m =
      (m + N) • translatedFirstFiberTotalClass p a N + translatedSecondFiberTotalClass p a N -
        ∑ j : Fin N, translatedTotalExceptionalClass p a N j := by
  rw [translatedStrictCurveClass_eq, translatedFirstFiberTotalClass_eq,
    translatedSecondFiberTotalClass_eq]
  simp_rw [translatedTotalExceptionalClass_eq]
  rw [← map_sum, ← map_nsmul, ← map_add, ← map_sub, strictCurvePicardClass_tower]

/-- `C_j = E_j^{(N)} − E_{j+1}^{(N)}` on stage `N` of the translated tower. -/
theorem translatedOldExceptionalStrictClasses_tower (p : ℕ) (a : k) (N j : ℕ)
    (h : j + 1 + 1 ≤ N) :
    translatedOldExceptionalStrictClass p a N j h =
      translatedTotalExceptionalClass p a N ⟨j, by omega⟩ -
        translatedTotalExceptionalClass p a N ⟨j + 1, by omega⟩ := by
  rw [translatedOldExceptionalStrictClass_eq, translatedTotalExceptionalClass_eq,
    translatedTotalExceptionalClass_eq, ← map_sub, oldExceptionalStrictClasses_tower N j h]

/-- `F_N = F_0^{(N)} − Σ_{j<N} E_j^{(N)}` on stage `N` of the translated tower. -/
theorem translatedFiberClass_tower (p : ℕ) (a : k) (N : ℕ) :
    translatedFiberClass p a N =
      translatedFiberZeroTotalClass p a N -
        ∑ j : Fin N, translatedTotalExceptionalClass p a N j := by
  rw [translatedFiberClass_eq, translatedFiberZeroTotalClass_eq]
  simp_rw [translatedTotalExceptionalClass_eq]
  rw [← map_sum, ← map_sub, fiberClass_tower]

/-- `F_{n+1} = π^* F_n − E_n` on stage `n+1` of the translated tower. -/
theorem translatedFiberClass_succ (p : ℕ) (a : k) (n : ℕ) :
    translatedFiberClass p a (n + 1) =
      (schemePicardPullbackHom ((translatedInitial p a).stepProjection n)).toAdditive
        (translatedFiberClass p a n) - translatedStepExceptionalClass p a n := by
  rw [translatedFiberClass_eq, translatedFiberClass_eq, translatedStepExceptionalClass_eq,
    ← picardPullback_inv_square_toAdditive _ _ _ _ (stageTranslationIso_hom_stepProjection p a n),
    ← map_sub, fiberClass_succ]

/-- The last exceptional curve is its own total transform. -/
theorem translatedTotalExceptionalClass_last (p : ℕ) (a : k) (N : ℕ) :
    translatedTotalExceptionalClass p a (N + 1) (Fin.last N) =
      translatedStepExceptionalClass p a N := by
  rw [translatedTotalExceptionalClass_eq, translatedStepExceptionalClass_eq,
    totalExceptionalClass_last]

/-- **The class table of Proposition 10.1 on every stage `N` of the translated contact tower**
(centre `(a, a^p)`), in `Additive (selectedStage p a N).Pic`, with every class defined from the
translated tower's own curves: `B`, `C_j`, `F` (iteration and one-step relation) and `P`. -/
theorem strictTransformClasses_translated_tower (p : ℕ) (a : k) :
    (∀ N m : ℕ, translatedStrictCurveClass p a N m =
      (m + N) • translatedFirstFiberTotalClass p a N + translatedSecondFiberTotalClass p a N -
        ∑ j : Fin N, translatedTotalExceptionalClass p a N j) ∧
    (∀ (N j : ℕ) (h : j + 1 + 1 ≤ N),
      translatedOldExceptionalStrictClass p a N j h =
        translatedTotalExceptionalClass p a N ⟨j, by omega⟩ -
          translatedTotalExceptionalClass p a N ⟨j + 1, by omega⟩) ∧
    (∀ N : ℕ, translatedFiberClass p a N =
      translatedFiberZeroTotalClass p a N -
        ∑ j : Fin N, translatedTotalExceptionalClass p a N j) ∧
    (∀ n : ℕ, translatedFiberClass p a (n + 1) =
      (schemePicardPullbackHom ((translatedInitial p a).stepProjection n)).toAdditive
        (translatedFiberClass p a n) - translatedStepExceptionalClass p a n) ∧
    (∀ N : ℕ, translatedTotalExceptionalClass p a (N + 1) (Fin.last N) =
      translatedStepExceptionalClass p a N) :=
  ⟨translatedStrictCurveClass_tower p a, translatedOldExceptionalStrictClasses_tower p a,
    translatedFiberClass_tower p a, translatedFiberClass_succ p a,
    translatedTotalExceptionalClass_last p a⟩

/-! ## The transport statements through lane A1's `picardEquivOfIso` -/

open KltDP.Examples.FrobeniusMultiCentreLocusPicard in
/-- Every class of the translated table is the image of the corresponding origin class under
the Picard-group isomorphism `picardEquivOfIso (stageTranslationIso p a N).inv`. -/
theorem translatedClasses_picardEquivOfIso (p : ℕ) (a : k) :
    (∀ N m : ℕ, translatedStrictCurveClass p a N m = Additive.ofMul
      (picardEquivOfIso (stageTranslationIso p a N).inv
        (Additive.toMul (strictCurvePicardClass (k := k) N m)))) ∧
    (∀ (N j : ℕ) (h : j + 1 + 1 ≤ N), translatedOldExceptionalStrictClass p a N j h =
      Additive.ofMul (picardEquivOfIso (stageTranslationIso p a N).inv
        (Additive.toMul (oldExceptionalStrictClass (k := k) N j h)))) ∧
    (∀ N : ℕ, translatedFiberClass p a N = Additive.ofMul
      (picardEquivOfIso (stageTranslationIso p a N).inv
        (Additive.toMul (fiberClass (k := k) N)))) ∧
    (∀ n : ℕ, translatedStepExceptionalClass p a n = Additive.ofMul
      (picardEquivOfIso (stageTranslationIso p a (n + 1)).inv
        (Additive.toMul (stepExceptionalPicardClass (k := k) n)))) ∧
    (∀ (N : ℕ) (j : Fin N), translatedTotalExceptionalClass p a N j = Additive.ofMul
      (picardEquivOfIso (stageTranslationIso p a N).inv
        (Additive.toMul (totalExceptionalClass (k := k) N j)))) ∧
    (∀ N : ℕ, translatedFirstFiberTotalClass p a N = Additive.ofMul
      (picardEquivOfIso (stageTranslationIso p a N).inv
        (Additive.toMul (firstFiberTotalClass (k := k) N)))) ∧
    (∀ N : ℕ, translatedSecondFiberTotalClass p a N = Additive.ofMul
      (picardEquivOfIso (stageTranslationIso p a N).inv
        (Additive.toMul (secondFiberTotalClass (k := k) N)))) :=
  ⟨fun N m => translatedStrictCurveClass_eq p a N m,
    fun N j h => translatedOldExceptionalStrictClass_eq p a N j h,
    fun N => translatedFiberClass_eq p a N,
    fun n => translatedStepExceptionalClass_eq p a n,
    fun N j => translatedTotalExceptionalClass_eq p a N j,
    fun N => translatedFirstFiberTotalClass_eq p a N,
    fun N => translatedSecondFiberTotalClass_eq p a N⟩

/-- The bundle has exactly one universe parameter. -/
theorem strictTransformClasses_translated_tower_universe_check (k : Type u) [Field k] (p : ℕ)
    (a : k) : True := by
  have _ := strictTransformClasses_translated_tower.{u} p a
  have _ := translatedClasses_picardEquivOfIso.{u} p a
  trivial

end KltDP.Examples.FrobeniusTowerTransportClasses

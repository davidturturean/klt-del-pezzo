import KltDP.Geometry.ProjectiveLineIdealLineDegree
import KltDP.Examples.FrobeniusStageExceptionalTable
import KltDP.Examples.FrobeniusOldExceptionalChainRows

/-!
# The row `F̃ · b = 0`, and the extended table (BRIEF16, item 2, partial)

The horizontal fibre `y = 0` of `P¹ × P¹` is disjoint from the graph of the constant map (`y = 1`,
the accepted `projectiveGraphMorphism 0 = horizontalFiberMorphism 1`; the rational points `0`, `1`
of `P¹` are distinct — accepted `point_injective`, which needs `IsAlgClosed k`), so it factors through the graph complement, on which the accepted
`complementGlobalFrameIso` trivialises the graph ideal line. Hence the pullback of `graphIdealLine 0`
along `horizontalFiberMorphism 0` is trivial (`pullbackGraphIdealLine_zero_unitIso`), its exponent is
`0`, and **`F̃ · b = 0`** on every `stageSurface (n+1) hproj` (`fiberStrictPairing_secondFiber_zero`),
unconditionally at stage `1`.

The extended table `f29_intersection_table_extended` collects BRIEF13's table, the `C_j` rows of
BRIEF14 and this row. **Not proved**: `B · a = 1`, `B · b = p`, `F̃ · a = 1` (they are the exponents
`−1`, `−p`, `−1` of `ProjectiveLineIdealLineDegree`; see the record).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusStrictTransformFiberRowsValues

open KltDP.Geometry KltDP.Geometry.ProjectiveLineIdealLineDegree
open FrobeniusGlobalBlowupStages FrobeniusStrictTransformPairing FrobeniusStrictTransformFiberRows
open FrobeniusGraphClosed FrobeniusProjectiveMorphism FrobeniusProjectivePoints
open FrobeniusGraphPicardClassZeroFiber FrobeniusGraphPicardClassTotalTransform
open FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassDiagonal

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The horizontal fibre `y = 0` misses the graph `y = 1` of the constant map. -/
theorem range_horizontalFiber_zero_subset_complement :
    Set.range (horizontalFiberMorphism (0 : k)).base ⊆
      Set.range (graphComplement (k := k) 0).ι.base := by
  rintro _ ⟨s, rfl⟩
  rw [Scheme.Opens.range_ι]
  change (horizontalFiberMorphism (0 : k)).base s ∉
    Set.range (projectiveGraphMorphism (k := k) 0).base
  rintro ⟨t, ht⟩
  rw [projectiveGraphMorphism_zero_eq_horizontalFiber] at ht
  have h := congrArg (secondProjection (k := k)).base ht
  rw [← Scheme.comp_base_apply, ← Scheme.comp_base_apply, horizontalFiberMorphism_snd,
    horizontalFiberMorphism_snd, Scheme.comp_base_apply, Scheme.comp_base_apply,
    Subsingleton.elim ((projectiveSpaceToSpec k 1).base t) (IsLocalRing.closedPoint k),
    Subsingleton.elim ((projectiveSpaceToSpec k 1).base s) (IsLocalRing.closedPoint k)] at h
  exact one_ne_zero (point_injective (k := k) h)

/-- The horizontal fibre `y = 0` inside the graph complement. -/
def horizontalFiberToComplement : projectiveSpace k 1 ⟶ (graphComplement (k := k) 0).toScheme :=
  IsOpenImmersion.lift (graphComplement (k := k) 0).ι (horizontalFiberMorphism (0 : k))
    range_horizontalFiber_zero_subset_complement

theorem horizontalFiberToComplement_ι :
    horizontalFiberToComplement ≫ (graphComplement (k := k) 0).ι = horizontalFiberMorphism (0 : k) :=
  IsOpenImmersion.lift_fac _ _ _

/-- **The pullback of the ideal line of `y = 1` along the fibre `y = 0` is trivial.** -/
def pullbackGraphIdealLine_zero_unitIso :
    (pullbackInvertibleSheaf (horizontalFiberMorphism (0 : k)) (graphIdealLine (k := k) 0)).obj ≅
      _root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf := by
  show (schemeModulePullback (horizontalFiberMorphism (0 : k))).obj
    (schemeKernelIdeal (projectiveGraphMorphism (k := k) 0)) ≅ _
  rw [← horizontalFiberToComplement_ι]
  refine ((schemeModulePullbackCompIso horizontalFiberToComplement
    (graphComplement (k := k) 0).ι).symm.app _) ≪≫ ?_
  refine (schemeModulePullback horizontalFiberToComplement).mapIso
    (complementGlobalFrameIso 0).symm ≪≫ ?_
  exact schemeModulePullbackUnitIso horizontalFiberToComplement

section Rows

variable (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- **`F̃ · b = 0`** on `stageSurface (n+1) hproj`. -/
theorem fiberStrictPairing_secondFiber_zero :
    fiberStrictPairing n hproj (secondFiberTotalClass (n + 1)) = 0 :=
  fiberStrictPairing_secondFiber_of_iso_unit n hproj pullbackGraphIdealLine_zero_unitIso

end Rows

end KltDP.Examples.FrobeniusStrictTransformFiberRowsValues

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusStrictTransformClassesTower
  FrobeniusGraphPicardClassTotalTransform FrobeniusStrictTransformPairing
  FrobeniusOldExceptionalLaterStages FrobeniusOldExceptionalChainRows
  FrobeniusStrictTransformFiberRowsValues FrobeniusStageExceptionalPairing
  FrobeniusStrictTransformPicardStep FrobeniusFiberPicard

/-- **The extended numerical table**: BRIEF13's table of the newest exceptional curve, the rows of
the older exceptional curves `C_j` (`C_j · a = C_j · b = 0`, `C_j · E_i^tot = 0` for `i < j`,
`C_j · C_i = 0` for `i + 2 ≤ j`), and `F̃ · b = 0`. -/
theorem f29_intersection_table_extended (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (h0 : FiberKernelInvertible (k := k) 0) :
    ((∀ j : Fin (n + 1), exceptionalPairing n hproj (totalExceptionalClass (n + 1) j) =
        if j = Fin.last n then -1 else 0) ∧
      exceptionalPairing n hproj (stepExceptionalPicardClass n) = -1 ∧
      exceptionalPairing n hproj (firstFiberTotalClass (n + 1)) = 0 ∧
      exceptionalPairing n hproj (secondFiberTotalClass (n + 1)) = 0 ∧
      (∀ m : ℕ, exceptionalPairing n hproj (strictCurvePicardClass (n + 1) m) = 1) ∧
      (∀ j : Fin n, exceptionalPairing n hproj (oldExceptionalStrictClass (n + 1) j.val (by omega)) =
        if j.succ = Fin.last n then 1 else 0) ∧
      exceptionalPairing n hproj (fiberTotalClass h0 (n + 1)) = 0 ∧
      exceptionalPairing n hproj (fiberPicardClass h0 (n + 1)) = 1) ∧
    (∀ (j : ℕ) (h : j + 2 ≤ n + 1),
      oldExceptionalPairing n hproj j h (firstFiberTotalClass (n + 1)) = 0 ∧
      oldExceptionalPairing n hproj j h (secondFiberTotalClass (n + 1)) = 0 ∧
      (∀ i : Fin (n + 1), i.val < j →
        oldExceptionalPairing n hproj j h (totalExceptionalClass (n + 1) i) = 0) ∧
      (∀ (i : ℕ) (hi : i + 2 ≤ j),
        oldExceptionalPairing n hproj j h (oldExceptionalStrictClass (n + 1) i (by omega)) = 0)) ∧
    fiberStrictPairing n hproj (secondFiberTotalClass (n + 1)) = 0 :=
  ⟨f29_intersection_table k n hproj h0,
    fun j h => ⟨oldExceptionalPairing_firstFiber n hproj j h,
      oldExceptionalPairing_secondFiber n hproj j h,
      fun i hi => oldExceptionalPairing_totalExceptional_of_lt n hproj j h i hi,
      fun i hi => oldExceptionalPairing_oldStrictClass_of_lt n hproj j h i hi⟩,
    fiberStrictPairing_secondFiber_zero n hproj⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_intersection_table_extended_universe_check (k : Type u) [Field k] [IsAlgClosed k]
    (n : ℕ) (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (h0 : FiberKernelInvertible (k := k) 0) : True := by
  have _ := f29_intersection_table_extended.{u} k n hproj h0
  trivial

end KltDP.Examples

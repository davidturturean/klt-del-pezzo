import KltDP.Geometry.PrimeCurveInclusionLift
import KltDP.Examples.FrobeniusStrictTransformPrimeCurves
import KltDP.Examples.FrobeniusStrictTransformClassesTower
import KltDP.Examples.FrobeniusPreviousStrictBlowdown

/-!
# Pairings of the strict transforms of the top stage (BRIEF14, item 3)

On `stageSurface (n + 1) hproj`, lane D's restriction-degree homomorphism paired with the prime
curves of `FrobeniusStrictTransformPrimeCurves`:

* `oldExceptionalPairing n hproj j h = C_j · (−)` for the older exceptional curve `C_j`
  (`j + 2 ≤ n + 1`). `C_j` blown down to stage `j` factors through the closed centre of stage `j`
  (`finalOldMap_comp_between`: through the accepted `strictToFiber` and the centre-fibre square), so
  by the generic `picardRestrictionDegreeHom_pullback_eq_zero` every class pulled back from stage
  `j` (or beyond) pairs to zero with `C_j` (`oldExceptionalPairing_pullback`). Hence the rows
  `C_j · a = 0`, `C_j · b = 0` (the fibre classes are pulled back from stage `0`,
  `class_between`) and `C_j · E_i^tot = 0` for `i < j` (`E_i^tot` is pulled back from stage
  `i + 1 ≤ j`).
* `graphStrictPairing n hproj m = B · (−)` and `fiberStrictPairing n hproj = F̃ · (−)` are defined;
  their rows `B · a`, `B · b`, `F̃ · a`, `F̃ · b` need the isomorphisms `B ≅ P¹`, `F̃ ≅ P¹` (the
  blowdown restricted to the strict transform) and are **not** proved here; the rows
  `C_j · E_j^tot`, `C_j · E_{j+1}^tot`, `C_j · E_i^tot` (`i ≥ j + 2`) and the self-intersections
  need the transversality of the chain or the symmetric pairing (recorded in
  `F29_INTERSECTION_TABLE.md`).

Bundle: `f29_old_exceptional_rows`, with a universe check.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusStrictTransformPairing

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface KltDP.Geometry.PrimeCurveInclusionLift
open KltDP.Geometry.PrimeCurveOfClosedImmersion
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
open FrobeniusStageSurface
open FrobeniusExceptionalFinalConfiguration FrobeniusGlobalExceptionalSuccessor
open FrobeniusPreviousStrictBlowdown FrobeniusStrictTransformClassesTower
open FrobeniusStrictTransformPrimeCurves FrobeniusGraphPicardClassTotalTransform
open FrobeniusStrictTransformPicardStep FrobeniusGlobalStrictTransform FrobeniusFiberClosure

variable {k : Type u} [Field k]

/-- The origin ideal is maximal (accepted), as a local instance. -/
local instance pairingOriginIdealMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  centerIdeal_isMaximal

section Factor

variable (A : PlaneChartedScheme k)

/-- **`C_j ⊆ stage N` blown down to stage `j` factors through the closed centre of stage `j`**:
through the accepted blowdown `strictToFiber` onto the exceptional fibre of stage `j+1` and the
centre-fibre pullback square. -/
theorem finalOldMap_comp_between (N j : ℕ) (h : j + 2 ≤ N) :
    finalOldMap A N j h ≫ between A (show j ≤ N by omega) =
      (strictToFiber (A.stage j) ≫
        PointBlowupGluing.globalCenterFiberToCenter (A.stage j).chart (originPoint (k := k))
          (A.stage j).center_closed) ≫
        PointBlowupGluing.closedCenterInclusion (A.stage j).chart (originPoint (k := k)) := by
  have h1 : between A (show j ≤ N by omega) =
      between A h ≫ between A (show j ≤ j + 2 by omega) :=
    (between_comp A (show j ≤ j + 2 by omega) h).symm
  have h2 : between A (show j ≤ j + 2 by omega) =
      A.stepProjection (j + 1) ≫ A.stepProjection j := by
    have e1 : between A (show j + 1 ≤ j + 2 by omega) = A.stepProjection (j + 1) :=
      between_step A (j + 1)
    have e2 : between A (show j ≤ j + 1 by omega) = A.stepProjection j := between_step A j
    rw [← between_comp A (show j ≤ j + 1 by omega) (show j + 1 ≤ j + 2 by omega), e1, e2]
  have h3 : previousStrictι (A.stage j) ≫ A.stepProjection (j + 1) =
      strictToFiber (A.stage j) ≫ previousFiberι (A.stage j) :=
    (strictToFiber_ι (A.stage j)).symm
  rw [h1, ← Category.assoc, finalOldMap_projection, h2, ← Category.assoc, h3, Category.assoc,
    Category.assoc]
  congr 1
  exact pullback.condition

end Factor

section Classes

/-- A family of classes on the tower propagating by pullback along the step projections is pulled
back along `between`. -/
theorem class_between {c : ∀ N : ℕ, Additive (projectiveContactStage (k := k) N).Pic}
    (hc : ∀ N, c (N + 1) =
      (schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection N)).toAdditive
        (c N))
    {j N : ℕ} (h : j ≤ N) :
    c N = (schemePicardPullbackHom (between (projectiveProductInitial (k := k)) h)).toAdditive
      (c j) := by
  induction N, h using Nat.le_induction with
  | base =>
    rw [between_refl, schemePicardPullbackHom_id]
    rfl
  | succ N hjN ih =>
    rw [hc, ih, between_succ (projectiveProductInitial (k := k)) hjN, schemePicardPullbackHom_comp]
    rfl

/-- The first fibre class of stage `N` is pulled back from stage `j ≤ N`. -/
theorem firstFiberTotalClass_between {j N : ℕ} (h : j ≤ N) :
    firstFiberTotalClass (k := k) N =
      (schemePicardPullbackHom (between (projectiveProductInitial (k := k)) h)).toAdditive
        (firstFiberTotalClass j) :=
  class_between (c := fun N => firstFiberTotalClass (k := k) N) firstFiberTotalClass_succ h

/-- The second fibre class of stage `N` is pulled back from stage `j ≤ N`. -/
theorem secondFiberTotalClass_between {j N : ℕ} (h : j ≤ N) :
    secondFiberTotalClass (k := k) N =
      (schemePicardPullbackHom (between (projectiveProductInitial (k := k)) h)).toAdditive
        (secondFiberTotalClass j) :=
  class_between (c := fun N => secondFiberTotalClass (k := k) N) secondFiberTotalClass_succ h

end Classes

section Pairing

variable [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- **The pairing `C_j · (−)`** of the older exceptional curve `C_j` (`j + 2 ≤ n + 1`) with the
Picard classes of stage `n+1`. -/
abbrev oldExceptionalPairing (j : ℕ) (h : j + 2 ≤ n + 1) :
    Additive (projectiveContactStage (k := k) (n + 1)).Pic →+ ℤ :=
  (stageSurface (n + 1) hproj).picardRestrictionDegreeHom (oldExceptionalPrimeCurve n hproj j h)

/-- **The pairing `B · (−)`** of the strict transform of the graph (residual exponent `m`). -/
abbrev graphStrictPairing (m : ℕ) : Additive (projectiveContactStage (k := k) (n + 1)).Pic →+ ℤ :=
  (stageSurface (n + 1) hproj).picardRestrictionDegreeHom (graphStrictPrimeCurve n hproj m)

/-- **The pairing `F̃ · (−)`** of the strict transform of the fibre. -/
abbrev fiberStrictPairing : Additive (projectiveContactStage (k := k) (n + 1)).Pic →+ ℤ :=
  (stageSurface (n + 1) hproj).picardRestrictionDegreeHom (fiberStrictPrimeCurve n hproj)

/-- **`C_j · (π ∘ ρ)^*q = 0`** for every class `q` pulled back through stage `j`. -/
theorem oldExceptionalPairing_pullback_comp (j : ℕ) (h : j + 2 ≤ n + 1) {Y : Scheme.{u}}
    (ρ : projectiveContactStage (k := k) j ⟶ Y) (q : Additive Y.Pic) :
    oldExceptionalPairing n hproj j h
      ((schemePicardPullbackHom
        (between (projectiveProductInitial (k := k)) (show j ≤ n + 1 by omega) ≫ ρ)).toAdditive
          q) = 0 := by
  letI : Field (planeRing k ⧸ (originPoint (k := k)).asIdeal) := Ideal.Quotient.field _
  exact picardRestrictionDegreeHom_pullback_eq_zero (oldExceptionalPrimeCurve n hproj j h)
    (finalOldMap (projectiveProductInitial (k := k)) (n + 1) j h) rfl
    (between (projectiveProductInitial (k := k)) (show j ≤ n + 1 by omega) ≫ ρ)
    (strictToFiber ((projectiveProductInitial (k := k)).stage j) ≫
      PointBlowupGluing.globalCenterFiberToCenter
        ((projectiveProductInitial (k := k)).stage j).chart (originPoint (k := k))
        ((projectiveProductInitial (k := k)).stage j).center_closed)
    (PointBlowupGluing.closedCenterInclusion
      ((projectiveProductInitial (k := k)).stage j).chart (originPoint (k := k)) ≫ ρ)
    (by rw [← Category.assoc, finalOldMap_comp_between, Category.assoc]) q

/-- **`C_j · π^*q = 0`** for every Picard class `q` of stage `j`. -/
theorem oldExceptionalPairing_pullback (j : ℕ) (h : j + 2 ≤ n + 1)
    (q : Additive (projectiveContactStage (k := k) j).Pic) :
    oldExceptionalPairing n hproj j h
      ((schemePicardPullbackHom
        (between (projectiveProductInitial (k := k)) (show j ≤ n + 1 by omega))).toAdditive q) =
      0 := by
  have := oldExceptionalPairing_pullback_comp n hproj j h (𝟙 _) q
  rwa [Category.comp_id] at this

/-- **`C_j · a = 0`**. -/
theorem oldExceptionalPairing_firstFiber (j : ℕ) (h : j + 2 ≤ n + 1) :
    oldExceptionalPairing n hproj j h (firstFiberTotalClass (n + 1)) = 0 := by
  rw [firstFiberTotalClass_between (show j ≤ n + 1 by omega)]
  exact oldExceptionalPairing_pullback n hproj j h _

/-- **`C_j · b = 0`**. -/
theorem oldExceptionalPairing_secondFiber (j : ℕ) (h : j + 2 ≤ n + 1) :
    oldExceptionalPairing n hproj j h (secondFiberTotalClass (n + 1)) = 0 := by
  rw [secondFiberTotalClass_between (show j ≤ n + 1 by omega)]
  exact oldExceptionalPairing_pullback n hproj j h _

/-- **`C_j · E_i^tot = 0` for `i < j`**: the total class of an exceptional curve born before `C_j`
is pulled back from stage `i + 1 ≤ j`. -/
theorem oldExceptionalPairing_totalExceptional_of_lt (j : ℕ) (h : j + 2 ≤ n + 1)
    (i : Fin (n + 1)) (hi : i.val < j) :
    oldExceptionalPairing n hproj j h (totalExceptionalClass (n + 1) i) = 0 := by
  rw [totalExceptionalClass, ← between_comp (projectiveProductInitial (k := k))
    (show i.val + 1 ≤ j by omega) (show j ≤ n + 1 by omega)]
  exact oldExceptionalPairing_pullback_comp n hproj j h _ _

end Pairing

end KltDP.Examples.FrobeniusStrictTransformPairing

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusStrictTransformClassesTower
  FrobeniusGraphPicardClassTotalTransform FrobeniusStrictTransformPairing

/-- **The rows of the older exceptional curves `C_j` against the pulled-back classes**: on
`stageSurface (n+1) hproj`, `C_j · a = C_j · b = 0` and `C_j · E_i^tot = 0` for `i < j`. -/
theorem f29_old_exceptional_rows (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (j : ℕ) (h : j + 2 ≤ n + 1) :
    oldExceptionalPairing n hproj j h (firstFiberTotalClass (n + 1)) = 0 ∧
    oldExceptionalPairing n hproj j h (secondFiberTotalClass (n + 1)) = 0 ∧
    ∀ i : Fin (n + 1), i.val < j →
      oldExceptionalPairing n hproj j h (totalExceptionalClass (n + 1) i) = 0 :=
  ⟨oldExceptionalPairing_firstFiber n hproj j h, oldExceptionalPairing_secondFiber n hproj j h,
    fun i hi => oldExceptionalPairing_totalExceptional_of_lt n hproj j h i hi⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_old_exceptional_rows_universe_check (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (j : ℕ) (h : j + 2 ≤ n + 1) : True := by
  have _ := f29_old_exceptional_rows.{u} k n hproj j h
  trivial

end KltDP.Examples

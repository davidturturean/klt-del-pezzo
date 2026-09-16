import KltDP.Examples.FrobeniusSpecialFiberCharts
import KltDP.Examples.FrobeniusSpecialFiberTower

/-!
# Bundle: the complete scheme-theoretic fibre on a contact tower (F29 clause 5, proved part)

`f29_special_fiber` collects, for a field `k`, the tower at `(a, a^p)` after `q + 1` blowups:

1. chart level (all stages `n`): the pullback of the fibre equation `v = 0` to the selected chart is
   `u^n · v`; the total fibre ideal is `(u)^n · (v)`; its exceptional saturation is the strict fibre;
   on the second Rees chart of the following blowup it is `(u/v)^n · v^(n+1)` (older exceptional
   curve with multiplicity `n`, newest with multiplicity `n + 1`); the strict fibre is its own
   transform;
2. the complete scheme-theoretic fibre `specialFiber p a (q+1)` (pullback of the horizontal fibre
   `y = a^p`) is a closed subscheme of the tower, a literal pullback, and its support is the strict
   fibre together with the exceptional locus; every final exceptional component `C_j`, `P` and the
   strict fibre lie in it;
3. the strict fibre of the tower is a closed integral curve, its centre point lies on `P`, and it
   misses every `C_j`.

Not included (see `F29_SPECIAL_FIBER.md`): the whole-stage equality of effective Cartier divisors and
the Picard relation `b = [F] + Σ j [C_j] + p [P]`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples

open KltDP.Geometry KltDP.Geometry.AffineBlowup FrobeniusBlowupContact FrobeniusBlowupChartIteration
  FrobeniusExceptionalSuccessorChart FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint
  FrobeniusExceptionalFinalConfiguration FrobeniusGraphPicardClassZeroFiber FrobeniusFiberClosure
  FrobeniusSpecialFiberCharts FrobeniusSpecialFiberTower

/-- The complete scheme-theoretic fibre on the contact tower: the clauses proved. -/
theorem f29_special_fiber (k : Type u) [Field k] (p : ℕ) (a : k) (q : ℕ) :
    -- (1) chart level
    (∀ n : ℕ, stageSubstitution (k := k) n vCoord = uCoord ^ n * vCoord) ∧
    (∀ n : ℕ, Ideal.map (stageSubstitution (k := k) n) (Ideal.span {vCoord}) =
        Ideal.span {uCoord (k := k)} ^ n * Ideal.span {vCoord}) ∧
    (∀ (n : ℕ) (f : planeRing k),
        (∃ j : ℕ, uCoord ^ j * f ∈ Ideal.span {stageSubstitution n vCoord}) ↔
          f ∈ Ideal.span {vCoord (k := k)}) ∧
    (∀ n : ℕ, chartBaseMap centerIdeal centerV (stageSubstitution (k := k) n vCoord) =
        oldRatio (k := k) ^ n * vEquation (k := k) ^ (n + 1)) ∧
    (∀ n : ℕ, fiberCurve (k := k) ≫ stageProjection n = fiberCurve) ∧
    -- (2) the special fibre of the tower
    IsClosedImmersion (specialFiberι p a (q + 1)) ∧
    IsPullback (specialFiberι p a (q + 1)) (specialFiberToLine p a (q + 1))
      (selectedProjection p a (q + 1)) (horizontalFiberMorphism (a ^ p)) ∧
    (specialFiberSupport p a (q + 1) =
      Set.range (fiberClosureInclusion (translatedInitial p a) (q + 1)).base ∪
        exceptionalLocus p a (q + 1)) ∧
    (∀ idx : FinalIndex.{0} q,
        finalSupport (translatedInitial p a) q idx ⊆ specialFiberSupport p a (q + 1)) ∧
    (Set.range (fiberClosureInclusion (translatedInitial p a) (q + 1)).base ⊆
      specialFiberSupport p a (q + 1)) ∧
    -- (3) the strict fibre of the tower
    IsIntegral (liftedFiberClosure (translatedInitial p a) (q + 1)) ∧
    ((fiberClosureInclusion (translatedInitial p a) (q + 1)).base
        (fiberContactPoint (translatedInitial p a) (q + 1)) ∈
      finalSupport (translatedInitial p a) q (Sum.inr PUnit.unit : FinalIndex.{0} q)) ∧
    (∀ j : Fin q,
        Disjoint (Set.range (fiberClosureInclusion (translatedInitial p a) (q + 1)).base)
          (finalSupport (translatedInitial p a) q (Sum.inl j : FinalIndex.{0} q))) :=
  ⟨fun n => stageFiberEquation n,
    fun n => stageFiberIdeal n,
    fun n f => stageFiberEquation_saturation n f,
    fun n => vChart_stageFiberEquation n,
    fun n => stageSubstitution_fiber_strict n,
    specialFiberι_isClosedImmersion p a (q + 1),
    specialFiber_isPullback p a (q + 1),
    specialFiberSupport_eq_union p a (q + 1),
    fun idx => (finalSupport_subset_exceptionalLocus p a q idx).trans
      (exceptionalLocus_subset_specialFiber p a (q + 1)),
    fiberClosure_subset_specialFiber p a (q + 1),
    liftedFiberClosure_isIntegral (translatedInitial p a) (q + 1),
    fiberClosure_terminal_mem_newestFiber (translatedInitial p a) q,
    fun j => fiberClosure_disjoint_finalSupport (translatedInitial p a) q j⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_special_fiber_universe_check (k : Type u) [Field k] (p : ℕ) (a : k) (q : ℕ) : True := by
  have _ := f29_special_fiber.{u} k p a q
  trivial

end KltDP.Examples

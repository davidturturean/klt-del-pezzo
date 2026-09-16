import KltDP.Examples.FrobeniusTranslatedCharts
import KltDP.Examples.FrobeniusGraphPicardClassMixedOverlap

/-!
# The point at infinity of the projective line

The accepted `projectiveSpace k 1` is covered by the two polynomial charts `polynomialChartMap k 0`
(the finite line `A¹ = chartOpen k 0`) and `polynomialChartMap k 1`. The point `∞ = [0:1]` is the
parameter `0` of the second chart: as a rational point `infinityMorphism` (a section of
`projectiveSpaceToSpec`) and as the scheme point `infinityPoint`. It is not on the finite line
(`infinityPoint_not_mem_chart`), the finite rational points `[1:c]` are (`point_mem_chart`), and
`P¹ ∖ A¹ = {∞}` as scheme points (`eq_infinityPoint_of_not_mem_chart`): a point off the finite line
lies on the second chart at a prime containing the coordinate `X` (accepted
`polynomialChart_mem_other_iff`), and the only such prime of `k[X]` is `(X)`
(`eq_parameterSchemePoint_zero_of_X_mem`, from the maximality of the kernel of evaluation at `0`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.ProjectiveLinePointAtInfinity

open KltDP.Geometry ProjectiveLineComparison FrobeniusProjectivePoints FrobeniusGraphContact
  FrobeniusGraphStalkContact FrobeniusGraphPicardClassPowerCharts
  FrobeniusGraphPicardClassMixedOverlap FrobeniusTranslatedCharts

variable {k : Type u} [Field k]

/-- The point `∞ = [0:1]`, as the parameter `0` of the second polynomial chart. -/
def infinityMorphism : Spec (CommRingCat.of k) ⟶ projectiveSpace k 1 :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ≫ polynomialChartMap k 1

theorem evalRingHom_zero_comp_C :
    (Polynomial.evalRingHom (0 : k)).comp Polynomial.C = RingHom.id k := by
  ext r
  simp

/-- `∞` is a rational point: a section of the structure morphism. -/
theorem infinityMorphism_over_base :
    infinityMorphism ≫ projectiveSpaceToSpec k 1 = 𝟙 (Spec (CommRingCat.of k)) := by
  rw [infinityMorphism, Category.assoc, polynomialChartMap_structureMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, evalRingHom_zero_comp_C, CommRingCat.ofHom_id, Spec.map_id]

/-- The point at infinity of the projective line. -/
def infinityPoint : projectiveSpace k 1 :=
  (polynomialChartMap k 1).base (parameterSchemePoint (0 : k))

theorem fieldMorphismPoint_infinityMorphism :
    fieldMorphismPoint (infinityMorphism (k := k)) = infinityPoint := by
  change (polynomialChartMap k 1).base
    (fieldMorphismPoint (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))) = _
  rw [polynomialEvaluation_point]
  rfl

theorem X_mem_parameterPointIdeal_zero :
    (Polynomial.X : Polynomial k) ∈ parameterPointIdeal (0 : k) := by
  have h : (Polynomial.X : Polynomial k) = Polynomial.X - Polynomial.C 0 := by simp
  rw [h]
  exact Ideal.subset_span (Set.mem_singleton _)

theorem otherIndex_one : otherIndex (1 : Fin 2) = 0 := rfl

/-- `∞` is not on the finite line. -/
theorem infinityPoint_not_mem_chart : infinityPoint (k := k) ∉ chartOpen k 0 := by
  intro hmem
  have h := polynomialChart_mem_other_iff (k := k) 1 (parameterSchemePoint (0 : k))
  rw [otherIndex_one] at h
  exact (h.mp hmem) X_mem_parameterPointIdeal_zero

/-- The finite rational point `[1:c]` is the parameter `c` of the finite chart. -/
theorem point_eq_chart (c : k) :
    FrobeniusProjectivePoints.point c = (polynomialChartMap k 0).base (parameterSchemePoint c) := by
  rw [FrobeniusProjectivePoints.point, ← polynomialChartMap_evaluation]
  change (polynomialChartMap k 0).base
    (fieldMorphismPoint (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c)))) = _
  rw [polynomialEvaluation_point]

/-- The finite rational points lie on the finite line. -/
theorem point_mem_chart (c : k) : FrobeniusProjectivePoints.point c ∈ chartOpen k 0 := by
  rw [point_eq_chart]
  have h : (polynomialChartMap k 0).base (parameterSchemePoint c) ∈
      (polynomialChartMap k 0).opensRange := ⟨_, rfl⟩
  rwa [polynomialChartMap_opensRange] at h

theorem infinityPoint_ne_point (c : k) : infinityPoint (k := k) ≠ FrobeniusProjectivePoints.point c :=
  fun h => infinityPoint_not_mem_chart (h ▸ point_mem_chart c)

/-- The kernel of evaluation at `0` is the origin ideal `(X)`. -/
theorem ker_evalRingHom_zero :
    RingHom.ker (Polynomial.evalRingHom (0 : k)) = parameterPointIdeal (0 : k) := by
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker] at hf
    have hX : (Polynomial.X : Polynomial k) ∣ f := by
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
      exact hf
    obtain ⟨g, hg⟩ := hX
    rw [hg]
    exact (parameterPointIdeal 0).mul_mem_right g X_mem_parameterPointIdeal_zero
  · rw [parameterPointIdeal, Ideal.span_le]
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst hf
    rw [SetLike.mem_coe, RingHom.mem_ker]
    simp

/-- The only prime of the parameter line containing `X` is the origin. -/
theorem eq_parameterSchemePoint_zero_of_X_mem (q : PrimeSpectrum (Polynomial k))
    (hq : (Polynomial.X : Polynomial k) ∈ q.asIdeal) : q = parameterSchemePoint (0 : k) := by
  have hker : RingHom.ker (Polynomial.evalRingHom (0 : k)) ≤ q.asIdeal := by
    rw [ker_evalRingHom_zero, parameterPointIdeal, Ideal.span_le]
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst hf
    simpa using hq
  have hmax : (RingHom.ker (Polynomial.evalRingHom (0 : k))).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (fun r => ⟨Polynomial.C r, by simp⟩)
  have heq : RingHom.ker (Polynomial.evalRingHom (0 : k)) = q.asIdeal :=
    hmax.eq_of_le q.isPrime.ne_top hker
  exact PrimeSpectrum.ext (heq.symm.trans ker_evalRingHom_zero)

/-- **`P¹ ∖ A¹ = {∞}`**: every point off the finite line is the point at infinity. -/
theorem eq_infinityPoint_of_not_mem_chart (y : projectiveSpace k 1) (hy : y ∉ chartOpen k 0) :
    y = infinityPoint := by
  obtain ⟨z, hz⟩ := (polynomialAffineCover k).covers y
  have key : ∀ i : Fin 2, (polynomialChartMap k i).base z = y → y = infinityPoint := by
    intro i hi
    have hi2 : i = 0 ∨ i = 1 := by fin_cases i <;> decide
    rcases hi2 with rfl | rfl
    · exfalso
      apply hy
      rw [← hi]
      have h : (polynomialChartMap k 0).base z ∈ (polynomialChartMap k 0).opensRange := ⟨z, rfl⟩
      rwa [polynomialChartMap_opensRange] at h
    · have h := polynomialChart_mem_other_iff (k := k) 1 z
      rw [otherIndex_one, hi] at h
      have hX : (Polynomial.X : Polynomial k) ∈ z.asIdeal := by
        by_contra hX
        exact hy (h.mpr hX)
      rw [← hi, eq_parameterSchemePoint_zero_of_X_mem z hX]
      rfl
  exact key _ hz

end KltDP.Examples.ProjectiveLinePointAtInfinity

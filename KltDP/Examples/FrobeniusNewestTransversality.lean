import KltDP.Examples.FrobeniusClosureNewestUnique

/-!
# Transversality at the contact points with the newest exceptional curve

On an arbitrary charted plane `A`, the newest exceptional curve `P` of stage `n + 1` is, in the selected
Rees chart, the line `u = 0` (`chart_mem_previousFiber_iff`): its local equation is the exceptional
coordinate `chartU`. The terminal closure of the graph meets `P` only in its contact point (BRIEF10) and
there the exceptional equation has contact length one on the closure — this is the accepted-form
statement `closure_exceptional_contact_length A n 0` (`FrobeniusClosureContact`), restated as
`closure_terminal_exceptional_contact_length`.

For the strict fibre the same machinery is built here: the fibre line `v = 0` in Rees coordinates
(`fiberCurveMap : u ↦ t, w ↦ 0`, `fiberCurveChartMorphism`), the germ of a Rees-chart section along the
fibre (`fiberIntersectionGerm`), the stalk of the strict fibre at its centre point identified with the
accepted curve stalk through the open chart `fiberResidualToClosure` (`fiberContactStalkEquiv`), the
germs on the strict fibre (`fiberContactGerm`, `fiberContactGerm_pullback`) and the contact length
`fiberClosure_exceptional_contact_length : … = 1`. Both lengths are `Module.length` of the curve stalk
modulo the pulled equation of `P`, the form used by the accepted `FrobeniusGraphStalkContact`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusNewestTransversality

open KltDP.Geometry FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusBlowupIncidence
  FrobeniusGlobalBlowupStages FrobeniusStrictTransformClosure
  FrobeniusStageComplement.PlaneChartedScheme FrobeniusGlobalExceptionalSuccessor
  FrobeniusClosureContact FrobeniusFiberClosure FrobeniusClosureNewestUnique

variable {k : Type u} [Field k]

/-! ## The newest exceptional curve is `u = 0` in the selected chart -/

theorem chartSubstitution_comap_eq_center_iff (y : plane k) :
    Ideal.comap (chartSubstitution (k := k)) y.asIdeal = centerIdeal ↔ uCoord ∈ y.asIdeal := by
  constructor
  · intro h
    have hu : uCoord (k := k) ∈ Ideal.comap chartSubstitution y.asIdeal := by
      rw [h]
      exact Ideal.subset_span (Set.mem_insert _ _)
    rw [Ideal.mem_comap, chartSubstitution_u] at hu
    exact hu
  · intro hu
    letI : (centerIdeal (k := k)).IsMaximal := centerIdeal_isMaximal
    refine (Ideal.IsMaximal.eq_of_le inferInstance (Ideal.comap_ne_top _ y.isPrime.ne_top) ?_).symm
    rw [centerIdeal, Ideal.span_le]
    rintro r hr
    rcases hr with rfl | rfl
    · rw [SetLike.mem_coe, Ideal.mem_comap, chartSubstitution_u]
      exact hu
    · rw [SetLike.mem_coe, Ideal.mem_comap, chartSubstitution_v]
      exact y.asIdeal.mul_mem_right _ hu

/-- In the selected chart of stage `n + 1`, the newest exceptional curve is the line `u = 0`. -/
theorem chart_mem_previousFiber_iff (A : PlaneChartedScheme k) (n : ℕ) (y : plane k) :
    (A.stage (n + 1)).chart.base y ∈ Set.range (previousFiberι (A.stage n)).base ↔
      uCoord ∈ y.asIdeal := by
  rw [mem_previousFiber_iff]
  have h1 : (A.stepProjection n).base ((A.stage (n + 1)).chart.base y) =
      (A.stage n).chart.base (coordinateBlowdown.base y) := by
    rw [← Scheme.comp_base_apply, ← Scheme.comp_base_apply]
    change ((A.stage n).nextChart ≫ (A.stage n).nextProjection).base y = _
    rw [PlaneChartedScheme.nextChart_projection]
  rw [h1, (A.stage n).chart.isOpenEmbedding.injective.eq_iff, coordinateBlowdown_eq]
  change PrimeSpectrum.comap (chartSubstitution (k := k)) y = originPoint ↔ _
  rw [← chartSubstitution_comap_eq_center_iff]
  constructor
  · intro h
    exact congrArg PrimeSpectrum.asIdeal h
  · intro h
    exact PrimeSpectrum.ext h

/-! ## The graph: the terminal statement -/

/-- At the terminal stage the exceptional equation has contact length one on the closure, i.e. the
terminal closure of the graph meets the newest exceptional curve transversally at its contact point. -/
theorem closure_terminal_exceptional_contact_length (A : PlaneChartedScheme k) (n : ℕ) :
    Module.length (closureContactStalk A (n + 1) 0)
      (closureContactStalk A (n + 1) 0 ⧸ Ideal.span {closureContactGerm A n 0 chartU}) = 1 :=
  closure_exceptional_contact_length A n 0

/-! ## The strict fibre -/

/-- The fibre line `v = 0` in Rees-chart coordinates: `u ↦ t`, `w ↦ 0`. -/
def fiberCurveMap : reesChartRing k →+* Polynomial k :=
  (Polynomial.evalRingHom (0 : Polynomial k)).comp (chartPolynomialEquiv (k := k)).toRingHom

@[simp] theorem fiberCurveMap_u : fiberCurveMap (chartU (k := k)) = Polynomial.X := by
  simp [fiberCurveMap, uCoord]

theorem fiberCurveMap_eq_residualCurveMap_u :
    fiberCurveMap (chartU (k := k)) = residualCurveMap 0 chartU := by
  rw [fiberCurveMap_u, residualCurveMap_u]

/-- The fibre line as a morphism into the Rees chart. -/
def fiberCurveChartMorphism : Spec (CommRingCat.of (Polynomial k)) ⟶
    Spec (CommRingCat.of (reesChartRing k)) :=
  Spec.map (CommRingCat.ofHom fiberCurveMap)

/-- It is the fibre `v = 0` of the polynomial plane followed by the accepted chart coordinates. -/
theorem fiberCurve_coordinateChartIso :
    fiberCurve ≫ coordinateChartIso.hom = fiberCurveChartMorphism (k := k) := by
  change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : Polynomial k))) ≫
    Spec.map (CommRingCat.ofHom (chartPolynomialEquiv (k := k)).toRingHom) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- The point of the Rees chart at the centre of the fibre. -/
def fiberPointInChart : Spec (CommRingCat.of (reesChartRing k)) :=
  (fiberCurveChartMorphism (k := k)).base curvePoint

/-- The germ of a Rees-chart section along the fibre, at its centre. -/
def fiberIntersectionGerm (s : reesChartRing k) : curveStalk k :=
  StructureSheaf.toStalk (Polynomial k) curvePoint (fiberCurveMap s)

theorem fiberIntersectionGerm_pullback (s : reesChartRing k) :
    (fiberCurveChartMorphism (k := k)).stalkMap curvePoint
      (StructureSheaf.toStalk (reesChartRing k) (fiberPointInChart (k := k)) s) =
        fiberIntersectionGerm s :=
  AlgebraicGeometry.stalkMap_toStalk_apply _ _ _

theorem fiberIntersectionGerm_u : fiberIntersectionGerm (chartU (k := k)) = intersectionGerm 0 chartU := by
  rw [fiberIntersectionGerm, intersectionGerm, fiberCurveMap_eq_residualCurveMap_u]

variable (A : PlaneChartedScheme k)

/-- The structure-sheaf stalk of the strict fibre at its centre point. -/
abbrev fiberContactStalk (n : ℕ) :=
  (liftedFiberClosure A n).presheaf.stalk (fiberContactPoint A n)

/-- The chart's stalk map identifies it with the accepted curve stalk. -/
def fiberContactStalkEquiv (n : ℕ) : fiberContactStalk A n ≃+* curveStalk k :=
  (asIso ((fiberResidualToClosure A n).stalkMap curvePoint)).commRingCatIsoToRingEquiv

/-- The germ of a Rees-chart section on the strict fibre of stage `n + 1`. -/
def fiberContactGerm (n : ℕ) (s : reesChartRing k) : fiberContactStalk A (n + 1) :=
  (fiberContactStalkEquiv A (n + 1)).symm (fiberIntersectionGerm s)

@[simp] theorem fiberContactStalkEquiv_germ (n : ℕ) (s : reesChartRing k) :
    fiberContactStalkEquiv A (n + 1) (fiberContactGerm A n s) = fiberIntersectionGerm s :=
  (fiberContactStalkEquiv A (n + 1)).apply_symm_apply _

theorem fiberContactGerm_pullback (n : ℕ) (s : reesChartRing k) :
    (fiberResidualToClosure A (n + 1)).stalkMap curvePoint (fiberContactGerm A n s) =
      (fiberCurveChartMorphism (k := k)).stalkMap curvePoint
        (StructureSheaf.toStalk (reesChartRing k) (fiberPointInChart (k := k)) s) := by
  change fiberContactStalkEquiv A (n + 1) (fiberContactGerm A n s) = _
  rw [fiberContactStalkEquiv_germ, fiberIntersectionGerm_pullback]

/-- **Transversality of the strict fibre and the newest exceptional curve**: the exceptional equation
has contact length one on the strict fibre at its centre point. -/
theorem fiberClosure_exceptional_contact_length (n : ℕ) :
    Module.length (fiberContactStalk A (n + 1))
      (fiberContactStalk A (n + 1) ⧸ Ideal.span {fiberContactGerm A n chartU}) = 1 := by
  rw [FrobeniusGraphStalkContact.quotient_span_length_eq_of_ringEquiv
    (fiberContactStalkEquiv A (n + 1)), fiberContactStalkEquiv_germ, fiberIntersectionGerm_u]
  exact exceptional_stalk_quotient_length 0

end KltDP.Examples.FrobeniusNewestTransversality

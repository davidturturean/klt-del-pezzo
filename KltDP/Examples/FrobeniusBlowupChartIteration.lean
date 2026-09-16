import KltDP.Examples.FrobeniusBlowupIncidence

/-!
# Iteration of the selected actual point-blowup charts

The polynomial plane is identified with the selected actual Rees chart by
the previously proved ring equivalence. Its morphism to the Rees Proj is
an open immersion, and its projection is the coordinate map `v ↦ u*v`.
The center `(u,v)` is proved to be the actual closed rational origin.

Successive local chart projections are compositions of this actual chart
projection. The coordinate formula and the lifts of the curves `v=u^m`
are proved for every number of steps. Each step factors through the actual
Rees Proj and the previously proved residual closed curve.

The construction is the tower of selected affine charts. It does not yet
glue the other charts into the iterated global projective blowup surface.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusBlowupChartIteration

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact

variable {k : Type u} [Field k]

abbrev plane (k : Type u) [Field k] := Spec (CommRingCat.of (planeRing k))

/-- Evaluation at the actual origin of the polynomial plane. -/
def originEvaluation : planeRing k →+* k :=
  (Polynomial.evalRingHom 0).comp (Polynomial.evalRingHom 0)

theorem originEvaluation_surjective : Function.Surjective (originEvaluation (k := k)) := by
  intro a
  exact ⟨Polynomial.C (Polynomial.C a), by simp [originEvaluation]⟩

/-- The Rees center ideal is the actual ideal of the rational origin. -/
theorem centerIdeal_eq_origin_kernel :
    centerIdeal (k := k) = RingHom.ker originEvaluation := by
  ext f
  rw [RingHom.mem_ker]
  change f ∈ Ideal.span {Polynomial.C Polynomial.X, Polynomial.X} ↔
    Polynomial.eval 0 (Polynomial.eval 0 f) = 0
  simpa only [Polynomial.C_0, sub_zero] using
    (Polynomial.mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero
      (a := (0 : k)) (b := (0 : Polynomial k)) (P := f))

instance centerIdeal_isMaximal : (centerIdeal (k := k)).IsMaximal := by
  rw [centerIdeal_eq_origin_kernel]
  exact RingHom.ker_isMaximal_of_surjective originEvaluation originEvaluation_surjective

/-- The actual center point of each selected coordinate chart. -/
def originPoint : plane k := ⟨centerIdeal, inferInstance⟩

theorem originPoint_closed : IsClosed ({originPoint (k := k)} : Set (plane k)) :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr centerIdeal_isMaximal

/-- The origin is supplied by an actual rational-point morphism. -/
def originMorphism : Spec (CommRingCat.of k) ⟶ plane k :=
  Spec.map (CommRingCat.ofHom originEvaluation)

theorem originMorphism_point : fieldMorphismPoint (originMorphism (k := k)) = originPoint := by
  apply PrimeSpectrum.ext
  change Ideal.comap originEvaluation (IsLocalRing.maximalIdeal k) = centerIdeal
  rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot,
    centerIdeal_eq_origin_kernel]

/-- Actual scheme coordinates on the selected Rees chart. -/
def coordinateChartIso : plane k ≅ Spec (CommRingCat.of (reesChartRing k)) :=
  Scheme.Spec.mapIso (FrobeniusBlowupContact.chartPolynomialEquiv (k := k)).toCommRingCatIso.op

/-- The polynomial plane is an actual open chart of the point blowup. -/
def coordinateChart : plane k ⟶ scheme (centerIdeal (k := k)) :=
  coordinateChartIso.hom ≫ chartι centerIdeal centerU

instance coordinateChart_isOpenImmersion : IsOpenImmersion (coordinateChart (k := k)) := by
  unfold coordinateChart
  infer_instance

/-- The actual projection of this chosen point-blowup chart. -/
def coordinateBlowdown : plane k ⟶ plane k :=
  coordinateChart ≫ toSpec centerIdeal

theorem chartToPolynomial_comp_baseMap :
    (FrobeniusBlowupContact.chartPolynomialEquiv (k := k)).toRingHom.comp baseMap =
      chartSubstitution := by
  apply RingHom.ext
  intro r
  exact chartToPolynomial_baseMap r

theorem coordinateBlowdown_eq :
    coordinateBlowdown (k := k) = Spec.map (CommRingCat.ofHom chartSubstitution) := by
  rw [coordinateBlowdown, coordinateChart, Category.assoc, chartι_toSpec]
  change Spec.map (CommRingCat.ofHom
      (FrobeniusBlowupContact.chartPolynomialEquiv (k := k)).toRingHom) ≫
    Spec.map (CommRingCat.ofHom baseMap) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, chartToPolynomial_comp_baseMap]

/-- The actual monomial curve in a chosen polynomial-plane chart. -/
def curveInPlane (m : ℕ) : Spec (CommRingCat.of (Polynomial k)) ⟶ plane k :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (Polynomial.X ^ m)))

instance curveInPlane_isClosedImmersion (m : ℕ) :
    IsClosedImmersion (curveInPlane (k := k) m) :=
  IsClosedImmersion.spec_of_surjective _ (fun r => ⟨Polynomial.C r, by simp⟩)

/-- The actual rational origin on the parameter line. -/
def parameterOriginMorphism : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0))

theorem curveEvaluation_origin (m : ℕ) (hm : 0 < m) :
    (Polynomial.evalRingHom (0 : k)).comp (Polynomial.evalRingHom (Polynomial.X ^ m)) =
      originEvaluation := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [originEvaluation]
  · simp [originEvaluation, ne_of_gt hm]

/-- Before contact is exhausted, the next center is the actual rational origin on the lifted curve. -/
theorem parameterOrigin_curveInPlane (m : ℕ) (hm : 0 < m) :
    parameterOriginMorphism (k := k) ≫ curveInPlane m = originMorphism := by
  change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (Polynomial.X ^ m))) =
      Spec.map (CommRingCat.ofHom originEvaluation)
  rw [← Spec.map_comp,
    ← CommRingCat.ofHom_comp, curveEvaluation_origin m hm]

/-- Coordinate parametrization identifies the curve with the already proved residual closed curve. -/
theorem curveInPlane_chart (m : ℕ) :
    curveInPlane (k := k) m ≫ coordinateChartIso.hom = residualCurveChartMorphism m := by
  change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (Polynomial.X ^ m))) ≫
    Spec.map (CommRingCat.ofHom (FrobeniusBlowupContact.chartPolynomialEquiv (k := k)).toRingHom) =
      Spec.map (CommRingCat.ofHom ((Polynomial.evalRingHom (Polynomial.X ^ m)).comp
        (FrobeniusBlowupContact.chartPolynomialEquiv (k := k)).toRingHom))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem curveInPlane_intoBlowup (m : ℕ) :
    curveInPlane (k := k) m ≫ coordinateChart = residualCurveMorphism m := by
  change curveInPlane m ≫ (coordinateChartIso.hom ≫ chartι centerIdeal centerU) =
    residualCurveChartMorphism m ≫ chartι centerIdeal centerU
  rw [← Category.assoc, curveInPlane_chart]

/-- One actual chart blowdown raises the monomial exponent by exactly one. -/
theorem curveInPlane_blowdown (m : ℕ) :
    curveInPlane (k := k) m ≫ coordinateBlowdown = curveInPlane (m + 1) := by
  change curveInPlane m ≫ (coordinateChart ≫ toSpec centerIdeal) =
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (Polynomial.X ^ (m + 1))))
  rw [← Category.assoc, curveInPlane_intoBlowup,
    residualCurveMorphism_toSpec]

/-- The actual tower projection, defined by composing point-blowup chart projections. -/
def stageProjection : ℕ → (plane k ⟶ plane k)
  | 0 => 𝟙 _
  | n + 1 => coordinateBlowdown ≫ stageProjection n

@[simp] theorem stageProjection_zero : stageProjection (k := k) 0 = 𝟙 _ := rfl

theorem stageProjection_succ (n : ℕ) :
    stageProjection (k := k) (n + 1) = coordinateBlowdown ≫ stageProjection n := rfl

/-- The ring map used to describe, rather than define, the actual composite projection. -/
def stageSubstitution (n : ℕ) : planeRing k →+* planeRing k :=
  Polynomial.eval₂RingHom Polynomial.C (uCoord ^ n * vCoord)

@[simp] theorem stageSubstitution_C (n : ℕ) (r : Polynomial k) :
    stageSubstitution n (Polynomial.C r) = Polynomial.C r := by
  simp [stageSubstitution]

@[simp] theorem stageSubstitution_u (n : ℕ) :
    stageSubstitution n (uCoord (k := k)) = uCoord := stageSubstitution_C n Polynomial.X

@[simp] theorem stageSubstitution_v (n : ℕ) :
    stageSubstitution n (vCoord (k := k)) = uCoord ^ n * vCoord := by
  simp [stageSubstitution, vCoord]

theorem stageSubstitution_zero :
    stageSubstitution (k := k) 0 = RingHom.id (planeRing k) := by
  apply Polynomial.ringHom_ext
  · intro r
    simp only [stageSubstitution_C, RingHom.id_apply]
  · change stageSubstitution 0 vCoord = vCoord
    rw [stageSubstitution_v, pow_zero, one_mul]

theorem stageSubstitution_succ (n : ℕ) :
    stageSubstitution (k := k) (n + 1) = chartSubstitution.comp (stageSubstitution n) := by
  apply Polynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, stageSubstitution_C, chartSubstitution_C]
  · change stageSubstitution (n + 1) vCoord = chartSubstitution (stageSubstitution n vCoord)
    rw [stageSubstitution_v, stageSubstitution_v, map_mul, map_pow,
      chartSubstitution_u, chartSubstitution_v, pow_succ, mul_assoc]

/-- The actual `n`-step projection has the coordinate formula `v ↦ u^n*v`. -/
theorem stageProjection_eq (n : ℕ) :
    stageProjection (k := k) n = Spec.map (CommRingCat.ofHom (stageSubstitution n)) := by
  induction n with
  | zero =>
      rw [stageProjection_zero, stageSubstitution_zero]
      exact (Spec.map_id _).symm
  | succ n ih =>
      rw [stageProjection_succ, coordinateBlowdown_eq, ih,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← stageSubstitution_succ]

/-- The actual composite pullback of the original curve equation has exactly this exceptional factor. -/
theorem stageTotalEquation_factorization (n m : ℕ) :
    stageSubstitution (k := k) n (vCoord - uCoord ^ (m + n)) =
      uCoord ^ n * (vCoord - uCoord ^ m) := by
  rw [map_sub, map_pow, stageSubstitution_v, stageSubstitution_u, pow_add]
  ring

/-- The full exceptional saturation of the actual `n`-stage total-transform ideal. -/
theorem stageTotalEquation_saturation (n m : ℕ) (f : planeRing k) :
    (∃ j : ℕ, uCoord ^ j * f ∈
      Ideal.span {stageSubstitution n (vCoord - uCoord ^ (m + n))}) ↔
        f ∈ Ideal.span {vCoord - uCoord ^ m} := by
  have hker : RingHom.ker (Polynomial.evalRingHom (Polynomial.X ^ m)) =
      Ideal.span {vCoord (k := k) - uCoord ^ m} := by
    rw [Polynomial.ker_evalRingHom]
    simp only [vCoord, uCoord, ← Polynomial.C_pow]
  have heval : Polynomial.evalRingHom (Polynomial.X ^ m : Polynomial k)
      (stageSubstitution (k := k) n (vCoord - uCoord ^ (m + n))) = 0 := by
    rw [stageTotalEquation_factorization]
    simp [vCoord, uCoord]
  have hu : Polynomial.evalRingHom (Polynomial.X ^ m) (uCoord (k := k)) = Polynomial.X := by
    simp [uCoord]
  constructor
  · rintro ⟨j, hj⟩
    rw [← hker, RingHom.mem_ker]
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hj
    have h : Polynomial.X ^ j * Polynomial.evalRingHom (Polynomial.X ^ m) f = 0 := by
      simpa only [map_mul, map_pow, hu, heval, zero_mul] using
        congrArg (Polynomial.evalRingHom (Polynomial.X ^ m)) hg
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero j Polynomial.X_ne_zero)
  · intro hf
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hf
    refine ⟨n, Ideal.mem_span_singleton.mpr ⟨g, ?_⟩⟩
    rw [hg, stageTotalEquation_factorization, mul_assoc]

/-- The full local tower gives actual compatible morphisms of the residual curves. -/
theorem curveInPlane_stageProjection (n m : ℕ) :
    curveInPlane (k := k) m ≫ stageProjection n = curveInPlane (m + n) := by
  induction n generalizing m with
  | zero => simp only [stageProjection_zero, Category.comp_id, Nat.add_zero]
  | succ n ih =>
      rw [stageProjection_succ, ← Category.assoc, curveInPlane_blowdown, ih]
      congr 1
      omega

/-- A stage bounded by the original contact exponent lifts that same original curve. -/
theorem curveInPlane_contactStage (p j : ℕ) (hj : j ≤ p) :
    curveInPlane (k := k) (p - j) ≫ stageProjection j = curveInPlane p := by
  rw [curveInPlane_stageProjection, Nat.sub_add_cancel hj]

/-- At the last local stage the lifted curve is `v=1`, with the original curve as its projection. -/
theorem terminal_curve_projection (p : ℕ) :
    curveInPlane (k := k) 0 ≫ stageProjection p = curveInPlane p := by
  simpa only [Nat.zero_add] using curveInPlane_stageProjection (k := k) p 0

end KltDP.Examples.FrobeniusBlowupChartIteration

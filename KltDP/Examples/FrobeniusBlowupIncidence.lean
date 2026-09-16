import KltDP.Examples.FrobeniusBlowupContact
import KltDP.Examples.FrobeniusGraphStalkContact
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Intersections in the actual monomial blowup chart

The residual curve is the previously constructed closed affine line in the
actual Rees chart. The intersection ideals below are the actual images of
the exceptional and fiber ideals under its ring map. Their quotient lengths
over the field are computed, as are lengths over the actual curve stalk at
the rational parameter zero. The ambient ideal-sum quotient is also related
to the pullback quotient by an actual ring equivalence.

This is one chart. It does not assert a global intersection-number formula
or construct the iterated surface and its other exceptional curves.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusBlowupIncidence

open FrobeniusBlowupContact FrobeniusGraphContact FrobeniusGraphStalkContact

variable {k : Type u} [Field k]

/-- The coordinate map of the strict fiber `w=0` in the actual Rees chart. -/
def fiberChartMap : reesChartRing k →+* Polynomial k :=
  (Polynomial.evalRingHom 0).comp FrobeniusBlowupContact.chartPolynomialEquiv.toRingHom

@[simp] theorem fiberChartMap_u : fiberChartMap (chartU (k := k)) = Polynomial.X := by
  simp [fiberChartMap, uCoord]

@[simp] theorem fiberChartMap_w : fiberChartMap (chartW (k := k)) = 0 := by
  simp [fiberChartMap, vCoord]

theorem fiberChartMap_ker :
    RingHom.ker (fiberChartMap (k := k)) = Ideal.span {chartW} := by
  have hmap : Ideal.map FrobeniusBlowupContact.chartPolynomialEquiv.toRingHom
      (Ideal.span {chartW (k := k)}) = Ideal.span {Polynomial.X} := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun z => Ideal.span {z}) FrobeniusBlowupContact.chartPolynomialEquiv_w
  rw [fiberChartMap, ← RingHom.comap_ker, Polynomial.ker_evalRingHom,
    Polynomial.C_0, sub_zero, ← hmap]
  exact Ideal.comap_map_of_bijective
    (FrobeniusBlowupContact.chartPolynomialEquiv (k := k)).toRingHom
    (FrobeniusBlowupContact.chartPolynomialEquiv (k := k)).bijective

/-- The strict fiber ideal is the full exceptional saturation of the actual base fiber ideal. -/
theorem saturation_baseFiber_iff (f : reesChartRing k) :
    (∃ j : ℕ, chartU (k := k) ^ j * f ∈ Ideal.span {baseMap (vCoord (k := k))}) ↔
      f ∈ Ideal.span {chartW} := by
  constructor
  · rintro ⟨j, hj⟩
    rw [← fiberChartMap_ker, RingHom.mem_ker]
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hj
    have h : (Polynomial.X : Polynomial k) ^ j * fiberChartMap f = 0 := by
      simpa only [← chartU_mul_chartW, map_mul, map_pow, fiberChartMap_u,
        fiberChartMap_w, mul_zero, zero_mul] using congrArg (fiberChartMap (k := k)) hg
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero j Polynomial.X_ne_zero)
  · intro hf
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hf
    refine ⟨1, Ideal.mem_span_singleton.mpr ⟨g, ?_⟩⟩
    rw [pow_one, hg, ← chartU_mul_chartW, mul_assoc]

/-- The actual ideal pulled back from a chart equation along the residual curve. -/
def intersectionIdeal (m : ℕ) (s : reesChartRing k) : Ideal (Polynomial k) :=
  Ideal.map (residualCurveMap m) (Ideal.span {s})

theorem intersectionIdeal_eq (m : ℕ) (s : reesChartRing k) :
    intersectionIdeal m s = Ideal.span {residualCurveMap m s} := by
  rw [intersectionIdeal, Ideal.map_span, Set.image_singleton]

/-- The actual affine scheme-theoretic intersection algebra, on the residual curve. -/
abbrev intersectionAlgebra (m : ℕ) (s : reesChartRing k) :=
  Polynomial k ⧸ intersectionIdeal m s

/-- The same intersection described by the two actual ideals in the ambient chart. -/
def ambientIntersectionIdeal (m : ℕ) (s : reesChartRing k) : Ideal (reesChartRing k) :=
  Ideal.span {residualEquation m} ⊔ Ideal.span {s}

/-- The ambient chart maps to the actual intersection quotient. -/
def intersectionQuotientMap (m : ℕ) (s : reesChartRing k) :
    reesChartRing k →+* intersectionAlgebra m s :=
  (Ideal.Quotient.mk (intersectionIdeal m s)).comp (residualCurveMap m)

theorem intersectionQuotientMap_ker (m : ℕ) (s : reesChartRing k) :
    RingHom.ker (intersectionQuotientMap m s) = ambientIntersectionIdeal m s := by
  rw [intersectionQuotientMap, ambientIntersectionIdeal, ← RingHom.comap_ker, Ideal.mk_ker,
    intersectionIdeal, Ideal.comap_map_of_surjective _ (residualCurveMap_surjective m),
    ← RingHom.ker_eq_comap_bot, residualCurveMap_ker, sup_comm]

/-- The two descriptions of the intersection are related by the proved first isomorphism theorem. -/
def ambientIntersectionQuotientEquiv (m : ℕ) (s : reesChartRing k) :
    reesChartRing k ⧸ ambientIntersectionIdeal m s ≃+* intersectionAlgebra m s :=
  (Ideal.quotEquivOfEq (intersectionQuotientMap_ker m s).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := intersectionQuotientMap m s)
      (Ideal.Quotient.mk_surjective.comp (residualCurveMap_surjective m)))

@[simp] theorem intersectionIdeal_exceptional (m : ℕ) :
    intersectionIdeal m (chartU (k := k)) = Ideal.span {Polynomial.X} := by
  rw [intersectionIdeal_eq, residualCurveMap_u]

@[simp] theorem intersectionIdeal_fiber (m : ℕ) :
    intersectionIdeal m (chartW (k := k)) = Ideal.span {Polynomial.X ^ m} := by
  rw [intersectionIdeal_eq, residualCurveMap_w]

instance exceptionalIntersection_finite (m : ℕ) :
    Module.Finite k (intersectionAlgebra m (chartU (k := k))) := by
  change Module.Finite k (Polynomial k ⧸ intersectionIdeal m chartU)
  rw [intersectionIdeal_exceptional]
  exact Polynomial.monic_X.finite_adjoinRoot

instance fiberIntersection_finite (m : ℕ) :
    Module.Finite k (intersectionAlgebra m (chartW (k := k))) := by
  change Module.Finite k (Polynomial k ⧸ intersectionIdeal m chartW)
  rw [intersectionIdeal_fiber]
  exact (Polynomial.monic_X.pow m).finite_adjoinRoot

theorem exceptionalIntersection_finrank (m : ℕ) :
    Module.finrank k (intersectionAlgebra m (chartU (k := k))) = 1 := by
  change Module.finrank k (Polynomial k ⧸ intersectionIdeal m chartU) = 1
  rw [intersectionIdeal_exceptional]
  have h := (AdjoinRoot.powerBasis' (Polynomial.monic_X (R := k))).finrank
  change Module.finrank k (AdjoinRoot (Polynomial.X : Polynomial k)) =
    (Polynomial.X : Polynomial k).natDegree at h
  simpa only [Polynomial.natDegree_X] using h

/-- The actual remaining fiber contact algebra has dimension `m`, including zero at `m=0`. -/
theorem fiberIntersection_finrank (m : ℕ) :
    Module.finrank k (intersectionAlgebra m (chartW (k := k))) = m := by
  change Module.finrank k (Polynomial k ⧸ intersectionIdeal m chartW) = m
  rw [intersectionIdeal_fiber]
  have h := (AdjoinRoot.powerBasis' ((Polynomial.monic_X (R := k)).pow m)).finrank
  change Module.finrank k (AdjoinRoot ((Polynomial.X : Polynomial k) ^ m)) =
    ((Polynomial.X : Polynomial k) ^ m).natDegree at h
  simpa only [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one] using h

theorem exceptionalIntersection_length_over_field (m : ℕ) :
    Module.length k (intersectionAlgebra m (chartU (k := k))) = 1 := by
  simp only [Module.length_eq_finrank, exceptionalIntersection_finrank, Nat.cast_one]

theorem fiberIntersection_length_over_field (m : ℕ) :
    Module.length k (intersectionAlgebra m (chartW (k := k))) = m := by
  rw [Module.length_eq_finrank, fiberIntersection_finrank]

/-- At the last step the two actual ambient ideals generate the unit ideal. -/
theorem terminal_ambientIntersection_eq_top :
    ambientIntersectionIdeal 0 (chartW (k := k)) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have hr : residualEquation 0 ∈ ambientIntersectionIdeal 0 (chartW (k := k)) :=
    (show Ideal.span {residualEquation (k := k) 0} ≤
      ambientIntersectionIdeal 0 chartW from le_sup_left)
        (Ideal.subset_span (Set.mem_singleton _))
  have hw : chartW ∈ ambientIntersectionIdeal 0 (chartW (k := k)) :=
    (show Ideal.span {chartW (k := k)} ≤
      ambientIntersectionIdeal 0 chartW from le_sup_right)
        (Ideal.subset_span (Set.mem_singleton _))
  have h := (ambientIntersectionIdeal 0 (chartW (k := k))).sub_mem hw hr
  simpa only [residualEquation, pow_zero, sub_sub_cancel] using h

/-- No actual chart prime lies simultaneously on the terminal graph and the fiber. -/
theorem terminal_no_common_prime (q : PrimeSpectrum (reesChartRing k)) :
    ¬ (residualEquation 0 ∈ q.asIdeal ∧ chartW ∈ q.asIdeal) := by
  rintro ⟨hr, hw⟩
  have h : ambientIntersectionIdeal 0 (chartW (k := k)) ≤ q.asIdeal :=
    sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hr)
      ((Ideal.span_singleton_le_iff_mem _).mpr hw)
  rw [terminal_ambientIntersection_eq_top] at h
  exact q.isPrime.ne_top (top_le_iff.mp h)

/-- The actual closed rational parameter point on the affine residual curve. -/
def curvePoint : Spec (CommRingCat.of (Polynomial k)) := parameterSchemePoint (0 : k)

theorem curvePoint_closed :
    IsClosed ({curvePoint (k := k)} : Set (Spec (CommRingCat.of (Polynomial k)))) := by
  apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
  change (parameterPointIdeal (0 : k)).IsMaximal
  rw [parameterPointIdeal, ← Polynomial.ker_evalRingHom]
  exact RingHom.ker_isMaximal_of_surjective (Polynomial.evalRingHom (0 : k))
    (fun r => ⟨Polynomial.C r, by simp⟩)

/-- Its actual image in the Rees chart under the constructed closed immersion. -/
def pointInChart (m : ℕ) : Spec (CommRingCat.of (reesChartRing k)) :=
  (residualCurveChartMorphism m).base curvePoint

theorem pointInChart_closed (m : ℕ) :
    IsClosed ({pointInChart (k := k) m} : Set (Spec (CommRingCat.of (reesChartRing k)))) := by
  simpa only [Set.image_singleton, pointInChart] using
    (residualCurveChartMorphism (k := k) m).isClosedEmbedding.isClosedMap _ curvePoint_closed

theorem pointInChart_mem_iff (m : ℕ) (s : reesChartRing k) :
    s ∈ (pointInChart (k := k) m).asIdeal ↔ Polynomial.eval 0 (residualCurveMap m s) = 0 := by
  change residualCurveMap m s ∈ parameterPointIdeal (0 : k) ↔ _
  rw [parameterPointIdeal, ← Polynomial.ker_evalRingHom, RingHom.mem_ker,
    Polynomial.coe_evalRingHom]

theorem pointInChart_on_exceptional (m : ℕ) :
    chartU (k := k) ∈ (pointInChart (k := k) m).asIdeal := by
  rw [pointInChart_mem_iff, residualCurveMap_u]
  simp

theorem pointInChart_on_graph (m : ℕ) :
    residualEquation m ∈ (pointInChart (k := k) m).asIdeal := by
  rw [pointInChart_mem_iff, residualCurveMap_residualEquation]
  simp

theorem pointInChart_on_fiber (m : ℕ) (hm : 0 < m) :
    chartW (k := k) ∈ (pointInChart (k := k) m).asIdeal := by
  rw [pointInChart_mem_iff, residualCurveMap_w]
  simp [ne_of_gt hm]

theorem terminal_point_has_fiber_coordinate_one :
    chartW (k := k) - 1 ∈ (pointInChart (k := k) 0).asIdeal := by
  simpa only [residualEquation, pow_zero] using (pointInChart_on_graph (k := k) 0)

/-- The actual structure-sheaf stalk of the residual affine curve at its rational point. -/
abbrev curveStalk (k : Type u) [Field k] :=
  (Spec (CommRingCat.of (Polynomial k))).presheaf.stalk curvePoint

/-- The germ of the actual pulled chart section. -/
def intersectionGerm (m : ℕ) (s : reesChartRing k) : curveStalk k :=
  StructureSheaf.toStalk (Polynomial k) curvePoint (residualCurveMap m s)

/-- It is also the actual stalk pullback of the ambient chart section. -/
theorem intersectionGerm_pullback (m : ℕ) (s : reesChartRing k) :
    (residualCurveChartMorphism (k := k) m).stalkMap curvePoint
      (StructureSheaf.toStalk (reesChartRing k) (pointInChart (k := k) m) s) =
        intersectionGerm m s :=
  AlgebraicGeometry.stalkMap_toStalk_apply
    (CommRingCat.ofHom (residualCurveMap (k := k) m)) (curvePoint (k := k)) s

/-- The standard stalk/localization equivalence for this actual affine curve point. -/
def curveStalkLocalEquiv : curveStalk k ≃+* parameterLocalRing (0 : k) :=
  KltDP.Geometry.specStalkLocalizationEquiv (Polynomial k) curvePoint

theorem curveStalkLocalEquiv_germ (m : ℕ) (s : reesChartRing k) :
    curveStalkLocalEquiv (intersectionGerm m s) =
      algebraMap (Polynomial k) (parameterLocalRing (0 : k)) (residualCurveMap m s) :=
  StructureSheaf.stalkToFiberRingHom_toStalk (Polynomial k) curvePoint (residualCurveMap m s)

theorem curveStalkLocalEquiv_exceptional (m : ℕ) :
    curveStalkLocalEquiv (intersectionGerm m (chartU (k := k))) = localParameter (0 : k) := by
  rw [curveStalkLocalEquiv_germ, residualCurveMap_u]
  simp [localParameter]

theorem curveStalkLocalEquiv_fiber (m : ℕ) :
    curveStalkLocalEquiv (intersectionGerm m (chartW (k := k))) =
      localParameter (0 : k) ^ m := by
  rw [curveStalkLocalEquiv_germ, residualCurveMap_w, map_pow]
  simp [localParameter]

/-- The actual exceptional germ cuts a length-one quotient on the actual curve stalk. -/
theorem exceptional_stalk_quotient_length (m : ℕ) :
    Module.length (curveStalk k)
      (curveStalk k ⧸ Ideal.span {intersectionGerm m (chartU (k := k))}) = 1 := by
  rw [quotient_span_length_eq_of_ringEquiv curveStalkLocalEquiv,
    curveStalkLocalEquiv_exceptional]
  have h := KltDP.RingTheory.dvr_length_quotient_uniformizer_pow
    (parameterLocalRing (0 : k)) (localParameter 0) (localParameter_uniformizer 0) 1
  have hp : localParameter (0 : k) ^ (1 : ℕ) = localParameter (0 : k) := pow_one _
  rw [hp] at h
  exact h

/-- The actual fiber germ cuts a quotient of length `m` on the actual curve stalk. -/
theorem fiber_stalk_quotient_length (m : ℕ) :
    Module.length (curveStalk k)
      (curveStalk k ⧸ Ideal.span {intersectionGerm m (chartW (k := k))}) = m := by
  rw [quotient_span_length_eq_of_ringEquiv curveStalkLocalEquiv,
    curveStalkLocalEquiv_fiber]
  exact KltDP.RingTheory.dvr_length_quotient_uniformizer_pow (parameterLocalRing (0 : k))
    (localParameter 0) (localParameter_uniformizer 0) m

end KltDP.Examples.FrobeniusBlowupIncidence

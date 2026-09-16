import KltDP.Examples.FrobeniusGlobalStrictTransform
import KltDP.Examples.FrobeniusBlowupIncidence
import KltDP.Geometry.ReducedClosedImageChart

/-!
# Contact on the actual whole strict transform at successive blowups

The residual affine line is proved to be an open chart of the actual
kernel-glued strict transform of the whole original projective graph.
Consequently its actual stalk map is an isomorphism. Through that original
map we transport the pulled exceptional and strict-fiber sections of the
actual Rees chart, and compute their quotient lengths on the whole strict
transform's stalk. The pulled preceding-stage strict-fiber section factors
as exceptional times current strict fiber, with quotient length one larger.

Only the original field and natural stage/contact exponents are inputs.
The characteristic-p graph is the case of total exponent p. No contact
integer, stalk isomorphism, intersection number, or global curve class is
assumed. The complementary exceptional chart and full exceptional chain
are separate obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusStrictTransformContact

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupChartIteration
open FrobeniusGlobalBlowupStages FrobeniusStrictTransformClosure
open FrobeniusGlobalStrictTransform FrobeniusBlowupIncidence

variable {k : Type u} [Field k]

/-- The actual residual-line factorization into the whole local closure
is an open immersion, derived from its reduced closed image. -/
instance residualToClosure_isOpenImmersion (A : PlaneChartedScheme k) (n m : ℕ) :
    IsOpenImmersion (residualToClosure A n m) := by
  apply ReducedClosedImageChart.isOpenImmersion_of_reduced_closed_image
    (curveInPlane m) (A.stage n).chart (closureInclusion A n m)
    (residualToClosure A n m)
  · exact residualToClosure_inclusion A n m
  · exact range_closureInclusion_eq_residual A n m

/-- The original affine residual curve is an actual open chart of the
strict transform defined from the entire original projective graph. -/
def residualChart (n m : ℕ) : Spec (CommRingCat.of (Polynomial k)) ⟶
    strictTransform (k := k) n (m + n) :=
  residualToClosure projectiveProductInitial n m ≫ (strictTransformIsoLocal n m).inv

instance residualChart_isOpenImmersion (n m : ℕ) :
    IsOpenImmersion (residualChart (k := k) n m) := by
  unfold residualChart
  infer_instance

/-- The new chart retains the actual inclusion in the entire blowup stage. -/
@[reassoc] theorem residualChart_ι (n m : ℕ) :
    residualChart (k := k) n m ≫ strictTransformι n (m + n) =
      (projectiveProductInitial (k := k)).residualCurve n m := by
  rw [residualChart, Category.assoc, ← strictTransformIsoLocal_hom_ι n m,
    Iso.inv_hom_id_assoc, residualToClosure_inclusion]

/-- At a successor stage the same map is the original residual curve
inside the actual Rees blowup chart and its global open inclusion. -/
@[reassoc] theorem residualChart_succ_ι (n m : ℕ) :
    residualChart (k := k) (n + 1) m ≫ strictTransformι (n + 1) (m + (n + 1)) =
      residualCurveChartMorphism m ≫
        AffineBlowup.chartι centerIdeal centerU ≫
          ((projectiveProductInitial (k := k)).stage n).nextAffineBlowup := by
  rw [residualChart_ι, PlaneChartedScheme.residualCurve_succ]
  simp only [residualCurveMorphism, Category.assoc]

/-- The actual point on the whole strict transform selected by parameter zero. -/
def contactPoint (n m : ℕ) : strictTransform (k := k) n (m + n) :=
  (residualChart n m).base (curvePoint (k := k))

/-- Before contact is exhausted, this is the actual next blowup center
in the whole stage. -/
theorem contactPoint_inclusion (n m : ℕ) (hm : 0 < m) :
    (strictTransformι n (m + n)).base (contactPoint (k := k) n m) =
      ((projectiveProductInitial (k := k)).stage n).chart.base originPoint := by
  change (residualChart n m ≫ strictTransformι n (m + n)).base curvePoint = _
  rw [residualChart_ι]
  have h := (projectiveProductInitial (k := k)).parameterOrigin_residualCurve n m hm
  have he := congrArg fieldMorphismPoint h
  rw [PlaneChartedScheme.centerMorphism_point] at he
  have hp : fieldMorphismPoint (parameterOriginMorphism (k := k)) = curvePoint :=
    FrobeniusGraphStalkContact.polynomialEvaluation_point 0
  change ((projectiveProductInitial (k := k)).residualCurve n m).base
    (fieldMorphismPoint (parameterOriginMorphism (k := k))) = _ at he
  rwa [hp] at he

/-- The actual structure-sheaf stalk of the whole strict transform. -/
abbrev contactStalk (n m : ℕ) :=
  (strictTransform (k := k) n (m + n)).presheaf.stalk (contactPoint n m)

/-- This ring equivalence is the original chart's actual stalk map. -/
def contactStalkEquiv (n m : ℕ) : contactStalk (k := k) n m ≃+* curveStalk k :=
  (asIso ((residualChart n m).stalkMap curvePoint)).commRingCatIsoToRingEquiv

/-- The germ obtained by restricting an original Rees-chart section to
the curve and using the actual open chart of the whole strict transform. -/
def contactGerm (n m : ℕ) (s : reesChartRing k) : contactStalk (k := k) (n + 1) m :=
  (contactStalkEquiv (n + 1) m).symm (intersectionGerm m s)

/-- The chart restriction of this germ is the actual stalk pullback of
the original ambient Rees-chart section. -/
theorem contactGerm_pullback (n m : ℕ) (s : reesChartRing k) :
    (residualChart (n + 1) m).stalkMap curvePoint (contactGerm n m s) =
      (residualCurveChartMorphism m).stalkMap curvePoint
        (StructureSheaf.toStalk (reesChartRing k) (pointInChart m) s) := by
  change contactStalkEquiv (n + 1) m
    ((contactStalkEquiv (n + 1) m).symm (intersectionGerm m s)) = _
  rw [RingEquiv.apply_symm_apply, intersectionGerm_pullback]

@[simp] theorem contactStalkEquiv_germ (n m : ℕ) (s : reesChartRing k) :
    contactStalkEquiv (n + 1) m (contactGerm n m s) = intersectionGerm m s :=
  (contactStalkEquiv (n + 1) m).apply_symm_apply _

/-- The original exceptional equation has intersection length one in
the actual whole-curve stalk at every successor stage. -/
theorem exceptional_contact_length (n m : ℕ) :
    Module.length (contactStalk (k := k) (n + 1) m)
      (contactStalk (k := k) (n + 1) m ⧸ Ideal.span {contactGerm n m chartU}) = 1 := by
  rw [FrobeniusGraphStalkContact.quotient_span_length_eq_of_ringEquiv
    (contactStalkEquiv (n + 1) m), contactStalkEquiv_germ]
  exact exceptional_stalk_quotient_length m

/-- The actual strict-fiber section has remaining contact length m
on the whole strict transform, including the terminal zero-length case. -/
theorem strictFiber_contact_length (n m : ℕ) :
    Module.length (contactStalk (k := k) (n + 1) m)
      (contactStalk (k := k) (n + 1) m ⧸ Ideal.span {contactGerm n m chartW}) = m := by
  rw [FrobeniusGraphStalkContact.quotient_span_length_eq_of_ringEquiv
    (contactStalkEquiv (n + 1) m), contactStalkEquiv_germ]
  exact fiber_stalk_quotient_length m

/-- The pulled preceding-stage strict-fiber equation is exceptional times
current strict fiber in the whole-curve stalk, by the original Rees equation. -/
theorem totalFiber_contactGerm (n m : ℕ) :
    contactGerm (k := k) n m (baseMap vCoord) =
      contactGerm n m chartU * contactGerm n m chartW := by
  apply (contactStalkEquiv (n + 1) m).injective
  rw [map_mul, contactStalkEquiv_germ, contactStalkEquiv_germ,
    contactStalkEquiv_germ, ← chartU_mul_chartW]
  simp only [intersectionGerm, map_mul]

/-- The pullback of the preceding-stage strict fiber has length m+1,
so the exceptional factor removes exactly one of its contacts at this blowup. -/
theorem totalFiber_contact_length (n m : ℕ) :
    Module.length (contactStalk (k := k) (n + 1) m)
      (contactStalk (k := k) (n + 1) m ⧸
        Ideal.span {contactGerm n m (baseMap vCoord)}) = m + 1 := by
  rw [FrobeniusGraphStalkContact.quotient_span_length_eq_of_ringEquiv
    (contactStalkEquiv (n + 1) m), contactStalkEquiv_germ,
    FrobeniusGraphStalkContact.quotient_span_length_eq_of_ringEquiv curveStalkLocalEquiv]
  have h : curveStalkLocalEquiv (intersectionGerm m (baseMap (vCoord (k := k)))) =
      FrobeniusGraphContact.localParameter (0 : k) ^ (m + 1) := by
    rw [← chartU_mul_chartW]
    have hm : intersectionGerm m (chartU (k := k) * chartW) =
        intersectionGerm m chartU * intersectionGerm m chartW := by
      simp only [intersectionGerm, map_mul]
    rw [hm]
    rw [map_mul, curveStalkLocalEquiv_exceptional, curveStalkLocalEquiv_fiber,
      pow_succ, mul_comm]
  rw [h]
  simpa only [Nat.cast_add, Nat.cast_one] using
    KltDP.RingTheory.dvr_length_quotient_uniformizer_pow
      (FrobeniusGraphContact.parameterLocalRing (0 : k))
      (FrobeniusGraphContact.localParameter 0)
      (FrobeniusGraphContact.localParameter_uniformizer 0) (m + 1)

/-- At the terminal graph point the original strict-fiber coordinate
is one in the actual whole-curve stalk, not merely of multiplicity zero. -/
theorem terminal_strictFiber_germ (n : ℕ) :
    contactGerm (k := k) n 0 chartW = 1 := by
  apply (contactStalkEquiv (n + 1) 0).injective
  rw [contactStalkEquiv_germ, map_one]
  simp only [intersectionGerm, residualCurveMap_w, pow_zero, map_one]

end KltDP.Examples.FrobeniusStrictTransformContact

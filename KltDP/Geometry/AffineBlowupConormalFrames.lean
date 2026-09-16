import KltDP.Geometry.AffineBlowupExceptionalOverlap

/-!
# Actual conormal and dual normal frames on a Rees-chart intersection

The two actual quotient restriction maps give mutually inverse ratios.
They determine an actual unit, whose inverse is the restriction of the
opposite chart ratio. The existing conormal equivalence supplies the
left frame; multiplication by this actual unit supplies the right frame,
proved equal to the restriction of the original right equation class.

The quotient-linear dual frames then transform by the inverse unit.
All modules and maps are the existing conormal modules and actual chart
restrictions. No global sheaf or projective-twist identification is assumed.
-/

noncomputable section

namespace KltDP.Geometry.AffineBlowup

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)

/-- The actual ratio unit; its inverse is the opposite chart ratio,
with both inverse identities proved in the actual overlap quotient. -/
def exceptionalOverlapTransitionUnit : (exceptionalOverlapRing I a b)ˣ where
  val := exceptionalOverlapLeft I a b
    (Ideal.Quotient.mk (chartCenterIdeal I a) (chartFraction I a b))
  inv := exceptionalOverlapRight I a b
    (Ideal.Quotient.mk (chartCenterIdeal I b) (chartFraction I b a))
  val_inv := exceptionalOverlap_chartFractions_mul I a b
  inv_val := (mul_comm _ _).trans (exceptionalOverlap_chartFractions_mul I a b)

/-- The unit's value is the already proved conormal transition coefficient. -/
@[simp] theorem exceptionalOverlapTransitionUnit_val :
    (exceptionalOverlapTransitionUnit I a b : exceptionalOverlapRing I a b) =
      Ideal.Quotient.mk (conormalOverlapIdeal I a b) (conormalOverlapRatio I a b) := rfl

/-- The first frame is the actual restriction of the first chart equation class. -/
def conormalOverlapFrameLeft : (conormalOverlapIdeal I a b).Cotangent :=
  conormalOverlapMapLeft I a b
    ((chartCenterIdeal I a).toCotangent (chartCenterEquation I a))

/-- The second frame is the actual restriction of the second chart equation class. -/
def conormalOverlapFrameRight : (conormalOverlapIdeal I a b).Cotangent :=
  conormalOverlapMapRight I a b
    ((chartCenterIdeal I b).toCotangent (chartCenterEquation I b))

/-- These actual frames satisfy the already derived transition equation. -/
theorem conormalOverlap_frames_transition :
    conormalOverlapFrameRight I a b =
      (exceptionalOverlapTransitionUnit I a b : exceptionalOverlapRing I a b) •
        conormalOverlapFrameLeft I a b :=
  conormalOverlap_generator_transition I a b

/-- The original left coordinates are normalized by the actual left frame. -/
@[simp] theorem conormalOverlapEquiv_one :
    conormalOverlapEquiv I a b 1 = conormalOverlapFrameLeft I a b := by
  change conormalOverlapEquiv I a b 1 =
    conormalOverlapMapLeft I a b
      ((chartCenterIdeal I a).toCotangent (chartCenterEquation I a))
  rw [conormalOverlapMapLeft_generator]
  exact KltDP.RingTheory.principalConormalEquiv_one _ _ _ _

/-- The right conormal coordinates are obtained by multiplication by
the actual quotient ratio unit, using the pinned linear equivalence. -/
def conormalOverlapRightEquiv :
    exceptionalOverlapRing I a b ≃ₗ[exceptionalOverlapRing I a b]
      (conormalOverlapIdeal I a b).Cotangent :=
  (LinearEquiv.smulOfUnit (M := exceptionalOverlapRing I a b)
    (exceptionalOverlapTransitionUnit I a b)).trans (conormalOverlapEquiv I a b)

/-- This is the actual right equation frame, not a separately chosen basis vector. -/
@[simp] theorem conormalOverlapRightEquiv_one :
    conormalOverlapRightEquiv I a b 1 = conormalOverlapFrameRight I a b := by
  change conormalOverlapEquiv I a b
    ((exceptionalOverlapTransitionUnit I a b : exceptionalOverlapRing I a b) * 1) = _
  rw [mul_one, conormalOverlap_frames_transition]
  have h := (conormalOverlapEquiv I a b).map_smul
    (exceptionalOverlapTransitionUnit I a b : exceptionalOverlapRing I a b) 1
  simpa only [smul_eq_mul, mul_one, conormalOverlapEquiv_one] using h

/-- The normal frame dual to the actual left conormal frame. -/
def conormalOverlapNormalFrameLeft :
    Module.Dual (exceptionalOverlapRing I a b) (conormalOverlapIdeal I a b).Cotangent :=
  (conormalOverlapEquiv I a b).symm.toLinearMap

/-- The normal frame dual to the actual right conormal frame. -/
def conormalOverlapNormalFrameRight :
    Module.Dual (exceptionalOverlapRing I a b) (conormalOverlapIdeal I a b).Cotangent :=
  (conormalOverlapRightEquiv I a b).symm.toLinearMap

@[simp] theorem conormalOverlapNormalFrameLeft_frame :
    conormalOverlapNormalFrameLeft I a b (conormalOverlapFrameLeft I a b) = 1 := by
  change (conormalOverlapEquiv I a b).symm (conormalOverlapFrameLeft I a b) = 1
  rw [← conormalOverlapEquiv_one, LinearEquiv.symm_apply_apply]

@[simp] theorem conormalOverlapNormalFrameRight_frame :
    conormalOverlapNormalFrameRight I a b (conormalOverlapFrameRight I a b) = 1 := by
  change (conormalOverlapRightEquiv I a b).symm (conormalOverlapFrameRight I a b) = 1
  rw [← conormalOverlapRightEquiv_one, LinearEquiv.symm_apply_apply]

/-- The actual dual normal frames transform by the inverse ratio unit. -/
theorem conormalOverlap_normal_frames_transition :
    conormalOverlapNormalFrameRight I a b =
      ((exceptionalOverlapTransitionUnit I a b)⁻¹ : (exceptionalOverlapRing I a b)ˣ) •
        conormalOverlapNormalFrameLeft I a b := by
  apply LinearMap.ext
  intro m
  rfl

end KltDP.Geometry.AffineBlowup

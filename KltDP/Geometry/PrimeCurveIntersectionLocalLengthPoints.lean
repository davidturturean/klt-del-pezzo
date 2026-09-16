import KltDP.Geometry.PrimeCurveIntersectionLocalLength
import KltDP.Geometry.SmoothFieldRegularPoints
import KltDP.Geometry.NormalStalkDVR
import KltDP.Geometry.PrimeCurveCodimension
import KltDP.Geometry.PrimeCurveSubscheme
import KltDP.Geometry.DivisorOrder

/-!
# The local-length sum formula with the DVR hypothesis at the intersection points (BRIEF20, item 3)

The accepted `PrimeCurve.intersectionDegree_eq_sum_cartierOrderAt` assumes that every stalk of `C` is a
discrete valuation ring. That cannot hold: the stalk at the generic point is a field, so the accepted
statement is vacuous (`docs/DEFECT_VACUOUS_LOCAL_LENGTH_20260911.md`). This module restates it with
hypotheses that can hold, and exhibits a class of curves satisfying them.

* `intersectionDegree_eq_sum_cartierOrderAt'`: the same formula
  `intersectionDegree = Σ_{z ∈ C ∩ D} (cartierOrderAt C (D|_C) (i z)).toNat`, with the DVR hypothesis
  only at the points `i z` of `C` under the intersection. The proof is the accepted one.
* `intersectionInclusion_base_isClosed` and `intersectionDegree_eq_sum_cartierOrderAt_of_closedPoints`:
  those points are closed, so DVR stalks at the closed points of `C` suffice.
* **Nonvacuity.** `stalk_isDiscreteValuationRing_of_isSmooth`: if `C.toSpec` is smooth, every closed
  point of `C` has a DVR stalk. The stalk is regular (`regularPoint_of_isSmooth_of_isClosed'` of
  `SmoothFieldRegularPoints`, with `topologicalKrullDim C.toScheme = 1 ≤ 2` and the accepted integrality
  and Noetherian stalks of `C.toScheme`). It has dimension exactly one: `≤ 1` by
  `ringKrullDim_stalk_le_topologicalKrullDim`, and `≥ 1` because a closed point is not the generic point
  (`ne_genericPoint_of_isClosed`). A regular local domain of dimension one is a DVR
  (`isDiscreteValuationRing_of_regularLocal_of_ringKrullDim_eq_one`).
* Hence `intersectionDegree_eq_sum_cartierOrderAt_of_isSmooth`: the formula for a curve smooth over `k`,
  with no DVR hypothesis left.

Whether a given prime curve of a given surface is smooth is not decided here; `[IsSmooth C.toSpec]` is a
hypothesis on `C`, satisfied for instance by a curve that is smooth over `k` in the pinned sense.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
  (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)
  (hC : C.NotInSupport D hD)

/-- Stalks of the integral curve scheme are domains (the accepted `integralSchemeStalk_isDomain`;
the accepted local-length module declares the same instance locally). -/
local instance localLengthPoints_stalkIsDomain (y : C.toScheme) :
    IsDomain (C.toScheme.presheaf.stalk y) :=
  integralSchemeStalk_isDomain C.toScheme y

/-- **The sum formula with the DVR hypothesis only at the points of `C` under the intersection.** -/
theorem intersectionDegree_eq_sum_cartierOrderAt' [IsAlgClosed k]
    (hDVR : ∀ z : C.intersectionScheme D hD hC,
      IsDiscreteValuationRing
        (C.toScheme.presheaf.stalk ((C.intersectionInclusion D hD hC).base z))) :
    letI : Fintype (C.intersectionScheme D hD hC) :=
      haveI := C.intersectionScheme_finite' D hD hC
      Fintype.ofFinite _
    C.intersectionDegree D hD hC = ∑ z : C.intersectionScheme D hD hC,
      (cartierOrderAt C.toScheme (C.restrictCartier D hD hC)
        ((C.intersectionInclusion D hD hC).base z)).toNat := by
  letI : Fintype (C.intersectionScheme D hD hC) :=
    haveI := C.intersectionScheme_finite' D hD hC
    Fintype.ofFinite _
  letI : DiscreteTopology (C.intersectionScheme D hD hC) :=
    DiscreteTopology.of_finite_of_isClosed_singleton
      (C.intersectionScheme_isClosed_singleton' D hD hC)
  refine (C.intersectionDegree_eq_sum_points'' D hD hC).trans ?_
  refine Finset.sum_congr rfl fun z _ => ?_
  obtain ⟨c, hzc⟩ := C.exists_genericChart D hD ((C.intersectionInclusion D hD hC).base z)
  obtain ⟨_, ⟨V, hVaff, rfl⟩, hzV, hVle⟩ :=
    (isBasis_affine_open C.toScheme).exists_subset_of_mem_open hzc (C.chartPreimage D c.1).2
  haveI := hDVR z
  refine (C.finrank_singleton_eq_localLength D hD hC z c ⟨V, hVaff⟩ hVle hzV).trans ?_
  rw [C.cartierOrderAt_restrictCartier_eq_localLength _ D hD hC c (hVle hzV), Int.toNat_natCast]

/-- The points of `C` under the intersection are closed. -/
theorem intersectionInclusion_base_isClosed (z : C.intersectionScheme D hD hC) :
    IsClosed ({(C.intersectionInclusion D hD hC).base z} : Set C.toScheme) := by
  rw [← Set.image_singleton]
  exact (IsClosedImmersion.base_closed (f := C.intersectionInclusion D hD hC)).isClosedMap _
    (C.intersectionScheme_isClosed_singleton' D hD hC z)

/-- **The sum formula with DVR stalks at the closed points of `C`.** The stalk orders in the
statement are taken at the discrete valuation rings the hypothesis provides, through the
closedness of the points of `C` under the intersection. -/
theorem intersectionDegree_eq_sum_cartierOrderAt_of_closedPoints [IsAlgClosed k]
    (hDVR : ∀ y : C.toScheme, IsClosed ({y} : Set C.toScheme) →
      IsDiscreteValuationRing (C.toScheme.presheaf.stalk y)) :
    letI : Fintype (C.intersectionScheme D hD hC) :=
      haveI := C.intersectionScheme_finite' D hD hC
      Fintype.ofFinite _
    letI : ∀ z : C.intersectionScheme D hD hC,
        IsDiscreteValuationRing
          (C.toScheme.presheaf.stalk ((C.intersectionInclusion D hD hC).base z)) :=
      fun z => hDVR _ (C.intersectionInclusion_base_isClosed D hD hC z)
    C.intersectionDegree D hD hC = ∑ z : C.intersectionScheme D hD hC,
      (cartierOrderAt C.toScheme (C.restrictCartier D hD hC)
        ((C.intersectionInclusion D hD hC).base z)).toNat := by
  letI : Fintype (C.intersectionScheme D hD hC) :=
    haveI := C.intersectionScheme_finite' D hD hC
    Fintype.ofFinite _
  letI : ∀ z : C.intersectionScheme D hD hC,
      IsDiscreteValuationRing
        (C.toScheme.presheaf.stalk ((C.intersectionInclusion D hD hC).base z)) :=
    fun z => hDVR _ (C.intersectionInclusion_base_isClosed D hD hC z)
  exact C.intersectionDegree_eq_sum_cartierOrderAt' D hD hC fun z =>
    hDVR _ (C.intersectionInclusion_base_isClosed D hD hC z)

/-- A closed point of a prime curve is not the generic point of the curve scheme: otherwise the curve
scheme would have at most one point, contradicting `topologicalKrullDim C.toScheme = 1`. -/
theorem ne_genericPoint_of_isClosed (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme)) :
    y ≠ _root_.genericPoint C.toScheme := by
  intro h
  haveI : Subsingleton C.toScheme := ⟨fun a b => by
    have ha : a ∈ closure ({_root_.genericPoint C.toScheme} : Set C.toScheme) := by
      rw [_root_.genericPoint_closure]
      exact Set.mem_univ a
    have hb : b ∈ closure ({_root_.genericPoint C.toScheme} : Set C.toScheme) := by
      rw [_root_.genericPoint_closure]
      exact Set.mem_univ b
    rw [← h, hy.closure_eq] at ha hb
    exact (Set.mem_singleton_iff.mp ha).trans (Set.mem_singleton_iff.mp hb).symm⟩
  have hnonpos := topologicalKrullDim_nonpos_of_subsingleton C.toScheme
  rw [C.dimension_one_toScheme] at hnonpos
  have hpositive : (0 : WithBot ℕ∞) < 1 :=
    WithBot.coe_lt_coe.mpr (by simp : (0 : ℕ∞) < 1)
  exact hpositive.not_le hnonpos

/-- **Nonvacuity: a prime curve smooth over `k` has discrete valuation rings at its closed points.** -/
theorem stalk_isDiscreteValuationRing_of_isSmooth [IsAlgClosed k] [IsSmooth C.toSpec]
    (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme)) :
    IsDiscreteValuationRing (C.toScheme.presheaf.stalk y) := by
  have hdim2 : topologicalKrullDim C.toScheme ≤ 2 := by
    rw [C.dimension_one_toScheme]
    norm_num
  have hreg : RegularPoint C.toScheme y :=
    SmoothFieldRegularPoints.regularPoint_of_isSmooth_of_isClosed' C.toSpec
      (fun x => inferInstance) hdim2 y hy
  have hle : ringKrullDim (C.toScheme.presheaf.stalk y) ≤ 1 :=
    (ringKrullDim_stalk_le_topologicalKrullDim C.toScheme y).trans_eq C.dimension_one_toScheme
  have hge : 1 ≤ ringKrullDim (C.toScheme.presheaf.stalk y) :=
    one_le_ringKrullDim_stalk_of_ne_genericPoint C.toScheme y (C.ne_genericPoint_of_isClosed y hy)
  exact isDiscreteValuationRing_of_regularLocal_of_ringKrullDim_eq_one _ hreg (le_antisymm hle hge)

/-- **The sum formula for a prime curve smooth over `k`**, with no DVR hypothesis left: the
discrete valuation rings in the statement are the ones proved above from smoothness. -/
theorem intersectionDegree_eq_sum_cartierOrderAt_of_isSmooth [IsAlgClosed k] [IsSmooth C.toSpec] :
    letI : Fintype (C.intersectionScheme D hD hC) :=
      haveI := C.intersectionScheme_finite' D hD hC
      Fintype.ofFinite _
    letI : ∀ z : C.intersectionScheme D hD hC,
        IsDiscreteValuationRing
          (C.toScheme.presheaf.stalk ((C.intersectionInclusion D hD hC).base z)) :=
      fun z => C.stalk_isDiscreteValuationRing_of_isSmooth _
        (C.intersectionInclusion_base_isClosed D hD hC z)
    C.intersectionDegree D hD hC = ∑ z : C.intersectionScheme D hD hC,
      (cartierOrderAt C.toScheme (C.restrictCartier D hD hC)
        ((C.intersectionInclusion D hD hC).base z)).toNat := by
  letI : Fintype (C.intersectionScheme D hD hC) :=
    haveI := C.intersectionScheme_finite' D hD hC
    Fintype.ofFinite _
  letI : ∀ z : C.intersectionScheme D hD hC,
      IsDiscreteValuationRing
        (C.toScheme.presheaf.stalk ((C.intersectionInclusion D hD hC).base z)) :=
    fun z => C.stalk_isDiscreteValuationRing_of_isSmooth _
      (C.intersectionInclusion_base_isClosed D hD hC z)
  exact C.intersectionDegree_eq_sum_cartierOrderAt_of_closedPoints D hD hC
    fun y hy => C.stalk_isDiscreteValuationRing_of_isSmooth y hy

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

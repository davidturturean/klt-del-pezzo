import KltDP.Geometry.PrimeCurveIntersectionLocalLengthPoints
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# A degree-one intersection has a simple original local quotient

The existing finite sum of singleton section dimensions bounds each local
length. At an actual point of a smooth curve the stalk is a DVR; its actual
intersection quotient is nonzero, so length at most one is exactly one.
The pinned simple-module criterion then identifies the equation ideal with
the original maximal ideal. No local transversality or multiplicity is an
input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k] {X : NormalProjectiveSurface k}
  (C : X.PrimeCurve) [IsSmooth C.toSpec]
  (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)
  (hC : C.NotInSupport D hD)

local instance intersectionOne_stalkIsDomain (y : C.toScheme) :
    IsDomain (C.toScheme.presheaf.stalk y) := integralSchemeStalk_isDomain C.toScheme y

/-- At every original intersection point, degree at most one forces the
restricted local equation to generate the actual curve maximal ideal. -/
theorem restrictedCoefficient_span_eq_maximalIdeal_of_degree_le_one
    (hdegree : C.intersectionDegree D hD hC ≤ 1)
    (z : C.intersectionScheme D hD hC) (c : C.GenericChart D)
    (hzc : (C.intersectionInclusion D hD hC).base z ∈ C.chartPreimage D c.1) :
    Ideal.span {C.toScheme.presheaf.germ (C.chartPreimage D c.1) _ hzc
      (C.restrictedCoefficient D c.1)} =
      maximalIdeal (C.toScheme.presheaf.stalk ((C.intersectionInclusion D hD hC).base z)) := by
  classical
  letI := C.intersectionScheme_finite' D hD hC
  letI : Fintype (C.intersectionScheme D hD hC) := Fintype.ofFinite _
  letI : DiscreteTopology (C.intersectionScheme D hD hC) :=
    DiscreteTopology.of_finite_of_isClosed_singleton
      (C.intersectionScheme_isClosed_singleton' D hD hC)
  letI : ∀ w : C.intersectionScheme D hD hC,
      Module k Γ(C.intersectionScheme D hD hC,
        singletonOpen (C.intersectionScheme D hD hC) w) :=
    fun w => sectionsBaseModule (C.intersectionScheme D hD hC)
      (baseFieldToGlobalSections (C.intersectionToSpec D hD hC))
      (singletonOpen (C.intersectionScheme D hD hC) w)
  let y := (C.intersectionInclusion D hD hC).base z
  let f := C.toScheme.presheaf.germ (C.chartPreimage D c.1) y hzc
    (C.restrictedCoefficient D c.1)
  letI := C.stalk_isDiscreteValuationRing_of_isSmooth y
    (C.intersectionInclusion_base_isClosed D hD hC z)
  obtain ⟨_, ⟨V, hVaff, rfl⟩, hzV, hVle⟩ :=
    (isBasis_affine_open C.toScheme).exists_subset_of_mem_open hzc
      (C.chartPreimage D c.1).isOpen
  have hlocal : C.localLength y f ≤ 1 := by
    rw [← C.finrank_singleton_eq_localLength D hD hC z c ⟨V, hVaff⟩ hVle hzV]
    apply le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ z))
    exact (C.intersectionDegree_eq_sum_points'' D hD hC).symm ▸ hdegree
  have hf : f ≠ 0 := C.germ_restrictedCoefficient_ne_zero y D hD hC c hzc
  have hfinite : Module.length (C.toScheme.presheaf.stalk y)
      (C.toScheme.presheaf.stalk y ⧸ Ideal.span {f}) ≠ ⊤ :=
    KltDP.RingTheory.dvr_length_quotient_span_ne_top _ f hf
  let e := C.intersectionStalkQuotientEquiv' D hD hC c ⟨V, hVaff⟩ hVle z hzV
  letI : Nontrivial (C.toScheme.presheaf.stalk y ⧸ Ideal.span {f}) :=
    e.surjective.nontrivial
  change (Module.length (C.toScheme.presheaf.stalk y)
    (C.toScheme.presheaf.stalk y ⧸ Ideal.span {f})).toNat ≤ 1 at hlocal
  have hle : Module.length (C.toScheme.presheaf.stalk y)
      (C.toScheme.presheaf.stalk y ⧸ Ideal.span {f}) ≤ 1 := by
    rw [← ENat.coe_toNat hfinite]
    exact_mod_cast hlocal
  have hone : Module.length (C.toScheme.presheaf.stalk y)
      (C.toScheme.presheaf.stalk y ⧸ Ideal.span {f}) = 1 :=
    le_antisymm hle (Order.one_le_iff_pos.mpr Module.length_pos)
  have hmax : (Ideal.span ({f} : Set (C.toScheme.presheaf.stalk y))).IsMaximal := by
    rw [Ideal.isMaximal_def, ← isSimpleModule_iff_isCoatom]
    exact Module.length_eq_one_iff.mp hone
  exact IsLocalRing.eq_maximalIdeal hmax

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

#print axioms KltDP.Geometry.NormalProjectiveSurface.PrimeCurve.restrictedCoefficient_span_eq_maximalIdeal_of_degree_le_one

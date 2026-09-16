import KltDP.Geometry.PrimeCurveIntersectionLocalLength
import KltDP.Geometry.PrimeCurveIntersectionNumber
import KltDP.Geometry.PrimeCurveCartierVanishingIdeal
import KltDP.Geometry.PrimeCurveIntersectionSymm
import KltDP.Geometry.PrimeCurveInclusionLift
import KltDP.Geometry.PrimeCurveCodimension
import KltDP.Geometry.ClosedImmersionKerDegree
import KltDP.Geometry.EffectiveCartierIdeal
import KltDP.Geometry.CartierPicardHom
import KltDP.Geometry.DivisorOrderLength

/-!
# Prime curves meeting in at most one point (BRIEF19, item 1)

Let `X` be a normal projective surface over an algebraically closed field `k`, regular at every
point (`hregular`), and let `C`, `D` be prime curves of `X`; `D_D := primeCurveCartier D` is lane D's
Cartier divisor with Weil divisor `1·D`.

* **Separation.** If `C ∩ D` has at most one point, `C` is not contained in `D` (a prime curve is not
  a single point: its generic point is not closed, accepted `not_isClosed_singleton_genericPoint`),
  hence `C` is not in the support of `D_D` (`notInSupport_primeCurveCartier_of_subsingleton`; the
  support of `D_D` is `D`, accepted `primeCurveCartier_support`).
* **Symmetry on classes.** Then `C · [D_D] = D · [D_C]` for lane D's restriction-degree pairing
  (`picardRestrictionDegreeHom_primeCurveCartier_symm`, from the accepted F03 symmetry
  `intersectionNumber_symm`).
* **The Cartier class of a curve given by a closed immersion.** If the carrier of `P` is the range of
  a closed immersion `ι` with reduced source and `L` is an invertible sheaf whose module is the kernel
  ideal of `ι`, then `O(−D_P)` and `L` have the same Picard class and `[D_P] = −[L]`
  (`toPic_neg_primeCurveCartier_of_kernel`, `cartierPicardHom_primeCurveCartier_of_kernel`): accepted
  `effectiveCartierKernelIso`, `primeCurveCartier_idealData_eq_vanishingIdeal`,
  `PrimeCurveInclusionLift.ker_eq_vanishingIdeal`, `kernelIsoOfKerEq` (the argument of the accepted
  `negativeCartierKernelIso` for the newest exceptional curve, made generic).
* **Local length one.** If `C ∩ D = {q}`, `C ⊄ Supp D_D`, the stalks of `C` at the points over `q`
  are discrete valuation rings, and there the restricted local equations of `D_D` are irreducible
  (uniformizers), then `C · D_D = 1` (`intersectionNumber_primeCurveCartier_eq_one`): in the accepted
  F03 formula `intersectionDegree = Σ_z dim_k Γ(C ∩ D, {z})` (`intersectionDegree_eq_sum_points''`)
  the intersection subscheme has the single point over `q`, where the dimension is the local length
  of the restricted equation (`finrank_singleton_eq_localLength`), and
  `length O_{C,y} ⧸ (ϖ) = 1` for a uniformizer `ϖ` (`dvr_length_quotient_uniformizer_pow`). The DVR
  hypothesis is imposed only at the points over `q` (the stalk at the generic point is a field).

Not proved here: the derivation of the uniformizer hypothesis from lane F's `TransversalCrossing`
(local equations generating the maximal ideal of `O_{X,q}`), through `O_{C,y} = O_{X,q} ⧸ (I_C)_q`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.PrimeCurveTransversalPoint

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

/-! ## Curves meeting in at most one point -/

section Separation

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k}

/-- A prime curve is not contained in a set with at most one point. -/
theorem not_subset_of_subsingleton (C : X.PrimeCurve) {S : Set X.toScheme} (hS : S.Subsingleton) :
    ¬ (C : Set X.toScheme) ⊆ S := by
  intro hsub
  have hC : (C : Set X.toScheme) = {C.genericPoint} :=
    (hS.anti hsub).eq_singleton_of_mem (SetLike.mem_coe.mpr C.genericPoint_mem)
  apply C.not_isClosed_singleton_genericPoint
  rw [← hC]
  exact C.isClosed

variable [IsAlgClosed k] (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- **`C ⊄ Supp D_D`** when `C ∩ D` has at most one point. -/
theorem notInSupport_primeCurveCartier_of_subsingleton (C D : X.PrimeCurve)
    (hCD : ((C : Set X.toScheme) ∩ D).Subsingleton) :
    C.NotInSupport (X.primeCurveCartier hregular D)
      (X.primeCurveCartier_hasRegularEquations hregular D) := by
  show C.genericPoint ∉ (effectiveCartierIdealDataOfRegularEquations X.toScheme
    (X.primeCurveCartier hregular D) (X.primeCurveCartier_hasRegularEquations hregular D)).support
  intro hmem
  have hD : C.genericPoint ∈ (D : Set X.toScheme) := by
    rw [← X.primeCurveCartier_support hregular D]
    exact SetLike.mem_coe.mpr hmem
  have hsub : (C : Set X.toScheme) ⊆ D := by
    rw [← C.closure_genericPoint]
    exact closure_minimal (Set.singleton_subset_iff.mpr hD) D.isClosed
  exact not_subset_of_subsingleton C hCD (Set.subset_inter Set.Subset.rfl hsub)

/-- **Symmetry of the pairing on the Cartier classes of two prime curves meeting in at most one
point**: `C · [D_D] = D · [D_C]`. -/
theorem picardRestrictionDegreeHom_primeCurveCartier_symm (C D : X.PrimeCurve)
    (hCD : ((C : Set X.toScheme) ∩ D).Subsingleton) :
    X.picardRestrictionDegreeHom C (cartierPicardHom X.toScheme (X.primeCurveCartier hregular D)) =
      X.picardRestrictionDegreeHom D (cartierPicardHom X.toScheme (X.primeCurveCartier hregular C)) := by
  have hDC : ((D : Set X.toScheme) ∩ C).Subsingleton := by
    rw [Set.inter_comm]
    exact hCD
  rw [C.picardRestrictionDegreeHom_cartierPicardHom, D.picardRestrictionDegreeHom_cartierPicardHom]
  exact X.intersectionNumber_symm hregular C D
    (notInSupport_primeCurveCartier_of_subsingleton hregular C D hCD)
    (notInSupport_primeCurveCartier_of_subsingleton hregular D C hDC)

end Separation

/-! ## The Cartier class of a curve given by a closed immersion -/

section KernelClass

variable {k : Type u} [Field k] [IsAlgClosed k] {X : NormalProjectiveSurface k}
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- The divisor ideal of `D_P` is the kernel of a closed immersion onto `P` with reduced source. -/
theorem primeCurveCartier_ker_eq_of_range (P : X.PrimeCurve) {Y : Scheme.{u}} (ι : Y ⟶ X.toScheme)
    [IsClosedImmersion ι] [AlgebraicGeometry.IsReduced Y]
    (hP : (P : Set X.toScheme) = Set.range ι.base) :
    (effectiveCartierIdealDataOfRegularEquations X.toScheme (X.primeCurveCartier hregular P)
        (X.primeCurveCartier_hasRegularEquations hregular P)).gluedTo.ker = ι.ker := by
  rw [effectiveCartierIdealDataOfRegularEquations_ker,
    X.primeCurveCartier_idealData_eq_vanishingIdeal hregular P,
    PrimeCurveInclusionLift.ker_eq_vanishingIdeal P ι hP]

/-- `O(−D_P)` and an invertible sheaf whose module is the kernel ideal of a closed immersion onto `P`
have the same Picard class. -/
theorem toPic_neg_primeCurveCartier_of_kernel (P : X.PrimeCurve) {Y : Scheme.{u}}
    (ι : Y ⟶ X.toScheme) [IsClosedImmersion ι] [AlgebraicGeometry.IsReduced Y]
    (hP : (P : Set X.toScheme) = Set.range ι.base) (L : InvertibleSheaf X.toScheme)
    (hL : L.obj = schemeKernelIdeal ι) :
    (cartierDivisorInvertibleSheaf X.toScheme (-(X.primeCurveCartier hregular P))).toPic =
      L.toPic := by
  letI := Scheme.Modules.monoidalCategory X.toScheme
  apply Units.ext
  change ((cartierDivisorInvertibleSheaf X.toScheme (-(X.primeCurveCartier hregular P))).toPic :
      Skeleton X.toScheme.Modules) = (L.toPic : Skeleton X.toScheme.Modules)
  rw [InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val]
  exact Quotient.sound ⟨effectiveCartierKernelIso X.toScheme (X.primeCurveCartier hregular P)
      (X.primeCurveCartier_hasRegularEquations hregular P) ≪≫
    kernelIsoOfKerEq _ ι (primeCurveCartier_ker_eq_of_range hregular P ι hP) ≪≫ eqToIso hL.symm⟩

/-- **The Cartier class of `D_P` is `−[L]`** for an invertible sheaf `L` whose module is the kernel
ideal of a closed immersion onto `P` (the ideal-sheaf sign convention of the tower classes). -/
theorem cartierPicardHom_primeCurveCartier_of_kernel (P : X.PrimeCurve) {Y : Scheme.{u}}
    (ι : Y ⟶ X.toScheme) [IsClosedImmersion ι] [AlgebraicGeometry.IsReduced Y]
    (hP : (P : Set X.toScheme) = Set.range ι.base) (L : InvertibleSheaf X.toScheme)
    (hL : L.obj = schemeKernelIdeal ι) :
    cartierPicardHom X.toScheme (X.primeCurveCartier hregular P) = -Additive.ofMul L.toPic := by
  have h2 : cartierPicardHom X.toScheme (-(X.primeCurveCartier hregular P)) =
      Additive.ofMul L.toPic := by
    change Additive.ofMul (cartierPicardClass X.toScheme (-(X.primeCurveCartier hregular P))) = _
    rw [cartierPicardClass]
    exact congrArg Additive.ofMul (toPic_neg_primeCurveCartier_of_kernel hregular P ι hP L hL)
  rw [← h2, map_neg, neg_neg]

end KernelClass

/-! ## Local length one at a single transversal point -/

section Transversal

variable {k : Type u} [Field k] [IsAlgClosed k] {X : NormalProjectiveSurface k}
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x) (C D : X.PrimeCurve)

/-- Stalks of the integral curve scheme are domains (needed by the DVR predicate; the accepted
`integralSchemeStalk_isDomain`). -/
local instance transversalPoint_stalkIsDomain (y : C.toScheme) :
    IsDomain (C.toScheme.presheaf.stalk y) :=
  integralSchemeStalk_isDomain C.toScheme y

omit [IsAlgClosed k] in
/-- The local length of a uniformizer is one. -/
theorem localLength_eq_one_of_irreducible (y : C.toScheme)
    [IsDiscreteValuationRing (C.toScheme.presheaf.stalk y)]
    (f : C.toScheme.presheaf.stalk y) (hf : Irreducible f) : C.localLength y f = 1 := by
  unfold PrimeCurve.localLength
  have h := KltDP.RingTheory.dvr_length_quotient_uniformizer_pow (C.toScheme.presheaf.stalk y) f hf 1
  rw [pow_one] at h
  rw [h]
  exact ENat.toNat_coe 1

variable (q : X.toScheme)
  (hC : C.NotInSupport (X.primeCurveCartier hregular D)
    (X.primeCurveCartier_hasRegularEquations hregular D))

/-- Every point of the intersection subscheme `C ∩ D` lies over the intersection. -/
theorem intersectionToSurface_base_mem (z : C.intersectionScheme (X.primeCurveCartier hregular D)
    (X.primeCurveCartier_hasRegularEquations hregular D) hC) :
    (C.intersectionToSurface _ _ hC).base z ∈ (C : Set X.toScheme) ∩ D := by
  have h : (C.intersectionToSurface _ _ hC).base z ∈
      Set.range (C.intersectionToSurface (X.primeCurveCartier hregular D)
        (X.primeCurveCartier_hasRegularEquations hregular D) hC).base := ⟨z, rfl⟩
  rw [C.range_intersectionToSurface, X.primeCurveCartier_support hregular D] at h
  exact h

include hregular hC in
/-- If `C ∩ D = {q}`, the intersection subscheme has at most one point. -/
theorem intersectionScheme_subsingleton (hCD : (C : Set X.toScheme) ∩ D = {q}) :
    Subsingleton (C.intersectionScheme (X.primeCurveCartier hregular D)
      (X.primeCurveCartier_hasRegularEquations hregular D) hC) := by
  refine ⟨fun z w => (C.intersectionToSurface _ _ hC).isClosedEmbedding.injective ?_⟩
  have hz := intersectionToSurface_base_mem hregular C D hC z
  have hw := intersectionToSurface_base_mem hregular C D hC w
  rw [hCD] at hz hw
  exact hz.trans hw.symm

include hregular hC in
/-- If `C ∩ D = {q}`, the intersection subscheme has a point over `q`. -/
theorem exists_intersection_point (hCD : (C : Set X.toScheme) ∩ D = {q}) :
    ∃ z : C.intersectionScheme (X.primeCurveCartier hregular D)
      (X.primeCurveCartier_hasRegularEquations hregular D) hC,
      (C.intersectionToSurface _ _ hC).base z = q := by
  have hq : q ∈ Set.range (C.intersectionToSurface (X.primeCurveCartier hregular D)
      (X.primeCurveCartier_hasRegularEquations hregular D) hC).base := by
    rw [C.range_intersectionToSurface, X.primeCurveCartier_support hregular D, hCD]
    exact Set.mem_singleton q
  exact hq

include hC in
/-- **`C · D_D = 1` for prime curves meeting at a single point where the restricted local equation of
`D_D` is a uniformizer**: `C ∩ D = {q}`, `C ⊄ Supp D_D`, the stalks of `C` at the points over `q` are
discrete valuation rings, and there the restricted local equations of `D_D` are irreducible. -/
theorem intersectionNumber_primeCurveCartier_eq_one (hCD : (C : Set X.toScheme) ∩ D = {q})
    (hDVR : ∀ y : C.toScheme, C.inclusion.base y = q →
      IsDiscreteValuationRing (C.toScheme.presheaf.stalk y))
    (htrans : ∀ (y : C.toScheme), C.inclusion.base y = q →
      ∀ (c : RegularCartierEquationChart X.toScheme (X.primeCurveCartier hregular D))
        (hy : y ∈ C.chartPreimage (X.primeCurveCartier hregular D) c),
        Irreducible (C.toScheme.presheaf.germ (C.chartPreimage (X.primeCurveCartier hregular D) c)
          y hy (C.restrictedCoefficient (X.primeCurveCartier hregular D) c))) :
    C.intersectionNumber (X.primeCurveCartier hregular D) = 1 := by
  set D' := X.primeCurveCartier hregular D with hD'
  set hD := X.primeCurveCartier_hasRegularEquations hregular D
  haveI := intersectionScheme_subsingleton hregular C D q hC hCD
  obtain ⟨z₀, hz₀⟩ := exists_intersection_point hregular C D q hC hCD
  have hzq : C.inclusion.base ((C.intersectionInclusion D' hD hC).base z₀) = q := hz₀
  haveI := hDVR _ hzq
  haveI := C.intersectionScheme_finite' D' hD hC
  letI : Fintype (C.intersectionScheme D' hD hC) := Fintype.ofFinite _
  letI : DiscreteTopology (C.intersectionScheme D' hD hC) :=
    DiscreteTopology.of_finite_of_isClosed_singleton
      (C.intersectionScheme_isClosed_singleton' D' hD hC)
  obtain ⟨c, hzc⟩ := C.exists_genericChart D' hD ((C.intersectionInclusion D' hD hC).base z₀)
  obtain ⟨_, ⟨V, hVaff, rfl⟩, hzV, hVle⟩ :=
    (isBasis_affine_open C.toScheme).exists_subset_of_mem_open hzc (C.chartPreimage D' c.1).2
  have h1 := C.finrank_singleton_eq_localLength D' hD hC z₀ c ⟨V, hVaff⟩ hVle hzV
  rw [localLength_eq_one_of_irreducible C _ _ (htrans _ hzq c.1 (hVle hzV))] at h1
  rw [C.intersectionNumber_eq_intersectionDegree D' hD hC,
    C.intersectionDegree_eq_sum_points'' D' hD hC,
    Finset.sum_eq_single_of_mem z₀ (Finset.mem_univ z₀)
      (fun z _ hz => absurd (Subsingleton.elim z z₀) hz)]
  exact (congrArg (Nat.cast : ℕ → ℤ) h1).trans Nat.cast_one

end Transversal

end KltDP.Geometry.PrimeCurveTransversalPoint

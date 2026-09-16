import KltDP.Geometry.CurveEffectiveCartierDegree
import KltDP.Geometry.PrimeCurveIntersectionZero
import KltDP.Geometry.SectionEffectiveCartier
import KltDP.Geometry.ProperGlobalSectionsConstants
import KltDP.Geometry.SchemeKernelIdealIsoTransport
import KltDP.Geometry.InvertibleSheafSectionPowers

/-!
# Degree-zero line bundles on actual integral proper curves are not big

A nonzero original section gives an actual effective Cartier divisor E.
Its support misses the generic point, so the existing dimension-one
closed-subset theorem makes its zero scheme finite with closed points.
The original ideal sequence and tensor-degree law give deg O(E)=dim Γ(E).
Degree zero forces this scheme to be empty; its ideal sequence then
trivializes O(-E), hence O(E) and the original line bundle's Picard class.

The actual proper global-functions theorem gives h⁰(O)=1 over the
algebraically closed original base. Thus every degree-zero line bundle,
including each original tensor power, has at most one section dimension.
This contradicts the positive linear growth in the existing `IsBig`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.CurveDegreeZeroNotBig

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y]
  (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]
  (hdim : topologicalKrullDim Y ≤ 1)

include f hdim in
private theorem effectiveCartier_finite_and_closed (E : CartierDivisor Y)
    (hE : HasRegularCartierEquations Y E) :
    Finite (effectiveCartierScheme Y E hE) ∧
      ∀ z : effectiveCartierScheme Y E hE, IsClosed ({z} : Set _) := by
  letI : IsNoetherian Y := isNoetherian_of_finiteType_toSpec f
  let I := effectiveCartierIdealDataOfRegularEquations Y E hE
  have hη : genericPoint Y ∉ I.support := by
    obtain ⟨c, hc⟩ := hE (genericPoint Y)
    intro hmem
    have hu : IsUnit (Y.germToFunctionField c.chart.openSet c.coefficient) := by
      rw [c.germ_eq]
      exact c.chart.equation.isUnit
    exact (NormalProjectiveSurface.PrimeCurve.mem_support_iff_not_isUnit_germ
      E hE c _ hc).mp hmem hu
  have hne : (I.support : Set Y) ≠ Set.univ := by
    intro h
    apply hη
    change genericPoint Y ∈ (I.support : Set Y)
    rw [h]
    exact Set.mem_univ _
  obtain ⟨hfin, hclosed⟩ :=
    KltDP.Topology.finite_and_isClosed_singleton_of_isClosed_of_ne_univ
      hdim I.isClosed_supportSet hne
  let i := effectiveCartierInclusion Y E hE
  have hrange : Set.range i.base = (I.support : Set Y) :=
    range_effectiveCartierInclusion Y E hE
  have hfinRange : (Set.range i.base).Finite := hrange.symm ▸ hfin
  have hinj : Function.Injective i.base :=
    (IsClosedImmersion.base_closed (f := i)).toIsEmbedding.injective
  constructor
  · letI := hfinRange.to_subtype
    exact Finite.of_injective
      (fun z => (⟨i.base z, Set.mem_range_self z⟩ : Set.range i.base))
      (fun _ _ h => hinj (Subtype.ext_iff.mp h))
  · intro z
    rw [(IsClosedImmersion.base_closed (f := i)).isClosed_iff_image_isClosed,
      Set.image_singleton]
    apply hclosed
    change i.base z ∈ (I.support : Set Y)
    rw [← hrange]
    exact Set.mem_range_self z

private abbrev divisorPushforward (E : CartierDivisor Y)
    (hE : HasRegularCartierEquations Y E) : Y.Modules :=
  (schemeModulePushforward (effectiveCartierInclusion Y E hE)).obj
    (_root_.SheafOfModules.unit (effectiveCartierScheme Y E hE).ringCatSheaf)

private theorem divisorPushforward_hZero (E : CartierDivisor Y)
    (hE : HasRegularCartierEquations Y E) :
    cohomologyDimension f (divisorPushforward E hE) 0 =
      effectiveCartierDegree Y E hE f := by
  letI := baseRingModule f (divisorPushforward E hE) 0
  letI := baseRingModule ((effectiveCartierInclusion Y E hE) ≫ f)
    (_root_.SheafOfModules.unit (effectiveCartierScheme Y E hE).ringCatSheaf) 0
  exact (pushforwardHZeroBaseRingLinearEquiv (effectiveCartierInclusion Y E hE) f
    (_root_.SheafOfModules.unit (effectiveCartierScheme Y E hE).ringCatSheaf)).finrank_eq

private theorem divisorPushforward_hZero_finite (E : CartierDivisor Y)
    (hE : HasRegularCartierEquations Y E) :
    FiniteDimensional k ((baseFunctor f 0).obj (divisorPushforward E hE)) := by
  letI := baseRingModule f (divisorPushforward E hE) 0
  letI := baseRingModule ((effectiveCartierInclusion Y E hE) ≫ f)
    (_root_.SheafOfModules.unit (effectiveCartierScheme Y E hE).ringCatSheaf) 0
  haveI : FiniteDimensional k
      (H (_root_.SheafOfModules.unit (effectiveCartierScheme Y E hE).ringCatSheaf) 0) :=
    effectiveCartierDegree_finiteDimensional Y E hE f
  exact (pushforwardHZeroBaseRingLinearEquiv (effectiveCartierInclusion Y E hE) f
    (_root_.SheafOfModules.unit (effectiveCartierScheme Y E hE).ringCatSheaf)).symm.finiteDimensional

include hdim in
/-- The existing effective-divisor degree computation on an arbitrary
integral proper scheme of dimension at most one. -/
theorem eulerDifference_cartier_eq_effectiveDegree (E : CartierDivisor Y)
    (hE : HasRegularCartierEquations Y E) :
    eulerCharacteristic f (cartierDivisorModule Y E) -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf) =
        (effectiveCartierDegree Y E hE f : ℤ) := by
  obtain ⟨hfinite, hclosed⟩ := effectiveCartier_finite_and_closed f hdim E hE
  letI := hfinite
  have hone : Subsingleton (H (divisorPushforward E hE) 1) :=
    pushforwardUnit_cohomology_succ_subsingleton
      (effectiveCartierInclusion Y E hE) hclosed 0
  have hχ : eulerCharacteristic f (divisorPushforward E hE) =
      (effectiveCartierDegree Y E hE f : ℤ) := by
    letI := hone
    rw [proper_eulerCharacteristic_eq_h0_sub_h1 f hdim,
      divisorPushforward_hZero, cohomologyDimension_eq_zero_of_subsingleton]
    simp
  letI : IsLocallyNoetherian Y := isLocallyNoetherian_of_locallyOfFiniteType_toSpec f
  letI : IsCoherentModule (cartierDivisorModule Y (-E)) :=
    (cartierDivisorInvertibleSheaf Y (-E)).isCoherent
  letI : IsCoherentModule (_root_.SheafOfModules.unit Y.ringCatSheaf) :=
    (InvertibleSheaf.trivial Y).isCoherent
  have hP1 : FiniteDimensional k ((baseFunctor f 1).obj (divisorPushforward E hE)) := by
    letI := baseModule f (divisorPushforward E hE) 1
    letI : Subsingleton ((baseFunctor f 1).obj (divisorPushforward E hE)) := hone
    exact Module.Finite.of_surjective (0 : k →ₗ[k] H (divisorPushforward E hE) 1)
      (fun y => ⟨0, Subsingleton.elim _ _⟩)
  have hadd := proper_eulerCharacteristic_additive_of_dimension_le_one f hdim
    (effectiveCartierSequence Y E hE)
    (effectiveCartierSequence_shortExact Y E hE
      (effectiveCartier_structureToPushforwardUnit_epi Y E hE))
    ⟨KltDP.AdmissionProbe.ProperCohomologyConsumers.proper_baseFunctor_finiteDimensional f
        (cartierDivisorModule Y (-E)) 0,
      KltDP.AdmissionProbe.ProperCohomologyConsumers.proper_baseFunctor_finiteDimensional f
        (cartierDivisorModule Y (-E)) 1⟩
    ⟨KltDP.AdmissionProbe.ProperCohomologyConsumers.proper_baseFunctor_finiteDimensional f
        (_root_.SheafOfModules.unit Y.ringCatSheaf) 0,
      KltDP.AdmissionProbe.ProperCohomologyConsumers.proper_baseFunctor_finiteDimensional f
        (_root_.SheafOfModules.unit Y.ringCatSheaf) 1⟩
    ⟨divisorPushforward_hZero_finite f E hE, hP1⟩
  change eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf) =
    eulerCharacteristic f (cartierDivisorModule Y (-E)) +
      eulerCharacteristic f (divisorPushforward E hE) at hadd
  have hsum := KltDP.AdmissionProbe.CurveTensorDegreeConsumers.proper_picardEulerDifference_mul
    f hdim (cartierPicardClass Y E) (cartierPicardClass Y (-E))
  rw [← cartierPicardClass_add, add_neg_cancel, cartierPicardClass_zero,
    picardEulerValue_one] at hsum
  change _ = (picardEulerValue f (cartierDivisorInvertibleSheaf Y E).toPic -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)) +
    (picardEulerValue f (cartierDivisorInvertibleSheaf Y (-E)).toPic -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)) at hsum
  rw [picardEulerValue_toPic, picardEulerValue_toPic] at hsum
  change _ = (eulerCharacteristic f (cartierDivisorModule Y E) -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)) +
    (eulerCharacteristic f (cartierDivisorModule Y (-E)) -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)) at hsum
  linarith

private theorem isEmpty_of_effectiveDegree_zero (E : CartierDivisor Y)
    (hE : HasRegularCartierEquations Y E)
    (hzero : effectiveCartierDegree Y E hE f = 0) :
    IsEmpty (effectiveCartierScheme Y E hE) := by
  letI := Module.compHom Γ(effectiveCartierScheme Y E hE, ⊤)
    (baseFieldToGlobalSections (effectiveCartierToSpec Y E hE f))
  letI : Module.Finite k Γ(effectiveCartierScheme Y E hE, ⊤) :=
    finite_sections_of_hZero (effectiveCartierToSpec Y E hE f)
      (effectiveCartierDegree_finiteDimensional Y E hE f)
  have hfin : Module.finrank k Γ(effectiveCartierScheme Y E hE, ⊤) = 0 :=
    (effectiveCartierDegree_eq_finrank_sections Y E hE f).symm.trans hzero
  exact NormalProjectiveSurface.PrimeCurve.scheme_isEmpty_of_subsingleton_sections _
    (Module.finrank_zero_iff.mp hfin)

private theorem structureMap_eq_zero_of_isEmpty {Z : Scheme.{u}} [IsEmpty Z]
    (i : Z ⟶ Y) : structureToPushforwardUnit i = 0 := by
  apply _root_.SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  let V := (Opens.map i.base).obj U.unop
  haveI : Subsingleton Γ(Z, V) :=
    CommRingCat.subsingleton_of_isTerminal (Z.sheaf.isTerminalOfEqEmpty (by
      ext z
      exact isEmptyElim z))
  change (i.app U.unop s : Γ(Z, V)) = 0
  exact Subsingleton.elim _ _

private def zeroCartierIsoUnit :
    cartierDivisorModule Y 0 ≅ _root_.SheafOfModules.unit Y.ringCatSheaf := by
  have h : principalCartierDivisorHom Y
      (Additive.ofMul (1 : Y.functionFieldˣ)) = 0 := by simp
  exact h ▸ principalCartierModuleIsoUnit Y 1

include hdim in
/-- A nonzero actual section of a degree-zero line bundle trivializes
its actual Picard class; no section bound or trivialization is assumed. -/
theorem toPic_eq_one_of_nonzero_section_of_degree_zero (L : InvertibleSheaf Y)
    (hdeg : eulerCharacteristic f L.obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf) = 0)
    (s : sections L.obj) (hs : s ≠ 0) : L.toPic = 1 := by
  obtain ⟨E, hE, e, _⟩ := exists_effectiveCartier_of_nonzero_section Y L s hs
  have hzero : effectiveCartierDegree Y E hE f = 0 := by
    have h := eulerDifference_cartier_eq_effectiveDegree f hdim E hE
    rw [eulerCharacteristic_eq_of_iso f e, hdeg] at h
    exact_mod_cast h.symm
  letI := isEmpty_of_effectiveDegree_zero f E hE hzero
  let eneg : cartierDivisorModule Y (-E) ≅
      _root_.SheafOfModules.unit Y.ringCatSheaf :=
    effectiveCartierKernelIso Y E hE ≪≫
      kernelIsoOfEq (structureMap_eq_zero_of_isEmpty (effectiveCartierInclusion Y E hE)) ≪≫
      kernelZeroIsoSource
  have hneg : cartierPicardClass Y (-E) = cartierPicardClass Y 0 :=
    SchemeKernelIdealIsoTransport.toPic_eq_of_iso
      (cartierDivisorInvertibleSheaf Y (-E)) (cartierDivisorInvertibleSheaf Y 0)
      (eneg ≪≫ zeroCartierIsoUnit.symm)
  rw [cartierPicardClass_neg, cartierPicardClass_zero, inv_eq_one] at hneg
  have hclass : cartierPicardClass Y E = L.toPic :=
    SchemeKernelIdealIsoTransport.toPic_eq_of_iso (cartierDivisorInvertibleSheaf Y E) L e
  exact hclass.symm.trans hneg

variable [IsAlgClosed k]

private theorem picardHZero_one : Positivity.picardHZero f (1 : Y.Pic) = 1 := by
  rw [← cartierPicardClass_zero Y]
  change Positivity.picardHZero f (cartierDivisorInvertibleSheaf Y 0).toPic = 1
  rw [Positivity.picardHZero_toPic]
  change cohomologyDimension f (cartierDivisorModule Y 0) 0 = 1
  rw [cohomologyDimension_eq_of_iso f zeroCartierIsoUnit 0]
  exact (cohomologyDimension_zero_unit_eq_finrank f).trans (globalSections_finrank_one f)

include hdim in
/-- The original global-section dimension of a degree-zero invertible
sheaf on an actual integral proper curve is at most one. -/
theorem hZero_le_one (L : InvertibleSheaf Y)
    (hdeg : eulerCharacteristic f L.obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf) = 0) :
    cohomologyDimension f L.obj 0 ≤ 1 := by
  classical
  by_cases hsec : ∃ s : sections L.obj, s ≠ 0
  · obtain ⟨s, hs⟩ := hsec
    have hvalue : cohomologyDimension f L.obj 0 = 1 := by
      rw [← Positivity.picardHZero_toPic f L,
        toPic_eq_one_of_nonzero_section_of_degree_zero f hdim L hdeg s hs,
        picardHZero_one]
    exact hvalue.le
  · haveI : Subsingleton (sections L.obj) := ⟨fun s t => by
      have hz : ∀ a : sections L.obj, a = 0 := fun a => by
        by_cases ha : a = 0
        · exact ha
        · exact False.elim (hsec ⟨a, ha⟩)
      exact (hz s).trans (hz t).symm⟩
    letI := baseSectionsModule f L.obj
    rw [cohomologyDimension_zero_eq_finrank_sections, Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _

include hdim in
private theorem picardEulerDifference_pow (p : Y.Pic) (n : ℕ) :
    picardEulerValue f (p ^ n) - picardEulerValue f 1 =
      (n : ℤ) * (picardEulerValue f p - picardEulerValue f 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,
      KltDP.AdmissionProbe.CurveTensorDegreeConsumers.proper_picardEulerDifference_mul
        f hdim, ih, Nat.cast_succ]
    ring

include hdim in
/-- Every actual tensor power retains degree zero and has at most one
global-section dimension for the original base-field action. -/
theorem picardHZero_pow_le_one (L : InvertibleSheaf Y)
    (hdeg : eulerCharacteristic f L.obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf) = 0) (n : ℕ) :
    Positivity.picardHZero f (L.toPic ^ n) ≤ 1 := by
  let M := InvertibleSheafSectionPowers.power L n
  have hclass : M.toPic = L.toPic ^ n := InvertibleSheafSectionPowers.power_toPic L n
  have hM : eulerCharacteristic f M.obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf) = 0 := by
    have h := picardEulerDifference_pow f hdim L.toPic n
    rw [← hclass, picardEulerValue_toPic, picardEulerValue_toPic,
      picardEulerValue_one, hdeg, mul_zero] at h
    exact h
  rw [← hclass, Positivity.picardHZero_toPic]
  exact hZero_le_one f hdim M hM

/-- Degree zero excludes the original positive-growth definition of
bigness on a one-dimensional integral proper scheme. -/
theorem not_isBig (hdimOne : topologicalKrullDim Y = 1) (L : InvertibleSheaf Y)
    (hdeg : eulerCharacteristic f L.obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf) = 0) :
    ¬ Positivity.IsBig f L := by
  rintro ⟨c, hc, hgrowth⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / c)
  obtain ⟨n, hn, hbound⟩ := hgrowth N
  have hdimNat : Positivity.natDim Y = 1 := by
    unfold Positivity.natDim
    rw [hdimOne]
    rfl
  rw [hdimNat, pow_one] at hbound
  have hh : (Positivity.picardHZero f (L.toPic ^ n) : ℚ) ≤ 1 := by
    exact_mod_cast picardHZero_pow_le_one f (le_of_eq hdimOne) L hdeg n
  have hnQ : (N : ℚ) ≤ n := by exact_mod_cast hn
  have hcn : (1 : ℚ) < (n : ℚ) * c :=
    (div_lt_iff₀ hc).mp (hN.trans_le hnQ)
  linarith

end KltDP.Geometry.CurveDegreeZeroNotBig

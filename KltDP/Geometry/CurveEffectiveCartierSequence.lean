import KltDP.Geometry.EffectiveCartierDegree
import KltDP.Geometry.PrimeCurveLineDegree
import KltDP.Geometry.ProperCurveEuler
import KltDP.Geometry.SchemeModulePushforwardScalars
import KltDP.Geometry.InvertibleCoherentModule
import KltDP.Geometry.FiniteTypeNoetherian
import KltDP.AdmissionProbe.ProperCohomologyConsumers

/-!
# The ideal sequence of an effective Cartier divisor and the 0AYY Euler computation

For an effective Cartier divisor `E` (regular local equations) on an integral scheme `X`, with
closed immersion `i : E → X`, the accepted kernel comparison `O_X(-E) ≅ ker(O_X → i_*O_E)` gives the
short complex

    O_X(-E) → O_X → i_*O_E

which is exact with monic first map; it is short exact as soon as `O_X → i_*O_E` is an
epimorphism (`hepi`, the surjectivity of the structure map of the closed immersion).

On a prime curve `C`, Euler additivity along this sequence together with
`H⁰(C, i_*O_E) = H⁰(E, O_E)` (the accepted degree-zero pushforward comparison) and the vanishing
of `H¹(C, i_*O_E)` (`hone`) gives the Stacks 0AYY value

    deg O_C(-E) = χ(O_C(-E)) - χ(O_C) = -χ(i_*O_E) = -dim_k Γ(E, O_E) = -effectiveCartierDegree E.

The two inputs `hepi` and `hone` are the remaining lemmas of the plan `F03_DEGREE_0AYY_PLAN.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section Sequence

variable (X : Scheme.{u}) [IsIntegral X] (E : CartierDivisor X)
  (hE : HasRegularCartierEquations X E)

/-- The inclusion `O_X(-E) → O_X` composed with the structure map of the closed immersion is zero. -/
theorem effectiveCartierNegativeInclusion_comp_structure :
    effectiveCartierNegativeInclusion X E hE ≫
      structureToPushforwardUnit (effectiveCartierInclusion X E hE) = 0 := by
  have h1 : effectiveCartierNegativeInclusion X E hE =
      (effectiveCartierKernelIso X E hE).hom ≫
        schemeKernelIdealι (effectiveCartierInclusion X E hE) :=
    (effectiveCartierKernelIso_hom_ι X E hE).symm
  rw [h1, Category.assoc, schemeKernelIdealι_comp, comp_zero]

/-- The short complex `O_X(-E) → O_X → i_*O_E` of the effective Cartier divisor `E`. -/
def effectiveCartierSequence : ShortComplex X.Modules :=
  ShortComplex.mk (effectiveCartierNegativeInclusion X E hE)
    (structureToPushforwardUnit (effectiveCartierInclusion X E hE))
    (effectiveCartierNegativeInclusion_comp_structure X E hE)

/-- The kernel short complex of the structure map, in the standard form. -/
def effectiveCartierKernelSequence : ShortComplex X.Modules :=
  ShortComplex.mk (kernel.ι (structureToPushforwardUnit (effectiveCartierInclusion X E hE)))
    (structureToPushforwardUnit (effectiveCartierInclusion X E hE))
    (kernel.condition (structureToPushforwardUnit (effectiveCartierInclusion X E hE)))

/-- The ideal sequence is isomorphic to the kernel sequence through the accepted kernel
comparison. -/
def effectiveCartierKernelSequenceIso :
    effectiveCartierKernelSequence X E hE ≅ effectiveCartierSequence X E hE :=
  ShortComplex.isoMk (effectiveCartierKernelIso X E hE).symm (Iso.refl _) (Iso.refl _)
    (by
      change (effectiveCartierKernelIso X E hE).inv ≫ effectiveCartierNegativeInclusion X E hE =
        kernel.ι (structureToPushforwardUnit (effectiveCartierInclusion X E hE)) ≫ 𝟙 _
      rw [effectiveCartierKernelIso_inv_ι, Category.comp_id]
      rfl)
    (by
      change 𝟙 _ ≫ structureToPushforwardUnit (effectiveCartierInclusion X E hE) =
        structureToPushforwardUnit (effectiveCartierInclusion X E hE) ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id])

/-- Exactness of `O_X(-E) → O_X → i_*O_E`. -/
theorem effectiveCartierSequence_exact : (effectiveCartierSequence X E hE).Exact :=
  ShortComplex.exact_of_iso (effectiveCartierKernelSequenceIso X E hE)
    (ShortComplex.exact_kernel (structureToPushforwardUnit (effectiveCartierInclusion X E hE)))

/-- The inclusion `O_X(-E) → O_X` is a monomorphism. -/
theorem effectiveCartierNegativeInclusion_mono : Mono (effectiveCartierNegativeInclusion X E hE) := by
  have h1 : effectiveCartierNegativeInclusion X E hE =
      (effectiveCartierKernelIso X E hE).hom ≫
        kernel.ι (structureToPushforwardUnit (effectiveCartierInclusion X E hE)) :=
    (effectiveCartierKernelIso_hom_ι X E hE).symm
  rw [h1]
  exact mono_comp _ _

/-- **The ideal short exact sequence of an effective Cartier divisor**, given that the structure
map `O_X → i_*O_E` of the closed immersion is an epimorphism. -/
theorem effectiveCartierSequence_shortExact
    (hepi : Epi (structureToPushforwardUnit (effectiveCartierInclusion X E hE))) :
    (effectiveCartierSequence X E hE).ShortExact :=
  { exact := effectiveCartierSequence_exact X E hE
    mono_f := effectiveCartierNegativeInclusion_mono X E hE
    epi_g := hepi }

end Sequence

end KltDP.Geometry

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

open KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
  (E : CartierDivisor C.toScheme) (hE : HasRegularCartierEquations C.toScheme E)

/-- The pushforward `i_*O_E` of the structure sheaf of the divisor to the curve. -/
abbrev divisorStructurePushforward : C.toScheme.Modules :=
  (schemeModulePushforward (effectiveCartierInclusion C.toScheme E hE)).obj (_root_.SheafOfModules.unit (effectiveCartierScheme C.toScheme E hE).ringCatSheaf)

/-- `dim_k H⁰(C, i_*O_E) = dim_k H⁰(E, O_E) = effectiveCartierDegree E` (the accepted degree-zero
pushforward comparison, `k`-linear for the composite structure morphism). -/
theorem cohomologyDimension_divisorStructurePushforward_zero :
    cohomologyDimension C.toSpec (C.divisorStructurePushforward E hE) 0 =
      effectiveCartierDegree C.toScheme E hE C.toSpec := by
  letI := baseRingModule C.toSpec (C.divisorStructurePushforward E hE) 0
  letI := baseRingModule ((effectiveCartierInclusion C.toScheme E hE) ≫ C.toSpec) (_root_.SheafOfModules.unit (effectiveCartierScheme C.toScheme E hE).ringCatSheaf) 0
  exact (pushforwardHZeroBaseRingLinearEquiv (effectiveCartierInclusion C.toScheme E hE) C.toSpec (_root_.SheafOfModules.unit (effectiveCartierScheme C.toScheme E hE).ringCatSheaf)).finrank_eq

/-- `H⁰(C, i_*O_E)` is finite dimensional (through the accepted finiteness of `Γ(E, O_E)`). -/
theorem divisorStructurePushforward_hZero_finiteDimensional :
    FiniteDimensional k ((baseFunctor C.toSpec 0).obj (C.divisorStructurePushforward E hE)) := by
  haveI := C.toSpec_isProper
  letI := baseRingModule C.toSpec (C.divisorStructurePushforward E hE) 0
  letI := baseRingModule ((effectiveCartierInclusion C.toScheme E hE) ≫ C.toSpec) (_root_.SheafOfModules.unit (effectiveCartierScheme C.toScheme E hE).ringCatSheaf) 0
  have hfin : FiniteDimensional k (H (_root_.SheafOfModules.unit (effectiveCartierScheme C.toScheme E hE).ringCatSheaf) 0) :=
    effectiveCartierDegree_finiteDimensional C.toScheme E hE C.toSpec
  exact (pushforwardHZeroBaseRingLinearEquiv (effectiveCartierInclusion C.toScheme E hE) C.toSpec (_root_.SheafOfModules.unit (effectiveCartierScheme C.toScheme E hE).ringCatSheaf)).symm.finiteDimensional

/-- `χ(i_*O_E) = effectiveCartierDegree E` once `H¹(C, i_*O_E)` vanishes. -/
theorem eulerCharacteristic_divisorStructurePushforward
    (hone : Subsingleton (H (C.divisorStructurePushforward E hE) 1)) :
    eulerCharacteristic C.toSpec (C.divisorStructurePushforward E hE) =
      (effectiveCartierDegree C.toScheme E hE C.toSpec : ℤ) := by
  haveI := hone
  rw [C.eulerCharacteristic_eq_h0_sub_h1, C.cohomologyDimension_divisorStructurePushforward_zero E hE,
    cohomologyDimension_eq_zero_of_subsingleton C.toSpec (C.divisorStructurePushforward E hE) 1]
  simp

/-- Euler additivity along `0 → O_C(-E) → O_C → i_*O_E → 0` on the prime curve. -/
theorem eulerCharacteristic_unit_eq_add
    (hepi : Epi (structureToPushforwardUnit (effectiveCartierInclusion C.toScheme E hE)))
    (hone : Subsingleton (H (C.divisorStructurePushforward E hE) 1)) :
    eulerCharacteristic C.toSpec (_root_.SheafOfModules.unit C.toScheme.ringCatSheaf) =
      eulerCharacteristic C.toSpec (cartierDivisorModule C.toScheme (-E)) +
        eulerCharacteristic C.toSpec (C.divisorStructurePushforward E hE) := by
  haveI := C.toSpec_isProper
  haveI : IsLocallyNoetherian C.toScheme :=
    isLocallyNoetherian_of_locallyOfFiniteType_toSpec C.toSpec
  haveI : IsCoherentModule (cartierDivisorModule C.toScheme (-E)) :=
    (cartierDivisorInvertibleSheaf C.toScheme (-E)).isCoherent
  haveI : IsCoherentModule (_root_.SheafOfModules.unit C.toScheme.ringCatSheaf) :=
    (InvertibleSheaf.trivial C.toScheme).isCoherent
  have hdim : topologicalKrullDim C.toScheme ≤ 1 := le_of_eq C.dimension_one_toScheme
  have h1 : FiniteDimensional k
      ((baseFunctor C.toSpec 1).obj (C.divisorStructurePushforward E hE)) := by
    letI := baseModule C.toSpec (C.divisorStructurePushforward E hE) 1
    letI : Subsingleton ((baseFunctor C.toSpec 1).obj (C.divisorStructurePushforward E hE)) := hone
    exact Module.Finite.of_surjective (0 : k →ₗ[k] H (C.divisorStructurePushforward E hE) 1)
      (fun y => ⟨0, Subsingleton.elim _ _⟩)
  exact proper_eulerCharacteristic_additive_of_dimension_le_one C.toSpec hdim
    (effectiveCartierSequence C.toScheme E hE) (effectiveCartierSequence_shortExact C.toScheme E hE hepi)
    ⟨KltDP.AdmissionProbe.ProperCohomologyConsumers.proper_baseFunctor_finiteDimensional C.toSpec
        (cartierDivisorModule C.toScheme (-E)) 0,
      KltDP.AdmissionProbe.ProperCohomologyConsumers.proper_baseFunctor_finiteDimensional C.toSpec
        (cartierDivisorModule C.toScheme (-E)) 1⟩
    ⟨KltDP.AdmissionProbe.ProperCohomologyConsumers.proper_baseFunctor_finiteDimensional C.toSpec
        (_root_.SheafOfModules.unit C.toScheme.ringCatSheaf) 0,
      KltDP.AdmissionProbe.ProperCohomologyConsumers.proper_baseFunctor_finiteDimensional C.toSpec
        (_root_.SheafOfModules.unit C.toScheme.ringCatSheaf) 1⟩
    ⟨C.divisorStructurePushforward_hZero_finiteDimensional E hE, h1⟩

/-- **Stacks 0AYY for `O_C(-E)`**, conditional on the two remaining inputs: the degree of
`O_C(-E)` is minus the degree `dim_k Γ(E, O_E)` of the effective Cartier divisor. -/
theorem lineDegree_neg_cartier_of_sequence
    (hepi : Epi (structureToPushforwardUnit (effectiveCartierInclusion C.toScheme E hE)))
    (hone : Subsingleton (H (C.divisorStructurePushforward E hE) 1)) :
    C.lineDegree (cartierDivisorInvertibleSheaf C.toScheme (-E)) =
      -(effectiveCartierDegree C.toScheme E hE C.toSpec : ℤ) := by
  have hadd := C.eulerCharacteristic_unit_eq_add E hE hepi hone
  have hchi := C.eulerCharacteristic_divisorStructurePushforward E hE hone
  have hL : C.lineDegree (cartierDivisorInvertibleSheaf C.toScheme (-E)) =
      eulerCharacteristic C.toSpec (cartierDivisorModule C.toScheme (-E)) -
        eulerCharacteristic C.toSpec (_root_.SheafOfModules.unit C.toScheme.ringCatSheaf) := rfl
  rw [hL]
  linarith

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

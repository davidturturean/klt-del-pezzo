import KltDP.Geometry.CartierEulerPairing
import KltDP.Geometry.ClosedImmersionPushforwardCohomology
import KltDP.Geometry.CurveEffectiveCartierSequence
import KltDP.Geometry.ClosedImmersionStructureEpi
import KltDP.Geometry.ClosedImmersionKerDegree
import KltDP.Geometry.GluedIdealSheafKernel
import KltDP.Geometry.PrimeCurveIntersectionNumber
import KltDP.Geometry.PrimeCurveIntersectionKernel
import KltDP.Geometry.PrimeCurveCartierVanishingIdeal
import KltDP.Geometry.PicardEulerValue
import KltDP.Geometry.InvertibleCoherentModule
import KltDP.Geometry.SchemeInvertibleSheafPullback
import KltDP.Geometry.FiniteTypeNoetherian

/-!
# The Euler-characteristic pairing against an effective Cartier divisor

`X` a normal projective surface over `k`, `D₂` an effective Cartier divisor with regular equations,
`i : Z → X` any closed immersion with kernel ideal sheaf `I(D₂)` (for instance the zero scheme
`Z(D₂)`, or the reduced curve `C` itself when `D₂ = D_C` is the Cartier divisor of a prime curve on a
regular surface, task 15).

**Proved unconditionally** (`eulerCharacteristic_unit_sub_neg`, `eulerCharacteristic_unit_sub_neg_of_ker`):

    χ_X(O_X) − χ_X(O_X(−D₂)) = χ_Z(O_Z),

from the ideal short exact sequence `0 → O_X(−D₂) → O_X → i_*O_{Z(D₂)} → 0` (tasks 11–12), Euler
additivity on the surface (finiteness of `H^n(X, i_*O_Z)` through the all-degree comparison
`H^n(X, i_*M) ≅ H^n(Z, M)` and 02O6 on `Z`; vanishing above `2`), the comparison
`χ_X(i_*M) = χ_Z(M)`, and the kernel transport `i_*O_Z ≅ i'_*O_{Z'}` for equal kernels (task 15).

**Conditional on the twisted ideal sequence** `TwistedIdealShortExact X D₂ i D₁`
(`0 → O_X(−D₁−D₂) → O_X(−D₁) → i_*(i^*O_X(−D₁)) → 0`, the projection-formula input, stated as an
explicit hypothesis and **not proved** in this tree):

    D₁ · D₂ = χ_Z(O_Z) − χ_Z(i^*O_X(−D₁)) = −deg_Z(i^*O_X(−D₁))       (`cartierEulerPairing_eq_of_twisted`)

with `deg_Z(L) := χ_Z(i^*L) − χ_Z(O_Z)` (`restrictedEulerDegree`; on a prime curve this is literally
the task-14 `intersectionNumber`), hence for a Cartier prime curve `C` on a regular surface
`D · D_C = D_C · D = intersectionNumber C D` (`cartierEulerPairing_primeCurveCartier_of_twisted`, using
`intersectionNumber_neg`) and linearity in the first argument for fixed `D_C`
(`cartierEulerPairing_add_left_of_twisted`, from `intersectionNumber_add`).

Not proved: the twisted sequence itself (projection formula `O_X(−D₁) ⊗ i_*O_Z ≅ i_*(i^*O_X(−D₁))`
and exactness of `− ⊗ O_X(−D₁)`), the conversion `−deg_Z(i^*O(−D₁)) = deg_Z(i^*O(D₁))` for a general
zero scheme `Z(D₂)` (needs Stacks 0AYX on `Z`, i.e. `topologicalKrullDim Z ≤ 1`), and bilinearity in
the second argument for non-effective divisors.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The surface is locally Noetherian (finite type over the field). -/
theorem isLocallyNoetherian_toScheme : IsLocallyNoetherian X.toScheme :=
  isLocallyNoetherian_of_locallyOfFiniteType_toSpec X.structureMorphism

/-- Every closed subscheme of the surface is locally Noetherian. -/
theorem isLocallyNoetherian_of_isClosedImmersion {Z : Scheme.{u}} (i : Z ⟶ X.toScheme)
    [IsClosedImmersion i] : IsLocallyNoetherian Z := by
  haveI : IsProper (i ≫ X.structureMorphism) := inferInstance
  exact isLocallyNoetherian_of_locallyOfFiniteType_toSpec (i ≫ X.structureMorphism)

/-- The structure sheaf of the surface is coherent (trivial invertible sheaf). -/
theorem unit_isCoherentModule' :
    IsCoherentModule (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) := by
  haveI := X.isLocallyNoetherian_toScheme
  exact (InvertibleSheaf.trivial X.toScheme).isCoherent

/-- Every Cartier module on the surface is coherent (it is invertible). -/
theorem cartierDivisorModule_isCoherentModule (E : CartierDivisor X.toScheme) :
    IsCoherentModule (cartierDivisorModule X.toScheme E) := by
  haveI := X.isLocallyNoetherian_toScheme
  exact (cartierDivisorInvertibleSheaf X.toScheme E).isCoherent

section Additivity

variable {Z : Scheme.{u}} (i : Z ⟶ X.toScheme) [IsClosedImmersion i]

/-- Euler additivity on the surface for a short exact sequence whose first two terms are isomorphic
to coherent modules and whose third term is isomorphic to the pushforward of a coherent module on a
closed subscheme: finiteness of the third term through `H^n(X, i_*M) ≅ H^n(Z, M)` and 02O6 on `Z`. -/
theorem eulerCharacteristic_additive_of_isos (S : ShortComplex X.toScheme.Modules)
    (hS : S.ShortExact)
    (M₁ M₂ : X.toScheme.Modules) [IsCoherentModule M₁] [IsCoherentModule M₂]
    (M₃ : Z.Modules) [IsCoherentModule M₃]
    (e₁ : S.X₁ ≅ M₁) (e₂ : S.X₂ ≅ M₂) (e₃ : S.X₃ ≅ (schemeModulePushforward i).obj M₃) :
    eulerCharacteristic X.structureMorphism S.X₂ =
      eulerCharacteristic X.structureMorphism S.X₁ +
        eulerCharacteristic X.structureMorphism S.X₃ :=
  eulerCharacteristic_additive X.structureMorphism S hS 2
    (fun n => by
      haveI := X.coherent_cohomology_finiteDimensional M₁ n
      exact ((baseFunctor X.structureMorphism n).mapIso e₁).toLinearEquiv.symm.finiteDimensional)
    (fun n => by
      haveI := X.coherent_cohomology_finiteDimensional M₂ n
      exact ((baseFunctor X.structureMorphism n).mapIso e₂).toLinearEquiv.symm.finiteDimensional)
    (fun n => by
      haveI := closedImmersionPushforward_baseFunctor_finiteDimensional_of_isProper i
        X.structureMorphism M₃ n
      exact ((baseFunctor X.structureMorphism n).mapIso e₃).toLinearEquiv.symm.finiteDimensional)
    (fun n hn => normalProjectiveSurface_H_subsingleton X S.X₁ n hn)
    (fun n hn => normalProjectiveSurface_H_subsingleton X S.X₂ n hn)
    (fun n hn => normalProjectiveSurface_H_subsingleton X S.X₃ n hn)

end Additivity

section Unit

variable (D₂ : CartierDivisor X.toScheme) (hD₂ : HasRegularCartierEquations X.toScheme D₂)

/-- **`χ(O_X) − χ(O_X(−D₂)) = χ(Z(D₂), O_{Z(D₂)})`**: Euler additivity along the ideal sequence of
`D₂` and the all-degree pushforward comparison. -/
theorem eulerCharacteristic_unit_sub_neg :
    eulerCharacteristic X.structureMorphism (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) -
        eulerCharacteristic X.structureMorphism (cartierDivisorModule X.toScheme (-D₂)) =
      eulerCharacteristic (effectiveCartierToSpec X.toScheme D₂ hD₂ X.structureMorphism)
        (_root_.SheafOfModules.unit (effectiveCartierScheme X.toScheme D₂ hD₂).ringCatSheaf) := by
  haveI := X.unit_isCoherentModule'
  haveI := X.cartierDivisorModule_isCoherentModule (-D₂)
  haveI := X.isLocallyNoetherian_of_isClosedImmersion (effectiveCartierInclusion X.toScheme D₂ hD₂)
  haveI : IsCoherentModule
      (_root_.SheafOfModules.unit (effectiveCartierScheme X.toScheme D₂ hD₂).ringCatSheaf) :=
    (InvertibleSheaf.trivial (effectiveCartierScheme X.toScheme D₂ hD₂)).isCoherent
  have hadd := X.eulerCharacteristic_additive_of_isos (effectiveCartierInclusion X.toScheme D₂ hD₂)
    (effectiveCartierSequence X.toScheme D₂ hD₂)
    (effectiveCartierSequence_shortExact X.toScheme D₂ hD₂
      (effectiveCartier_structureToPushforwardUnit_epi X.toScheme D₂ hD₂))
    (cartierDivisorModule X.toScheme (-D₂)) (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf)
    (_root_.SheafOfModules.unit (effectiveCartierScheme X.toScheme D₂ hD₂).ringCatSheaf)
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  have hpush := eulerCharacteristic_closedImmersionPushforward
    (effectiveCartierInclusion X.toScheme D₂ hD₂) X.structureMorphism
    (_root_.SheafOfModules.unit (effectiveCartierScheme X.toScheme D₂ hD₂).ringCatSheaf)
  change eulerCharacteristic X.structureMorphism
      (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) =
    eulerCharacteristic X.structureMorphism (cartierDivisorModule X.toScheme (-D₂)) +
      eulerCharacteristic X.structureMorphism
        ((schemeModulePushforward (effectiveCartierInclusion X.toScheme D₂ hD₂)).obj
          (_root_.SheafOfModules.unit (effectiveCartierScheme X.toScheme D₂ hD₂).ringCatSheaf))
    at hadd
  change _ = eulerCharacteristic (effectiveCartierInclusion X.toScheme D₂ hD₂ ≫ X.structureMorphism)
    (_root_.SheafOfModules.unit (effectiveCartierScheme X.toScheme D₂ hD₂).ringCatSheaf)
  rw [← hpush]
  omega

/-- The same for any closed immersion `i : Z → X` whose kernel ideal sheaf is `I(D₂)` (kernel
transport of task 15 and the all-degree comparison for both immersions). -/
theorem eulerCharacteristic_unit_sub_neg_of_ker {Z : Scheme.{u}} (i : Z ⟶ X.toScheme)
    [IsClosedImmersion i]
    (hker : i.ker = effectiveCartierIdealDataOfRegularEquations X.toScheme D₂ hD₂) :
    eulerCharacteristic X.structureMorphism (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) -
        eulerCharacteristic X.structureMorphism (cartierDivisorModule X.toScheme (-D₂)) =
      eulerCharacteristic (i ≫ X.structureMorphism) (_root_.SheafOfModules.unit Z.ringCatSheaf) := by
  rw [X.eulerCharacteristic_unit_sub_neg D₂ hD₂]
  have hk : (effectiveCartierInclusion X.toScheme D₂ hD₂).ker = i.ker := by
    rw [hker]
    exact (effectiveCartierIdealDataOfRegularEquations X.toScheme D₂ hD₂).ker_gluedTo
  change eulerCharacteristic (effectiveCartierInclusion X.toScheme D₂ hD₂ ≫ X.structureMorphism)
    (_root_.SheafOfModules.unit (effectiveCartierScheme X.toScheme D₂ hD₂).ringCatSheaf) = _
  rw [← eulerCharacteristic_closedImmersionPushforward (effectiveCartierInclusion X.toScheme D₂ hD₂)
      X.structureMorphism,
    ← eulerCharacteristic_closedImmersionPushforward i X.structureMorphism]
  exact eulerCharacteristic_eq_of_iso X.structureMorphism
    (pushforwardUnitIsoOfKerEq (effectiveCartierInclusion X.toScheme D₂ hD₂) i hk)

end Unit

section Twisted

variable (D₂ : CartierDivisor X.toScheme) {Z : Scheme.{u}} (i : Z ⟶ X.toScheme) [IsClosedImmersion i]

/-- **The twisted ideal sequence** `0 → O_X(−D₁−D₂) → O_X(−D₁) → i_*(i^*O_X(−D₁)) → 0`, as an
explicit hypothesis: a short exact sequence of modules on `X` whose three terms are isomorphic to
these. It is the projection formula `O_X(−D₁) ⊗ i_*O_Z ≅ i_*(i^*O_X(−D₁))` applied to the ideal
sequence of `D₂` tensored with `O_X(−D₁)`; **it is not proved in this tree**. -/
def TwistedIdealShortExact (D₁ : CartierDivisor X.toScheme) : Prop :=
  ∃ S : ShortComplex X.toScheme.Modules, S.ShortExact ∧
    Nonempty (S.X₁ ≅ cartierDivisorModule X.toScheme (-(D₁ + D₂))) ∧
    Nonempty (S.X₂ ≅ cartierDivisorModule X.toScheme (-D₁)) ∧
    Nonempty (S.X₃ ≅ (schemeModulePushforward i).obj
      ((schemeModulePullback i).obj (cartierDivisorModule X.toScheme (-D₁))))

/-- The pulled-back Cartier module is invertible, hence coherent, on `Z`. -/
theorem pullback_cartierDivisorModule_isCoherentModule (E : CartierDivisor X.toScheme) :
    IsCoherentModule ((schemeModulePullback i).obj (cartierDivisorModule X.toScheme E)) := by
  haveI := X.isLocallyNoetherian_of_isClosedImmersion i
  haveI : KltDP.SheafOfModules.IsInvertible (R := Z.ringCatSheaf)
      ((schemeModulePullback i).obj (cartierDivisorModule X.toScheme E)) :=
    schemeModulePullback_isInvertible i _ (cartierDivisorInvertibleSheaf X.toScheme E).property
  exact isCoherentModule_of_isInvertible _

/-- `χ(O_X(−D₁)) − χ(O_X(−D₁−D₂)) = χ(Z, i^*O_X(−D₁))` under the twisted ideal sequence. -/
theorem eulerCharacteristic_neg_sub_of_twisted (D₁ : CartierDivisor X.toScheme)
    (h : X.TwistedIdealShortExact D₂ i D₁) :
    eulerCharacteristic X.structureMorphism (cartierDivisorModule X.toScheme (-D₁)) -
        eulerCharacteristic X.structureMorphism (cartierDivisorModule X.toScheme (-(D₁ + D₂))) =
      eulerCharacteristic (i ≫ X.structureMorphism)
        ((schemeModulePullback i).obj (cartierDivisorModule X.toScheme (-D₁))) := by
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := h
  haveI := X.cartierDivisorModule_isCoherentModule (-(D₁ + D₂))
  haveI := X.cartierDivisorModule_isCoherentModule (-D₁)
  haveI := X.pullback_cartierDivisorModule_isCoherentModule i (-D₁)
  have hadd := X.eulerCharacteristic_additive_of_isos i S hS _ _ _ e₁ e₂ e₃
  rw [eulerCharacteristic_eq_of_iso X.structureMorphism e₁,
    eulerCharacteristic_eq_of_iso X.structureMorphism e₂,
    eulerCharacteristic_eq_of_iso X.structureMorphism e₃,
    eulerCharacteristic_closedImmersionPushforward i X.structureMorphism] at hadd
  omega

/-- The Euler degree on the closed subscheme `Z` of the pullback of a module `L` on `X`:
`deg_Z(i^*L) := χ_Z(i^*L) − χ_Z(O_Z)`. On a prime curve this is the task-14 `intersectionNumber`
(`restrictedEulerDegree_inclusion`). -/
def restrictedEulerDegree (L : X.toScheme.Modules) : ℤ :=
  eulerCharacteristic (i ≫ X.structureMorphism) ((schemeModulePullback i).obj L) -
    eulerCharacteristic (i ≫ X.structureMorphism) (_root_.SheafOfModules.unit Z.ringCatSheaf)

/-- **`D₁ · D₂ = χ_Z(O_Z) − χ_Z(i^*O_X(−D₁))`** for a closed immersion `i` with kernel `I(D₂)`,
under the twisted ideal sequence. -/
theorem cartierEulerPairing_eq_of_twisted (hD₂ : HasRegularCartierEquations X.toScheme D₂)
    (hker : i.ker = effectiveCartierIdealDataOfRegularEquations X.toScheme D₂ hD₂)
    (D₁ : CartierDivisor X.toScheme) (h : X.TwistedIdealShortExact D₂ i D₁) :
    X.cartierEulerPairing D₁ D₂ =
      eulerCharacteristic (i ≫ X.structureMorphism) (_root_.SheafOfModules.unit Z.ringCatSheaf) -
        eulerCharacteristic (i ≫ X.structureMorphism)
          ((schemeModulePullback i).obj (cartierDivisorModule X.toScheme (-D₁))) := by
  unfold cartierEulerPairing
  have hA := X.eulerCharacteristic_unit_sub_neg_of_ker D₂ hD₂ i hker
  have hB := X.eulerCharacteristic_neg_sub_of_twisted D₂ i D₁ h
  omega

/-- **`D₁ · D₂ = −deg_Z(i^*O_X(−D₁))`** under the twisted ideal sequence. -/
theorem cartierEulerPairing_eq_neg_restrictedEulerDegree
    (hD₂ : HasRegularCartierEquations X.toScheme D₂)
    (hker : i.ker = effectiveCartierIdealDataOfRegularEquations X.toScheme D₂ hD₂)
    (D₁ : CartierDivisor X.toScheme) (h : X.TwistedIdealShortExact D₂ i D₁) :
    X.cartierEulerPairing D₁ D₂ =
      -X.restrictedEulerDegree i (cartierDivisorModule X.toScheme (-D₁)) := by
  rw [X.cartierEulerPairing_eq_of_twisted D₂ i hD₂ hker D₁ h]
  unfold restrictedEulerDegree
  omega

end Twisted

section PrimeCurve

/-- On a prime curve the Euler degree of `i^*O_X(E)` is the task-14 intersection number. -/
theorem restrictedEulerDegree_inclusion (C : X.PrimeCurve) (E : CartierDivisor X.toScheme) :
    X.restrictedEulerDegree C.inclusion (cartierDivisorModule X.toScheme E) =
      C.intersectionNumber E := rfl

variable [IsAlgClosed k] (hregular : ∀ x : X.Point, RegularPoint X.toScheme x) (C : X.PrimeCurve)

/-- The kernel of `C → X` is the ideal sheaf of the Cartier divisor `D_C` (tasks 15–16). -/
theorem inclusion_ker_primeCurveCartier :
    C.inclusion.ker = effectiveCartierIdealDataOfRegularEquations X.toScheme
      (X.primeCurveCartier hregular C) (X.primeCurveCartier_hasRegularEquations hregular C) := by
  rw [C.inclusion_ker, X.primeCurveCartier_idealData_eq_vanishingIdeal hregular C]

/-- **`χ(O_X) − χ(O_X(−D_C)) = χ(C, O_C)`** for a Cartier prime curve `C` on a regular surface
(unconditional). -/
theorem eulerCharacteristic_unit_sub_neg_primeCurveCartier :
    eulerCharacteristic X.structureMorphism (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) -
        eulerCharacteristic X.structureMorphism
          (cartierDivisorModule X.toScheme (-(X.primeCurveCartier hregular C))) =
      eulerCharacteristic C.toSpec (_root_.SheafOfModules.unit C.toScheme.ringCatSheaf) :=
  X.eulerCharacteristic_unit_sub_neg_of_ker (X.primeCurveCartier hregular C)
    (X.primeCurveCartier_hasRegularEquations hregular C) C.inclusion
    (X.inclusion_ker_primeCurveCartier hregular C)

/-- **`D · D_C = intersectionNumber C D`** for a Cartier prime curve `C` on a regular surface, under
the twisted ideal sequence for `(D, D_C)` along `C → X`. -/
theorem cartierEulerPairing_primeCurveCartier_of_twisted (D : CartierDivisor X.toScheme)
    (h : X.TwistedIdealShortExact (X.primeCurveCartier hregular C) C.inclusion D) :
    X.cartierEulerPairing D (X.primeCurveCartier hregular C) = C.intersectionNumber D := by
  rw [X.cartierEulerPairing_eq_neg_restrictedEulerDegree (X.primeCurveCartier hregular C) C.inclusion
      (X.primeCurveCartier_hasRegularEquations hregular C)
      (X.inclusion_ker_primeCurveCartier hregular C) D h,
    X.restrictedEulerDegree_inclusion C (-D), C.intersectionNumber_neg, neg_neg]

/-- **`D_C · D = intersectionNumber C D`** (by symmetry of the pairing). -/
theorem cartierEulerPairing_primeCurveCartier_of_twisted' (D : CartierDivisor X.toScheme)
    (h : X.TwistedIdealShortExact (X.primeCurveCartier hregular C) C.inclusion D) :
    X.cartierEulerPairing (X.primeCurveCartier hregular C) D = C.intersectionNumber D := by
  rw [X.cartierEulerPairing_comm]
  exact X.cartierEulerPairing_primeCurveCartier_of_twisted hregular C D h

/-- **Linearity in the first argument** for a fixed Cartier prime curve, under the twisted ideal
sequences for `D`, `D'` and `D + D'` (from `intersectionNumber_add`). -/
theorem cartierEulerPairing_add_left_of_twisted (D D' : CartierDivisor X.toScheme)
    (h : X.TwistedIdealShortExact (X.primeCurveCartier hregular C) C.inclusion D)
    (h' : X.TwistedIdealShortExact (X.primeCurveCartier hregular C) C.inclusion D')
    (h'' : X.TwistedIdealShortExact (X.primeCurveCartier hregular C) C.inclusion (D + D')) :
    X.cartierEulerPairing (D + D') (X.primeCurveCartier hregular C) =
      X.cartierEulerPairing D (X.primeCurveCartier hregular C) +
        X.cartierEulerPairing D' (X.primeCurveCartier hregular C) := by
  rw [X.cartierEulerPairing_primeCurveCartier_of_twisted hregular C _ h'',
    X.cartierEulerPairing_primeCurveCartier_of_twisted hregular C _ h,
    X.cartierEulerPairing_primeCurveCartier_of_twisted hregular C _ h', C.intersectionNumber_add]

end PrimeCurve

end KltDP.Geometry.NormalProjectiveSurface

namespace KltDP.Geometry

open KltDP.Geometry.ModuleCohomology NormalProjectiveSurface

/-- **F03 export (Task 17): the Euler pairing against an effective divisor.** For an effective Cartier
divisor `D₂` with regular equations and a closed immersion `i : Z → X` with kernel `I(D₂)`:
(1) unconditionally `χ(O_X) − χ(O_X(−D₂)) = χ_Z(O_Z)`; (2) under the twisted ideal sequence for
`D₁`, `D₁ · D₂ = −deg_Z(i^*O_X(−D₁))` with `deg_Z(i^*L) = χ_Z(i^*L) − χ_Z(O_Z)`. -/
theorem f03_euler_pairing_effective {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (D₂ : CartierDivisor X.toScheme) (hD₂ : HasRegularCartierEquations X.toScheme D₂)
    {Z : Scheme.{u}} (i : Z ⟶ X.toScheme) [IsClosedImmersion i]
    (hker : i.ker = effectiveCartierIdealDataOfRegularEquations X.toScheme D₂ hD₂) :
    (eulerCharacteristic X.structureMorphism (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) -
        eulerCharacteristic X.structureMorphism (cartierDivisorModule X.toScheme (-D₂)) =
      eulerCharacteristic (i ≫ X.structureMorphism)
        (_root_.SheafOfModules.unit Z.ringCatSheaf)) ∧
    (∀ D₁ : CartierDivisor X.toScheme, X.TwistedIdealShortExact D₂ i D₁ →
      X.cartierEulerPairing D₁ D₂ =
        -X.restrictedEulerDegree i (cartierDivisorModule X.toScheme (-D₁))) :=
  ⟨X.eulerCharacteristic_unit_sub_neg_of_ker D₂ hD₂ i hker,
    fun D₁ h => X.cartierEulerPairing_eq_neg_restrictedEulerDegree D₂ i hD₂ hker D₁ h⟩

/-- Universe check: a single universe `u`. -/
example {k : Type u} [Field k] (X : NormalProjectiveSurface k) [IsAlgClosed k]
    (hregular : ∀ x : X.Point, RegularPoint X.toScheme x) (C : X.PrimeCurve)
    (D : CartierDivisor X.toScheme)
    (h : X.TwistedIdealShortExact (X.primeCurveCartier hregular C) C.inclusion D) :
    X.cartierEulerPairing (X.primeCurveCartier hregular C) D = C.intersectionNumber D :=
  X.cartierEulerPairing_primeCurveCartier_of_twisted' hregular C D h

end KltDP.Geometry

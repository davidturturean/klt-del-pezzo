import KltDP.Geometry.CartierEulerPairingEffective
import KltDP.Geometry.ClosedImmersionProjectionFormula

/-!
# The twisted ideal sequence; the unconditional Euler pairing against effective divisors

The Task-17 hypothesis `TwistedIdealShortExact X D₂ i D₁` (a short exact sequence with terms
isomorphic to `O_X(−D₁−D₂)`, `O_X(−D₁)`, `i_*(i^*O_X(−D₁))`) is discharged here for every effective
`D₂` with regular equations, every closed immersion `i : Z → X` with kernel `I(D₂)` and every `D₁`:
the ideal sequence `0 → O_X(−D₂) → O_X → i_*O_Z → 0` (Tasks 11–12, 15) tensored with the invertible
sheaf `O_X(−D₁)` stays short exact (`InvertibleTensorExact`), its first term is `O_X(−D₂) ⊗ O_X(−D₁)
≅ O_X(−D₁−D₂)` (accepted `cartierTensorIso`), its middle term is `O_X ⊗ O_X(−D₁) ≅ O_X(−D₁)`, and its
last term is `i_*O_Z ⊗ O_X(−D₁) ≅ i_*(i^*O_X(−D₁))` (the projection formula
`ClosedImmersionProjectionFormula`).

Consequently the Task-17 pairing identities hold unconditionally:
`D₁ · D₂ = χ_Z(O_Z) − χ_Z(i^*O_X(−D₁)) = −deg_Z(i^*O_X(−D₁))` for effective `D₂`;
**`D · D_C = D_C · D = intersectionNumber C D`** for a Cartier prime curve `C` on a regular surface
over an algebraically closed field; **linearity in the first argument** against `D_C`.
Export `f03_euler_pairing_bilinear_effective`.

**Not proved here** (done in `KltDP.Geometry.CartierEulerPairingDegree`): `topologicalKrullDim
Z(D₂) ≤ 1` for a general effective `D₂`, hence the conversion `−deg_Z(i^*O(−D₁)) = deg_Z(i^*O(D₁))`
and linearity in `D₁` for a zero scheme that is not a prime curve (Stacks 0AYX on `Z(D₂)`).
**Not proved in this tree:** linearity in a non-effective `D₂`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance twistedPairingMonoidal (Z : Scheme.{u}) : MonoidalCategory Z.Modules :=
  Scheme.Modules.monoidalCategory Z

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

section Twisted

variable (D₂ : CartierDivisor X.toScheme) (hD₂ : HasRegularCartierEquations X.toScheme D₂)
  {Z : Scheme.{u}} (i : Z ⟶ X.toScheme) [IsClosedImmersion i]
  (hker : i.ker = effectiveCartierIdealDataOfRegularEquations X.toScheme D₂ hD₂)

include hD₂ hker in
/-- **The twisted ideal sequence exists**: the ideal sequence of `D₂` tensored with `O_X(−D₁)`,
with its three terms identified by the Cartier tensor isomorphism, the unit isomorphism and the
projection formula. -/
theorem twistedIdealShortExact (D₁ : CartierDivisor X.toScheme) :
    X.TwistedIdealShortExact D₂ i D₁ := by
  letI : (tensorRight (cartierDivisorModule X.toScheme (-D₁))).PreservesZeroMorphisms :=
    (cartierDivisorInvertibleSheaf X.toScheme (-D₁)).tensorRight_preservesZeroMorphisms
  obtain ⟨L', ⟨e⟩, ⟨e'⟩⟩ :=
    cartierDivisorModule_exists_tensorInverse (X := X.toScheme) (-D₁)
  refine ⟨(effectiveCartierSequence X.toScheme D₂ hD₂).map
      (tensorRight (cartierDivisorModule X.toScheme (-D₁))),
    KltDP.Monoidal.shortExact_map_tensorRight _ L' e e' _
      (effectiveCartierSequence_shortExact X.toScheme D₂ hD₂
        (effectiveCartier_structureToPushforwardUnit_epi X.toScheme D₂ hD₂)),
    ⟨?_⟩, ⟨?_⟩, ⟨?_⟩⟩
  · exact cartierTensorIso X.toScheme (-D₂) (-D₁) ≪≫
      eqToIso (congrArg (cartierDivisorModule X.toScheme) (by abel))
  · exact schemeUnitTensorLeftIso X.toScheme (cartierDivisorModule X.toScheme (-D₁))
  · have hk : (effectiveCartierInclusion X.toScheme D₂ hD₂).ker = i.ker := by
      rw [hker]
      exact (effectiveCartierIdealDataOfRegularEquations X.toScheme D₂ hD₂).ker_gluedTo
    exact (tensorRight (cartierDivisorModule X.toScheme (-D₁))).mapIso
        (pushforwardUnitIsoOfKerEq (effectiveCartierInclusion X.toScheme D₂ hD₂) i hk) ≪≫
      pushforwardUnitTensorIso i (cartierDivisorModule X.toScheme (-D₁)) L' e e'

include hD₂ hker in
/-- **`D₁ · D₂ = χ_Z(O_Z) − χ_Z(i^*O_X(−D₁))`** for every effective `D₂` with regular equations and
every closed immersion `i : Z → X` with kernel `I(D₂)` (unconditional). -/
theorem cartierEulerPairing_eq_sub_of_ker (D₁ : CartierDivisor X.toScheme) :
    X.cartierEulerPairing D₁ D₂ =
      eulerCharacteristic (i ≫ X.structureMorphism) (_root_.SheafOfModules.unit Z.ringCatSheaf) -
        eulerCharacteristic (i ≫ X.structureMorphism)
          ((schemeModulePullback i).obj (cartierDivisorModule X.toScheme (-D₁))) :=
  X.cartierEulerPairing_eq_of_twisted D₂ i hD₂ hker D₁ (X.twistedIdealShortExact D₂ hD₂ i hker D₁)

include hD₂ hker in
/-- **`D₁ · D₂ = −deg_Z(i^*O_X(−D₁))`** (unconditional). -/
theorem cartierEulerPairing_eq_neg_restrictedEulerDegree_of_ker (D₁ : CartierDivisor X.toScheme) :
    X.cartierEulerPairing D₁ D₂ =
      -X.restrictedEulerDegree i (cartierDivisorModule X.toScheme (-D₁)) :=
  X.cartierEulerPairing_eq_neg_restrictedEulerDegree D₂ i hD₂ hker D₁
    (X.twistedIdealShortExact D₂ hD₂ i hker D₁)

end Twisted

section PrimeCurve

variable [IsAlgClosed k] (hregular : ∀ x : X.Point, RegularPoint X.toScheme x) (C : X.PrimeCurve)

/-- The twisted ideal sequence along a Cartier prime curve, for every `D`. -/
theorem twistedIdealShortExact_primeCurveCartier (D : CartierDivisor X.toScheme) :
    X.TwistedIdealShortExact (X.primeCurveCartier hregular C) C.inclusion D :=
  X.twistedIdealShortExact (X.primeCurveCartier hregular C)
    (X.primeCurveCartier_hasRegularEquations hregular C) C.inclusion
    (X.inclusion_ker_primeCurveCartier hregular C) D

/-- **`D · D_C = intersectionNumber C D`** for a Cartier prime curve `C` on a regular surface over an
algebraically closed field (unconditional). -/
theorem cartierEulerPairing_primeCurveCartier (D : CartierDivisor X.toScheme) :
    X.cartierEulerPairing D (X.primeCurveCartier hregular C) = C.intersectionNumber D :=
  X.cartierEulerPairing_primeCurveCartier_of_twisted hregular C D
    (X.twistedIdealShortExact_primeCurveCartier hregular C D)

/-- **`D_C · D = intersectionNumber C D`** (unconditional). -/
theorem cartierEulerPairing_primeCurveCartier' (D : CartierDivisor X.toScheme) :
    X.cartierEulerPairing (X.primeCurveCartier hregular C) D = C.intersectionNumber D :=
  X.cartierEulerPairing_primeCurveCartier_of_twisted' hregular C D
    (X.twistedIdealShortExact_primeCurveCartier hregular C D)

/-- **Linearity in the first argument** against a Cartier prime curve (unconditional). -/
theorem cartierEulerPairing_add_left (D D' : CartierDivisor X.toScheme) :
    X.cartierEulerPairing (D + D') (X.primeCurveCartier hregular C) =
      X.cartierEulerPairing D (X.primeCurveCartier hregular C) +
        X.cartierEulerPairing D' (X.primeCurveCartier hregular C) :=
  X.cartierEulerPairing_add_left_of_twisted hregular C D D'
    (X.twistedIdealShortExact_primeCurveCartier hregular C D)
    (X.twistedIdealShortExact_primeCurveCartier hregular C D')
    (X.twistedIdealShortExact_primeCurveCartier hregular C (D + D'))

/-- **Linearity in the second argument** against a Cartier prime curve, by symmetry. -/
theorem cartierEulerPairing_add_right (D D' : CartierDivisor X.toScheme) :
    X.cartierEulerPairing (X.primeCurveCartier hregular C) (D + D') =
      X.cartierEulerPairing (X.primeCurveCartier hregular C) D +
        X.cartierEulerPairing (X.primeCurveCartier hregular C) D' := by
  rw [X.cartierEulerPairing_comm, X.cartierEulerPairing_add_left hregular C D D',
    X.cartierEulerPairing_comm _ D, X.cartierEulerPairing_comm _ D']

end PrimeCurve

end KltDP.Geometry.NormalProjectiveSurface

namespace KltDP.Geometry

open KltDP.Geometry.ModuleCohomology NormalProjectiveSurface

/-- **F03 export (Task 18): the Euler pairing against effective divisors, unconditionally.**
(1) For every effective `D₂` with regular equations, every closed immersion `i : Z → X` with kernel
`I(D₂)` and every `D₁`: `D₁ · D₂ = −deg_Z(i^*O_X(−D₁))` with `deg_Z(i^*L) = χ_Z(i^*L) − χ_Z(O_Z)`.
(2) For a Cartier prime curve `C` on a regular surface over an algebraically closed field:
`D · D_C = D_C · D = intersectionNumber C D` for every `D`, and the pairing against `D_C` is additive
in the other argument. -/
theorem f03_euler_pairing_bilinear_effective {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    [IsAlgClosed k] (hregular : ∀ x : X.Point, RegularPoint X.toScheme x) (C : X.PrimeCurve) :
    (∀ (D₂ : CartierDivisor X.toScheme) (hD₂ : HasRegularCartierEquations X.toScheme D₂)
      {Z : Scheme.{u}} (i : Z ⟶ X.toScheme) [IsClosedImmersion i]
      (_ : i.ker = effectiveCartierIdealDataOfRegularEquations X.toScheme D₂ hD₂)
      (D₁ : CartierDivisor X.toScheme),
      X.cartierEulerPairing D₁ D₂ =
        -X.restrictedEulerDegree i (cartierDivisorModule X.toScheme (-D₁))) ∧
    (∀ D : CartierDivisor X.toScheme,
      X.cartierEulerPairing D (X.primeCurveCartier hregular C) = C.intersectionNumber D) ∧
    (∀ D : CartierDivisor X.toScheme,
      X.cartierEulerPairing (X.primeCurveCartier hregular C) D = C.intersectionNumber D) ∧
    (∀ D D' : CartierDivisor X.toScheme,
      X.cartierEulerPairing (D + D') (X.primeCurveCartier hregular C) =
        X.cartierEulerPairing D (X.primeCurveCartier hregular C) +
          X.cartierEulerPairing D' (X.primeCurveCartier hregular C)) :=
  ⟨fun D₂ hD₂ _ i _ hker D₁ =>
      X.cartierEulerPairing_eq_neg_restrictedEulerDegree_of_ker D₂ hD₂ i hker D₁,
    fun D => X.cartierEulerPairing_primeCurveCartier hregular C D,
    fun D => X.cartierEulerPairing_primeCurveCartier' hregular C D,
    fun D D' => X.cartierEulerPairing_add_left hregular C D D'⟩

/-- Universe check: a single universe `u`. -/
example {k : Type u} [Field k] (X : NormalProjectiveSurface k) [IsAlgClosed k]
    (hregular : ∀ x : X.Point, RegularPoint X.toScheme x) (C : X.PrimeCurve)
    (D : CartierDivisor X.toScheme) :
    X.cartierEulerPairing (X.primeCurveCartier hregular C) D = C.intersectionNumber D :=
  X.cartierEulerPairing_primeCurveCartier' hregular C D

end KltDP.Geometry

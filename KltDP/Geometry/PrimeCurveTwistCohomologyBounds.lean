import KltDP.Geometry.ModuleCohomologyDimensionBounds
import KltDP.Geometry.CartierEulerPairingTwisted
import KltDP.Geometry.ProperCurveEuler

/-!
# Actual cohomology bounds for adding a prime Cartier curve

The original prime may be singular. Its dimension-one vanishing and the
proved twisted ideal sequence give H0 monotonicity and H2 antitonicity.
No duality, adjunction, or ampleness hypothesis is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology

universe u

set_option autoImplicit false

namespace KltDP.Geometry.NormalProjectiveSurface

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x) (C : X.PrimeCurve)

/-- The existing twisted sequence, with its terms written as O(D),
O(D+C), and the original pushforward from C. -/
theorem exists_prime_add_shortExact (D : CartierDivisor X.toScheme) :
    ∃ S : ShortComplex X.toScheme.Modules, S.ShortExact ∧
      Nonempty (S.X₁ ≅ cartierDivisorModule X.toScheme D) ∧
      Nonempty (S.X₂ ≅ cartierDivisorModule X.toScheme
        (D + X.primeCurveCartier hregular C)) ∧
      Nonempty (S.X₃ ≅ (schemeModulePushforward C.inclusion).obj
        ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme
          (D + X.primeCurveCartier hregular C)))) := by
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    X.twistedIdealShortExact_primeCurveCartier hregular C
      (-(D + X.primeCurveCartier hregular C))
  refine ⟨S, hS, ⟨?_⟩, ⟨?_⟩, ⟨?_⟩⟩
  · exact e₁ ≪≫ eqToIso (congrArg (cartierDivisorModule X.toScheme) (by abel))
  · simpa only [neg_neg] using e₂
  · simpa only [neg_neg] using e₃

/-- Adding the actual prime curve increases H0 and decreases H2. -/
theorem cohomologyDimension_prime_add_bounds (D : CartierDivisor X.toScheme) :
    cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme D) 0 ≤
        cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme
          (D + X.primeCurveCartier hregular C)) 0 ∧
      cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme
        (D + X.primeCurveCartier hregular C)) 2 ≤
        cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme D) 2 := by
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := X.exists_prime_add_shortExact hregular C D
  letI := X.cartierDivisorModule_isCoherentModule D
  letI := X.cartierDivisorModule_isCoherentModule (D + X.primeCurveCartier hregular C)
  haveI := X.coherent_cohomology_finiteDimensional
    (cartierDivisorModule X.toScheme D) 2
  haveI := X.coherent_cohomology_finiteDimensional
    (cartierDivisorModule X.toScheme (D + X.primeCurveCartier hregular C)) 0
  letI : FiniteDimensional k ((baseFunctor X.structureMorphism 2).obj S.X₁) :=
    ((baseFunctor X.structureMorphism 2).mapIso e₁).toLinearEquiv.symm.finiteDimensional
  letI : FiniteDimensional k ((baseFunctor X.structureMorphism 0).obj S.X₂) :=
    ((baseFunctor X.structureMorphism 0).mapIso e₂).toLinearEquiv.symm.finiteDimensional
  letI := C.toSpec_isProper
  let T := (schemeModulePullback C.inclusion).obj
    (cartierDivisorModule X.toScheme (D + X.primeCurveCartier hregular C))
  letI : Subsingleton (H T 2) :=
    proper_H_subsingleton_of_dimension_le_one C.toSpec C.dimension_one_toScheme.le T 2
      (by decide)
  letI : Subsingleton (H ((schemeModulePushforward C.inclusion).obj T) 2) :=
    closedImmersionPushforward_H_subsingleton C.inclusion T 2
  letI : Subsingleton (H S.X₃ 2) :=
    ((zariskiFunctor X.toScheme 2).mapIso e₃).addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mpr
      inferInstance
  have h₀ := cohomologyDimension_zero_le_of_shortExact X.structureMorphism S hS
  have h₂ := cohomologyDimension_middle_le_of_subsingleton_right
    X.structureMorphism S hS 2
  rw [cohomologyDimension_eq_of_iso X.structureMorphism e₁,
    cohomologyDimension_eq_of_iso X.structureMorphism e₂] at h₀ h₂
  exact ⟨h₀, h₂⟩

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.exists_prime_add_shortExact
#print axioms KltDP.Geometry.NormalProjectiveSurface.exists_prime_add_shortExact
#check @KltDP.Geometry.NormalProjectiveSurface.cohomologyDimension_prime_add_bounds
#print axioms KltDP.Geometry.NormalProjectiveSurface.cohomologyDimension_prime_add_bounds

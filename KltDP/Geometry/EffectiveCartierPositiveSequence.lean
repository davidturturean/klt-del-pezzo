import KltDP.Geometry.CurveEffectiveCartierSequence
import KltDP.Geometry.ClosedImmersionStructureEpi
import KltDP.Geometry.ClosedImmersionProjectionFormula
import KltDP.Geometry.CartierEulerPairingDegree

/-! The actual positive Cartier sequence on the original integral scheme.
The maps are obtained by tensoring its original ideal sequence with O(E).
No cohomology, generation, dimension, or curve rationality is assumed. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace KltDP.Geometry.EffectiveCartierPositive

local instance positiveMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable (X : Scheme.{u}) [IsIntegral X]
  (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)

/-- The original ideal sequence tensored with the original O(E). -/
def sequence : ShortComplex X.Modules :=
  letI : (tensorRight (cartierDivisorModule X E)).PreservesZeroMorphisms :=
    (cartierDivisorInvertibleSheaf X E).tensorRight_preservesZeroMorphisms
  (effectiveCartierSequence X E hE).map (tensorRight (cartierDivisorModule X E))

/-- Its exactness follows from the actual closed immersion and invertible tensor functor. -/
theorem shortExact : (sequence X E hE).ShortExact :=
  (cartierDivisorInvertibleSheaf X E).shortExact_map_tensorRight
    (effectiveCartierSequence X E hE)
    (effectiveCartierSequence_shortExact X E hE
      (effectiveCartier_structureToPushforwardUnit_epi X E hE))

/-- The first term is the original structure module, by (-E)+E=0. -/
def firstIsoUnit :
    (sequence X E hE).X₁ ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
  cartierTensorIso X (-E) E ≪≫
    eqToIso (congrArg (cartierDivisorModule X) (neg_add_cancel E)) ≪≫
      cartierDivisorModuleZeroIsoUnit X

/-- The middle term is the original positive Cartier module. -/
def middleIso : (sequence X E hE).X₂ ≅ cartierDivisorModule X E :=
  schemeUnitTensorLeftIso X (cartierDivisorModule X E)

/-- The quotient is the actual restriction to the original Cartier zero scheme. -/
def quotientIso :
    (sequence X E hE).X₃ ≅
      (schemeModulePushforward (effectiveCartierInclusion X E hE)).obj
        ((schemeModulePullback (effectiveCartierInclusion X E hE)).obj
          (cartierDivisorModule X E)) :=
  Classical.choice (InvertibleSheaf.exists_pushforwardUnitTensorIso
    (effectiveCartierInclusion X E hE) (cartierDivisorInvertibleSheaf X E))

#print axioms shortExact
#print axioms firstIsoUnit
#print axioms middleIso
#print axioms quotientIso

end KltDP.Geometry.EffectiveCartierPositive

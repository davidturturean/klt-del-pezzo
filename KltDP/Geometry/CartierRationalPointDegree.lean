import KltDP.Geometry.CartierRationalPointRestriction
import KltDP.Geometry.CurveDegreeZeroNotBig

/-! The original rational Cartier point has degree one. The degree comparison
uses the original closed-immersion kernels and original base scalar actions.
Its Cartier line therefore has Euler degree one on the original proper curve,
without a genus-zero or smoothness hypothesis. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CartierRationalPoint

open ModuleCohomology

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
  (i : Spec (CommRingCat.of k) ⟶ X) [hiClosed : IsClosedImmersion i]
  (hker : i.ker = effectiveCartierIdealDataOfRegularEquations X E hE)

include hiClosed hker in
/-- The actual effective divisor has one-dimensional global functions
under the scalar action of the original structure morphism. -/
theorem effectiveCartierDegree_eq_one
    (f : X ⟶ Spec (CommRingCat.of k)) (hi : i ≫ f = 𝟙 _) :
    effectiveCartierDegree X E hE f = 1 := by
  let j := effectiveCartierInclusion X E hE
  have hk : j.ker = i.ker := by
    change (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo.ker = i.ker
    rw [Scheme.IdealSheafData.ker_gluedTo, hker]
  let e := pushforwardUnitIsoOfKerEq j i hk
  letI := baseRingModule f ((schemeModulePushforward j).obj
    (_root_.SheafOfModules.unit (effectiveCartierScheme X E hE).ringCatSheaf)) 0
  letI := baseRingModule (j ≫ f)
    (_root_.SheafOfModules.unit (effectiveCartierScheme X E hE).ringCatSheaf) 0
  have hp : cohomologyDimension f ((schemeModulePushforward j).obj
      (_root_.SheafOfModules.unit (effectiveCartierScheme X E hE).ringCatSheaf)) 0 =
      effectiveCartierDegree X E hE f :=
    (pushforwardHZeroBaseRingLinearEquiv j f
      (_root_.SheafOfModules.unit (effectiveCartierScheme X E hE).ringCatSheaf)).finrank_eq
  rw [← hp, cohomologyDimension_eq_of_iso f e 0]
  exact RationalPointPushforward.cohomologyDimension_zero i f hi

include hiClosed hker in
/-- The original O(E) has degree one on the original proper integral curve.
This is the actual Euler degree, not the degree of a chosen zero-cycle. -/
theorem eulerDegree_eq_one
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (hi : i ≫ f = 𝟙 _) :
    eulerCharacteristic f (cartierDivisorModule X E) -
      eulerCharacteristic f (_root_.SheafOfModules.unit X.ringCatSheaf) = 1 := by
  rw [CurveDegreeZeroNotBig.eulerDifference_cartier_eq_effectiveDegree f hdim E hE,
    effectiveCartierDegree_eq_one E hE i hker f hi, Nat.cast_one]

#print axioms effectiveCartierDegree_eq_one
#print axioms eulerDegree_eq_one

end KltDP.Geometry.CartierRationalPoint

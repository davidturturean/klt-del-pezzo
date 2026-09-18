import KltDP.Geometry.CartierExceptionalKernelTensor
import KltDP.Geometry.KernelLinePullbackOffRange
import KltDP.Geometry.SchemeModulePullbackTensor

/-!
# The original Cartier line pulls back trivially off its branch divisor

The actual kernel becomes the structure module by disjointness of the
original ranges. Pulling back actual Cartier multiplication then cancels
that kernel and gives a trivialization of the positive Cartier line.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.UnbranchedCartierPullback

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- The divisor, its actual zero scheme and the original pullback are retained. -/
def unitIso {X C : Scheme.{u}} [IsIntegral X]
    (E : CartierDivisor X) (hE : HasRegularCartierEquations X E) (f : C ⟶ X)
    (hdisj : Disjoint (Set.range f.base)
      (Set.range (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo.base)) :
    (schemeModulePullback f).obj (cartierDivisorModule X E) ≅
      _root_.SheafOfModules.unit C.ringCatSheaf := by
  let i := (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo
  let N := (schemeModulePullback f).obj (cartierDivisorModule X E)
  let eK : (schemeModulePullback f).obj (schemeKernelIdeal i) ≅ 𝟙_ C.Modules :=
    KernelLinePullbackOffRange.kernelLine_pullback_unitIso i f hdisj ≪≫
      SchemeModuleStructureUnit.iso C
  let eEK := CartierExceptionalKernelTensor.positiveKernelTensorIso E hE i
    (effectiveCartierIdealDataOfRegularEquations_ker X E hE).symm
  exact (ρ_ N).symm ≪≫ tensorIso (Iso.refl N) eK.symm ≪≫
    (schemeModulePullbackTensorIso f (cartierDivisorModule X E)
      (schemeKernelIdeal i)).symm ≪≫ (schemeModulePullback f).mapIso eEK ≪≫
    schemeModulePullbackTensorUnitIso f ≪≫ (SchemeModuleStructureUnit.iso C).symm

end KltDP.Geometry.UnbranchedCartierPullback

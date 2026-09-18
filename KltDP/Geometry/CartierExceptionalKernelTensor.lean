import KltDP.Geometry.EffectiveCartierIdeal
import KltDP.Geometry.ClosedImmersionKerDegree
import KltDP.Geometry.CartierTensorProduct
import KltDP.Geometry.SchemeModuleStructureUnit

/-!
# The actual Cartier module inverse of an exceptional kernel

Identify O(-E) with the kernel of the original closed immersion by its
proved ideal-sheaf equality, retaining the original inclusion. Actual
Cartier multiplication then identifies O(E) tensor that kernel with the
structure module. No choice of a Picard-class representative is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.CartierExceptionalKernelTensor

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- The negative Cartier module is the actual original closed-immersion kernel. -/
def negativeKernelIso {X Z : Scheme.{u}} [IsIntegral X]
    (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hI : effectiveCartierIdealDataOfRegularEquations X E hE = i.ker) :
    cartierDivisorModule X (-E) ≅ schemeKernelIdeal i :=
  effectiveCartierKernelIso X E hE ≪≫
    kernelIsoOfKerEq _ i
      ((effectiveCartierIdealDataOfRegularEquations_ker X E hE).trans hI)

/-- The comparison retains the original normalized negative-Cartier inclusion. -/
theorem negativeKernelIso_hom_inclusion {X Z : Scheme.{u}} [IsIntegral X]
    (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hI : effectiveCartierIdealDataOfRegularEquations X E hE = i.ker) :
    (negativeKernelIso E hE i hI).hom ≫ schemeKernelIdealι i =
      effectiveCartierNegativeInclusion X E hE := by
  have hk : (kernelIsoOfKerEq _ i
      ((effectiveCartierIdealDataOfRegularEquations_ker X E hE).trans hI)).hom ≫
        schemeKernelIdealι i =
      schemeKernelIdealι (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo :=
    kernelIsoOfKerEq_hom_ι _ i
      ((effectiveCartierIdealDataOfRegularEquations_ker X E hE).trans hI)
  change ((effectiveCartierKernelIso X E hE).hom ≫
    (kernelIsoOfKerEq _ i
      ((effectiveCartierIdealDataOfRegularEquations_ker X E hE).trans hI)).hom) ≫
        schemeKernelIdealι i = _
  rw [Category.assoc, hk, effectiveCartierKernelIso_hom_ι]

/-- Actual Cartier multiplication cancels the original exceptional kernel. -/
def positiveKernelTensorIso {X Z : Scheme.{u}} [IsIntegral X]
    (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hI : effectiveCartierIdealDataOfRegularEquations X E hE = i.ker) :
    cartierDivisorModule X E ⊗ schemeKernelIdeal i ≅ 𝟙_ X.Modules := by
  have hzero : principalCartierDivisorHom X (Additive.ofMul (1 : X.functionFieldˣ)) = 0 :=
    map_zero (principalCartierDivisorHom X)
  exact tensorIso (Iso.refl _) (negativeKernelIso E hE i hI).symm ≪≫
    cartierTensorIso X E (-E) ≪≫
    eqToIso (congrArg (cartierDivisorModule X) ((add_neg_cancel E).trans hzero.symm)) ≪≫
    principalCartierModuleIsoUnit X 1 ≪≫ SchemeModuleStructureUnit.iso X

end KltDP.Geometry.CartierExceptionalKernelTensor

#check @KltDP.Geometry.CartierExceptionalKernelTensor.positiveKernelTensorIso
#print axioms KltDP.Geometry.CartierExceptionalKernelTensor.negativeKernelIso_hom_inclusion
#print axioms KltDP.Geometry.CartierExceptionalKernelTensor.positiveKernelTensorIso

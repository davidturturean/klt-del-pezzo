import KltDP.Geometry.GluedConormalTildeDualChart
import KltDP.Geometry.EffectiveCartierIdeal
import KltDP.Geometry.CartierTensorProduct

/-!
# The original normal sheaf as the positive Cartier line

The original Cartier multiplication and the original sheaf evaluation identify
the dual of O(-E) with O(E). The accepted kernel comparison and the original
pullback-dual comparison then identify the actual normal sheaf of the original
effective Cartier zero scheme with the restriction of O(E).
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u
namespace KltDP.Geometry.GluedAdjunctionCartierNormal

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance structureSectionsComm (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.val.obj U) :=
  fun U => by
    change IsMulCommutative (X.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable (X : Scheme.{u}) [IsIntegral X]

/-- The original principal trivialization for the zero Cartier divisor. -/
def zeroIso : cartierDivisorModule X 0 ≅ _root_.SheafOfModules.unit X.ringCatSheaf := by
  simpa only [ofMul_one, map_zero] using
    principalCartierModuleIsoUnit X (1 : X.functionFieldˣ)

/-- Original Cartier multiplication, followed by the original unit comparison. -/
def oppositePair (E : CartierDivisor X) :
    cartierDivisorModule X E ⊗ cartierDivisorModule X (-E) ≅ 𝟙_ X.Modules :=
  cartierTensorIso X E (-E) ≪≫
    eqToIso (congrArg (cartierDivisorModule X) (add_neg_cancel E)) ≪≫
    zeroIso X ≪≫
    (PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond).symm

/-- The actual dual of the negative Cartier module, using its original evaluation. -/
def negativeDualIso (E : CartierDivisor X) :
    KltDP.SheafOfModules.dual X.ringCatSheaf (cartierDivisorModule X (-E)) ≅
      cartierDivisorModule X E :=
  let L := cartierDivisorModule X (-E)
  let D := KltDP.SheafOfModules.dual X.ringCatSheaf L
  let P := cartierDivisorModule X E
  (λ_ D).symm ≪≫
    (whiskerRightIso (oppositePair X E) D).symm ≪≫
    (α_ P L D) ≪≫
    whiskerLeftIso P
      (KltDP.SheafOfModules.tensorDualIsoUnit X.sheaf.val X.ringCatSheaf.cond L) ≪≫
    (ρ_ P)

/-- The original structural kernel, after duality and pullback, is the positive Cartier line.
Every comparison in this composite is the accepted comparison for the original objects. -/
def normalIso (E : CartierDivisor X) (hE : HasRegularCartierEquations X E) :
    GluedConormalTildeDualChart.globalNormalSheaf
        (effectiveCartierIdealDataOfRegularEquations X E hE) ≅
      (schemeModulePullback (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo).obj
        (cartierDivisorModule X E) :=
  let I := effectiveCartierIdealDataOfRegularEquations X E hE
  let hI := effectiveCartierIdealDataOfRegularEquations_regular X E hE
  (schemeModulePullbackDualIso I.gluedTo (gluedKernelLine I hI)).symm ≪≫
    (schemeModulePullback I.gluedTo).mapIso
      (sectionDualIso X (effectiveCartierKernelIso X E hE)) ≪≫
    (schemeModulePullback I.gluedTo).mapIso (negativeDualIso X E)

end KltDP.Geometry.GluedAdjunctionCartierNormal

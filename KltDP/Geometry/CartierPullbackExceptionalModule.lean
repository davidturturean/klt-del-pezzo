import KltDP.Geometry.CartierExceptionalKernelTensor
import KltDP.Geometry.DominantCartierPullbackModule

/-!
# The Cartier module of a pullback plus the actual exceptional divisor

Apply the original signed Cartier pullback comparison to a given Cartier
representative. Tensor the actual exceptional-kernel factor with O(E), then
cancel that kernel by the original Cartier multiplication. The construction
uses the given whole-map factor itself, not a Picard-class equality.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.CartierPullbackExceptionalModule

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- The original factor through the exceptional ideal makes the literal
Cartier divisor `π*K + E` a representative of the original target module. -/
def ofFactorIso {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (π : X ⟶ Y) [GenericPointPreserving π]
    (K : CartierDivisor Y) (M : Y.Modules) (N : X.Modules)
    (eK : cartierDivisorModule Y K ≅ M)
    (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hI : effectiveCartierIdealDataOfRegularEquations X E hE = i.ker)
    (eFactor : (schemeModulePullback π).obj M ≅ schemeKernelIdeal i ⊗ N) :
    cartierDivisorModule X (DominantCartierPullback.pullbackHom π K + E) ≅ N :=
  eqToIso (congrArg (cartierDivisorModule X)
    (add_comm (DominantCartierPullback.pullbackHom π K) E)) ≪≫
  (cartierTensorIso X E (DominantCartierPullback.pullbackHom π K)).symm ≪≫
  tensorIso (Iso.refl _)
    ((DominantCartierPullback.modulePullbackIso π K).symm ≪≫
      (schemeModulePullback π).mapIso eK ≪≫ eFactor) ≪≫
  (α_ (cartierDivisorModule X E) (schemeKernelIdeal i) N).symm ≪≫
  tensorIso (CartierExceptionalKernelTensor.positiveKernelTensorIso E hE i hI)
    (Iso.refl N) ≪≫
  λ_ N

end KltDP.Geometry.CartierPullbackExceptionalModule

#check @KltDP.Geometry.CartierPullbackExceptionalModule.ofFactorIso
#print axioms KltDP.Geometry.CartierPullbackExceptionalModule.ofFactorIso

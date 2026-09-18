import KltDP.Geometry.OriginalCartierRamificationIdealRegular
import KltDP.Geometry.OriginalCartierQuadraticSurface
import KltDP.Geometry.ClosedImmersionKerDegree

/-!
# The actual ramification Cartier divisor on the original quadratic surface

The original reduced nonempty Cartier branch produces the already proved
normal projective surface on the unchanged cover. Its actual ramification
kernel has proved local regular equations. The existing divisor-of-ideal
construction therefore gives an actual Cartier divisor R whose canonical
ideal is exactly the original root-zero immersion's kernel. Its negative
Cartier module is the actual kernel module, without changing the cover.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.OriginalCartierRamificationSmooth

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)

local instance originalCartierRamificationDivisorSeparated : S.toScheme.IsSeparated :=
  NormalProjectiveSurface.surfaceSeparated S
local instance originalCartierRamificationDivisorMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

variable (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
    (hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)

local notation "A" => effectiveCartierQuadraticAtlas S.toScheme E hE L e
local notation "T" => OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne

local instance originalCartierRamificationDivisorClosed : IsClosedImmersion (A).rootZeroGlobalι :=
  (A).rootZeroGlobalι_isClosedImmersion

/-- The actual ramification divisor on the unchanged original quadratic surface. -/
def originalRamificationDivisor : CartierDivisor (T).toScheme :=
  cartierDivisorOfIdeal (T).toScheme (A).rootZeroGlobalι.ker
    (original_rootZeroGlobal_kernel_locallyPrincipalRegular S.toScheme E hE L e)

/-- Its effectiveness and regular equations are proved from the original branch data. -/
theorem originalRamificationDivisor_hasRegularEquations :
    HasRegularCartierEquations (T).toScheme (originalRamificationDivisor S E hE L e h2 hred hne) :=
  cartierDivisorOfIdeal_hasRegularEquations (T).toScheme (A).rootZeroGlobalι.ker
    (original_rootZeroGlobal_kernel_locallyPrincipalRegular S.toScheme E hE L e)

/-- The divisor's canonical ideal is exactly the original global root-zero kernel. -/
theorem originalRamificationDivisor_ideal :
    effectiveCartierIdealDataOfRegularEquations (T).toScheme
      (originalRamificationDivisor S E hE L e h2 hred hne)
      (originalRamificationDivisor_hasRegularEquations S E hE L e h2 hred hne) =
        (A).rootZeroGlobalι.ker :=
  cartierDivisorOfIdeal_idealData (T).toScheme (A).rootZeroGlobalι.ker
    (original_rootZeroGlobal_kernel_locallyPrincipalRegular S.toScheme E hE L e)

/-- The negative ramification Cartier module is the actual original kernel module. -/
def originalRamificationDivisor_kernelIso :
    cartierDivisorModule (T).toScheme (-(originalRamificationDivisor S E hE L e h2 hred hne)) ≅
      schemeKernelIdeal (A).rootZeroGlobalι :=
  effectiveCartierKernelIso (T).toScheme _
      (originalRamificationDivisor_hasRegularEquations S E hE L e h2 hred hne) ≪≫
    kernelIsoOfKerEq _ (A).rootZeroGlobalι
      (((effectiveCartierIdealDataOfRegularEquations (T).toScheme
        (originalRamificationDivisor S E hE L e h2 hred hne)
        (originalRamificationDivisor_hasRegularEquations S E hE L e h2 hred hne)).ker_gluedTo).trans
          (originalRamificationDivisor_ideal S E hE L e h2 hred hne))

end KltDP.Geometry.OriginalCartierRamificationSmooth

#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.originalRamificationDivisor
#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.originalRamificationDivisor_ideal
#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.originalRamificationDivisor_kernelIso

import KltDP.Geometry.QuadraticRootGlobalIdealRegular
import KltDP.Geometry.OriginalCartierQuadraticIntegral

/-!
# Original Cartier data supplies actual regular ramification equations

Nonvanishing of the original canonical Cartier section gives nonzero
coefficients on every nonempty original affine chart. Since the base is
integral, these coefficients are regular. The proved root-atlas kernel
comparison therefore makes the actual global ramification kernel locally
principal regular. Neither local equations nor cover regularity is an input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.OriginalCartierRamificationSmooth

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated]

local instance originalCartierRamificationIdealRegularMonoidal : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- The unchanged original cover has a locally principal regular actual ramification ideal. -/
theorem original_rootZeroGlobal_kernel_locallyPrincipalRegular
    (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X E) :
    IdealLocallyPrincipalRegular
      (effectiveCartierQuadraticAtlas X E hE L e).rootZeroGlobalι.ker := by
  apply QuadraticCoverAtlas.Data.rootZeroGlobal_kernel_locallyPrincipalRegular
  intro i hi
  obtain ⟨x, hx⟩ := hi
  letI : Nonempty ((effectiveCartierQuadraticAtlas X E hE L e).opens i) := ⟨⟨x, hx⟩⟩
  letI : Nonempty (AffineOpenRefinement.opens X L.localTrivializations.X i).toScheme := ⟨⟨x, hx⟩⟩
  apply mem_nonZeroDivisors_of_ne_zero
  exact InvertibleQuadraticAtlas.fromSquareRoot_coefficient_ne_zero X L
    (cartierDivisorModule X E) e (effectiveCartierSection X E hE)
    (effectiveCartierSection_ne_zero X E hE) i

end KltDP.Geometry.OriginalCartierRamificationSmooth

#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.original_rootZeroGlobal_kernel_locallyPrincipalRegular

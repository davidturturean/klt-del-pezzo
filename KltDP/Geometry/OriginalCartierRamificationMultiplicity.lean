import KltDP.Geometry.OriginalCartierRamificationDivisor
import KltDP.Geometry.QuadraticOriginalRamificationMultiplicity

/-!
# Multiplicity two for the original ramification Cartier divisor

The unchanged cover's canonical branch coefficients supply all inputs to
the proved affine ideal-square comparison. The existing divisor-of-ideal
theorems then identify the actual Cartier pullback of E with twice the
actual ramification divisor R. Integrality of the cover is derived from
the original reduced nonempty branch, rather than supplied.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.OriginalCartierRamificationSmooth

open CartierDivisorPullbackIdeal QuadraticCover

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)

local instance originalCartierRamificationMultiplicitySeparated : S.toScheme.IsSeparated :=
  NormalProjectiveSurface.surfaceSeparated S
local instance originalCartierRamificationMultiplicityMonoidal : MonoidalCategory S.toScheme.Modules :=
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

local instance originalCartierRamificationMultiplicityClosed : IsClosedImmersion (A).rootZeroGlobalι :=
  (A).rootZeroGlobalι_isClosedImmersion

private theorem original_branchIdeal_on_chart
    (i : AffineOpenRefinement.Index S.toScheme L.localTrivializations.X) :
    (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).ideal
      ⟨(A).opens i, (A).affine i⟩ = branchIdeal ((A).sections i) := by
  rw [← effectiveCartierIdealData_eq_ofRegularEquations S.toScheme E hE L e]
  exact effectiveCartierIdealData_eq_quadraticBranchIdeal S.toScheme E hE L e i

private theorem original_branchCoefficient_regular
    (i : AffineOpenRefinement.Index S.toScheme L.localTrivializations.X)
    (hi : ((A).opens i : Set S.toScheme).Nonempty) :
    (A).sections i ∈ nonZeroDivisors Γ(S.toScheme, (A).opens i) := by
  obtain ⟨x, hx⟩ := hi
  letI : Nonempty ((A).opens i) := ⟨⟨x, hx⟩⟩
  letI : Nonempty (AffineOpenRefinement.opens S.toScheme L.localTrivializations.X i).toScheme :=
    ⟨⟨x, hx⟩⟩
  apply mem_nonZeroDivisors_of_ne_zero
  exact InvertibleQuadraticAtlas.fromSquareRoot_coefficient_ne_zero S.toScheme L
    (cartierDivisorModule S.toScheme E) e (effectiveCartierSection S.toScheme E hE)
    (effectiveCartierSection_ne_zero S.toScheme E hE) i

/-- The actual pullback of the original branch is twice the actual ramification divisor. -/
theorem original_pullback_branch_eq_two_ramification :
    letI : IsIntegral (A).scheme := (T).integral
    letI : GenericPointPreserving (A).morphism := (A).morphism_genericPointPreserving
    pullbackDivisor (A).morphism E hE =
      (2 : ℕ) • originalRamificationDivisor S E hE L e h2 hred hne := by
  letI : IsIntegral (A).scheme := (T).integral
  letI : GenericPointPreserving (A).morphism := (A).morphism_genericPointPreserving
  let hJ := original_rootZeroGlobal_kernel_locallyPrincipalRegular S.toScheme E hE L e
  have hideal := (A).pullbackIdealData_eq_rootZeroKernel_sq E hE
    (original_branchIdeal_on_chart S E hE L e)
    (original_branchCoefficient_regular S E hE L e)
  calc
    pullbackDivisor (A).morphism E hE =
        cartierDivisorOfIdeal (A).scheme (pullbackIdealData (A).morphism E hE)
          (pullbackIdealData_locallyPrincipalRegular (A).morphism E hE) :=
      pullbackDivisor_eq_cartierDivisorOfIdeal (A).morphism E hE
    _ = cartierDivisorOfIdeal (A).scheme (idealSheafDataPow (A).rootZeroGlobalι.ker 2)
          (idealSheafDataPow_locallyPrincipalRegular hJ 2) :=
      cartierDivisorOfIdeal_congr (A).scheme _ _ hideal
        (idealSheafDataPow_locallyPrincipalRegular hJ 2)
    _ = (2 : ℕ) • cartierDivisorOfIdeal (A).scheme (A).rootZeroGlobalι.ker hJ :=
      cartierDivisorOfIdeal_pow (A).scheme (A).rootZeroGlobalι.ker hJ 2
    _ = (2 : ℕ) • originalRamificationDivisor S E hE L e h2 hred hne := rfl

end KltDP.Geometry.OriginalCartierRamificationSmooth

#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.original_pullback_branch_eq_two_ramification


import KltDP.Geometry.QuadraticOriginalCanonicalFactor
import KltDP.Geometry.OriginalCartierRamificationDivisor
import KltDP.Geometry.OriginalCartierQuadraticRegular
import KltDP.Geometry.RegularSurfaceSmoothLiteralUse

/-!
# The actual Hurwitz factor for the original Cartier square-root cover

The original Cartier ideal and canonical section supply the exact original
coefficient equations and regularity. Smoothness of the same cover is
obtained from its proved all-point regularity and the existing regular
surface smoothness theorem. The constructed canonical factor therefore
requires no cover smoothness, local frame, or canonical formula premise.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.OriginalCartierRamificationSmooth

open TransitionUnitGluing SchemeTopDifferentialFactorSquare
attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k]
  (S : NormalProjectiveSurface k) [IsSmoothOfRelativeDimension 2 S.structureMorphism]

local instance originalCartierCanonicalSeparated : S.toScheme.IsSeparated :=
  NormalProjectiveSurface.surfaceSeparated S
local instance originalCartierCanonicalModules (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

variable (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
  (L : InvertibleSheaf S.toScheme)
  (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
  (hred : IsReduced (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
  (hne : Nonempty (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
  [IsSmoothOfRelativeDimension 1
    ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism)]

local notation "A" => effectiveCartierQuadraticAtlas S.toScheme E hE L e
local notation "T" => OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
local notation "I" => effectiveCartierIdealDataOfRegularEquations S.toScheme E hE

/-- The same original quadratic surface is smooth of relative dimension two. -/
theorem originalCover_smoothTwo : IsSmoothOfRelativeDimension 2 (T).structureMorphism := by
  letI : IsSmooth S.structureMorphism := IsSmoothOfRelativeDimension.isSmooth 2 S.structureMorphism
  exact (T).isSmoothOfRelativeDimension_two_of_regularPoints
    (regularPoints_of_smooth_base_and_branch S E hE L e h2 hred hne
      (IsSmoothOfRelativeDimension.isSmooth 1 ((I).gluedTo ≫ S.structureMorphism)))

/-- The branch ideal on each original atlas chart is its original coefficient ideal. -/
theorem originalCanonical_branchEquation
    (i : AffineOpenRefinement.Index S.toScheme L.localTrivializations.X) :
    (I).ideal ⟨(A).opens i, (A).affine i⟩ = Ideal.span {(A).sections i} := by
  rw [← effectiveCartierIdealData_eq_ofRegularEquations S.toScheme E hE L e]
  exact effectiveCartierIdealData_eq_quadraticBranchIdeal S.toScheme E hE L e i

/-- The original canonical Cartier section gives regular original coefficients. -/
theorem originalCanonical_coefficient_regular
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

/-- The original base canonical sheaf pulls back to O(-R) tensored with
canonical differentials of the same original constructed cover. -/
def originalCartierCanonicalFactor :
    (schemeModulePullback (A).morphism).obj (top S.structureMorphism 2) ≅
      cartierDivisorModule (T).toScheme (-(originalRamificationDivisor S E hE L e h2 hred hne)) ⊗
        top (T).structureMorphism 2 := by
  letI : IsIntegral (A).scheme := (T).integral
  letI : IsSmoothOfRelativeDimension 2 ((A).morphism ≫ S.structureMorphism) :=
    originalCover_smoothTwo S E hE L e h2 hred hne
  have h2' : IsUnit (2 : Γ(S.toScheme, ⊤)) := by
    simpa only [map_ofNat] using h2.map
      (S.structureMorphism.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
  exact (A).originalCanonicalFactor S.structureMorphism h2' (I)
    (effectiveCartierIdealDataOfRegularEquations_regular S.toScheme E hE)
    (originalCanonical_branchEquation S E hE L e)
    (originalCanonical_coefficient_regular S E hE L e) ≪≫
      tensorIso (originalRamificationDivisor_kernelIso S E hE L e h2 hred hne).symm (Iso.refl _)

end KltDP.Geometry.OriginalCartierRamificationSmooth

#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.originalCover_smoothTwo
#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.originalCartierCanonicalFactor

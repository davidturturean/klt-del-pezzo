import KltDP.Geometry.OriginalCartierRamificationMultiplicity
import KltDP.Geometry.CartierPullbackComparison

/-!
# The actual doubled ramification and half-branch Picard classes

The original tensor-square isomorphism identifies the branch class with
twice the original line class. The proved original Cartier pullback
π*E = 2R therefore identifies the doubled classes of R and π*L.
No cancellation in the Picard group is asserted.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.OriginalCartierRamificationSmooth

open CartierDivisorPullbackIdeal
attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)

local instance ramificationHalfLineSeparated : S.toScheme.IsSeparated :=
  NormalProjectiveSurface.surfaceSeparated S
local instance ramificationHalfLineModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
  (L : InvertibleSheaf S.toScheme)
  (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
  (hred : IsReduced (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
  (hne : Nonempty (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)

local notation "A" => effectiveCartierQuadraticAtlas S.toScheme E hE L e
local notation "T" => OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
local notation "R₀" => originalRamificationDivisor S E hE L e h2 hred hne

include e in
/-- The actual original tensor square supplies the branch Picard equation. -/
theorem original_branchPicard_eq_twice_line :
    cartierPicardHom S.toScheme E = (2 : ℕ) • Additive.ofMul L.toPic := by
  have hc : cartierPicardClass S.toScheme E = L.toPic * L.toPic := by
    apply Units.ext
    change ((cartierDivisorInvertibleSheaf S.toScheme E).toPic : Skeleton S.toScheme.Modules) =
      (L.toPic : Skeleton S.toScheme.Modules) * (L.toPic : Skeleton S.toScheme.Modules)
    simp only [InvertibleSheaf.toPic_val, ← Skeleton.toSkeleton_tensorObj]
    exact Quotient.sound ⟨e.symm⟩
  change Additive.ofMul (cartierPicardClass S.toScheme E) = _
  rw [hc, ofMul_mul, two_nsmul]

/-- Twice the actual ramification class is twice the pullback of the
original half-branch line; the original atlas and pullback are retained. -/
theorem original_ramificationPicard_twice :
    letI : IsIntegral (T).toScheme := (T).integral
    (2 : ℕ) • cartierPicardHom (T).toScheme (R₀) =
      (2 : ℕ) • (schemePicardPullbackHom (A).morphism).toAdditive (Additive.ofMul L.toPic) := by
  letI : IsIntegral (T).toScheme := (T).integral
  letI : IsIntegral (A).scheme := (T).integral
  letI : GenericPointPreserving (A).morphism := (A).morphism_genericPointPreserving
  let c := cartierPicardHom (A).scheme
  let P := (schemePicardPullbackHom (A).morphism).toAdditive
  change (2 : ℕ) • c (R₀) = (2 : ℕ) • P (Additive.ofMul L.toPic)
  have hdiv : pullbackDivisor (A).morphism E hE = (2 : ℕ) • (R₀) :=
    original_pullback_branch_eq_two_ramification S E hE L e h2 hred hne
  have hpull : c (pullbackDivisor (A).morphism E hE) = P (cartierPicardHom S.toScheme E) :=
    CartierPullbackComparison.cartierPicardHom_pullbackDivisor_eq (A).morphism E hE
  have hbranch : cartierPicardHom S.toScheme E = (2 : ℕ) • Additive.ofMul L.toPic :=
    original_branchPicard_eq_twice_line S E L e
  exact (map_nsmul c 2 (R₀)).symm.trans
    ((congrArg c hdiv).symm.trans
      (hpull.trans ((congrArg P hbranch).trans (map_nsmul P 2 (Additive.ofMul L.toPic)))))

end KltDP.Geometry.OriginalCartierRamificationSmooth

#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.original_ramificationPicard_twice

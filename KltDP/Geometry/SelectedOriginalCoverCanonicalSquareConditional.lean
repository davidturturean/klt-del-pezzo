import KltDP.Geometry.OriginalQuadraticIntersectionPullbackConditional
import KltDP.Geometry.EvenDisjointSelectionEuler

/-!
# The actual canonical square for a disjoint minus-two branch selection

The actual selected branch intersection and its original tensor-square
line determine the half-line square and canonical pairing. Substitution
in the original cover's Hurwitz intersection formula gives KY²=2KS²−n.
All branch curves, divisor classes, and the quadratic morphism remain the
original geometric objects.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped BigOperators
universe u

namespace KltDP.Geometry.OriginalCartierRamificationSmooth

open ModuleCohomology SmoothCanonicalCartierRepresentative
attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance selectedCanonicalSquareModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable (hAffine : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsAffineHom f] (n : ℕ),
    ∃ e : ∀ (M : X.Modules), M.IsQuasicoherent →
      H ((schemeModulePushforward f).obj M) n ≃+ H M n,
      ∀ (M N : X.Modules) (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent)
        (φ : M ⟶ N) (x : H ((schemeModulePushforward f).obj M) n),
        e N hN ((zariskiFunctor Y n).map ((schemeModulePushforward f).map φ) x) =
          (zariskiFunctor X n).map φ (e M hM x))

include hAffine

variable {k : Type u} [Field k] [IsAlgClosed k]
  (S : NormalProjectiveSurface k) [IsSmoothOfRelativeDimension 2 S.structureMorphism]

local instance selectedCanonicalSquareSeparated : S.toScheme.IsSeparated :=
  NormalProjectiveSurface.surfaceSeparated S

variable (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
  (L : InvertibleSheaf S.toScheme)
  (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
  (hred : IsReduced (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
  (hne : Nonempty (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
  [IsSmoothOfRelativeDimension 1
    ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism)]

local notation "T" => OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne

/-- The manuscript's canonical-square identity, for the same original
cover branched over its original selected disjoint minus-two curves. -/
theorem originalSelectedCover_canonical_selfIntersection
    (hS : ∀ x : S.Point, RegularPoint S.toScheme x)
    (hT : ∀ y : (T).Point, RegularPoint (T).toScheme y)
    (N : Finset S.PrimeCurve) (hselected : S.cartierToWeilHom E = S.selectedPrimeWeil N)
    (hdisj : (N : Set S.PrimeCurve).Pairwise fun C D =>
      Disjoint (C : Set S.toScheme) (D : Set S.toScheme))
    (hself : ∀ C ∈ N, C.selfIntersectionNumber hS = -2)
    (hK : ∀ C ∈ N, C.intersectionNumber (cartierRepresentative S.structureMorphism) = 0) :
    letI : IsIntegral (T).toScheme := (T).integral
    letI : IsSmoothOfRelativeDimension 2 (T).structureMorphism :=
      originalCover_smoothTwo S E hE L e h2 hred hne
    (T).intersectionPairing hT (cartierRepresentative (T).structureMorphism)
        (cartierRepresentative (T).structureMorphism) =
      2 * S.intersectionPairing hS (cartierRepresentative S.structureMorphism)
        (cartierRepresentative S.structureMorphism) - (N.card : ℤ) := by
  classical
  letI : IsIntegral (T).toScheme := (T).integral
  letI : IsSmoothOfRelativeDimension 2 (T).structureMorphism :=
    originalCover_smoothTwo S E hE L e h2 hred hne
  let K := cartierRepresentative S.structureMorphism
  have he : cartierPicardClass S.toScheme E = L.toPic * L.toPic := by
    have he' := congrArg Additive.toMul (original_branchPicard_eq_twice_line S E L e)
    simpa only [cartierPicardHom_apply, two_nsmul, toMul_add, toMul_ofMul] using he'
  have hdiag : S.picardPairing hS (L.toPic * L.toPic) (L.toPic * L.toPic) =
      -2 * (N.card : ℤ) := by
    rw [← he, S.picardPairing_class]
    exact S.selectedPrime_intersectionPairing_self hS N E hselected hdisj hself
  simp only [S.picardPairing_mul_left_of_regular, S.picardPairing_mul_right_of_regular] at hdiag
  have hcanonical : S.picardPairing hS (L.toPic * L.toPic) (cartierPicardClass S.toScheme K) = 0 := by
    rw [← he, S.picardPairing_class, S.selectedPrime_intersectionPairing hS N E hselected K]
    exact Finset.sum_eq_zero fun C hC => hK C hC
  rw [S.picardPairing_mul_left_of_regular] at hcanonical
  have hLK : S.picardPairing hS L.toPic (cartierPicardClass S.toScheme K) = 0 := by omega
  have hKL : S.picardPairing hS (cartierPicardClass S.toScheme K) L.toPic = 0 := by
    rw [S.picardPairing_symm, hLK]
  rw [originalCover_canonical_selfIntersection hAffine S E hE L e h2 hred hne hS hT]
  change 2 * S.picardPairing hS (cartierPicardClass S.toScheme K * L.toPic)
      (cartierPicardClass S.toScheme K * L.toPic) = _
  rw [S.picardPairing_mul_left_of_regular, S.picardPairing_mul_right_of_regular,
    S.picardPairing_mul_right_of_regular, hLK, hKL, S.picardPairing_class]
  dsimp only [K]
  omega

end KltDP.Geometry.OriginalCartierRamificationSmooth

#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.originalSelectedCover_canonical_selfIntersection

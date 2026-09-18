import KltDP.Examples.FrobeniusContactTowerCanonicalFactorIdeals
import KltDP.Examples.FrobeniusContactTowerCanonicalIteration
import KltDP.Geometry.RationalTreePicardMultidegree

/-!
# The iterated exceptional tensor has the accepted total exceptional classes

The recursive actual ideal tensor is compared with the previously defined
total exceptional classes of the original translated tower. The equality
uses the proved tensor and pullback Picard maps and finite-sum recursion.
This identifies the actual target line of the normalized tower factor;
it does not define a canonical class or assume a canonical formula.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusContactTowerCanonicalFactorPicard

open KltDP.Geometry KltDP.Geometry.RationalTreePicard
open FrobeniusGlobalBlowupStages FrobeniusGlobalBlowupCanonicalTarget
open FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint FrobeniusTowerTransportClasses
open FrobeniusContactTowerCanonicalFactorTensor FrobeniusContactTowerCanonicalFactorIdeals
open FrobeniusContactTowerCanonicalIteration

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance factorPicardModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- The class of the original tensor is the product of the original two line classes. -/
theorem tensorLine_toPic {X : Scheme.{u}} (L M : InvertibleSheaf X) :
    (tensorLine L M).toPic = L.toPic * M.toPic := by
  apply Units.ext
  change ((tensorLine L M).toPic : Skeleton X.Modules) =
    (L.toPic : Skeleton X.Modules) * (M.toPic : Skeleton X.Modules)
  rw [InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val]
  exact Skeleton.toSkeleton_tensorObj _ _

private theorem tensorPullback_neg_toPic {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L : InvertibleSheaf X) (M : InvertibleSheaf Y) :
    -Additive.ofMul (tensorLine (pullbackInvertibleSheaf f L) M).toPic =
      (schemePicardPullbackHom f).toAdditive (-Additive.ofMul L.toPic) +
        -Additive.ofMul M.toPic := by
  rw [tensorLine_toPic, map_neg]
  change -Additive.ofMul ((pullbackInvertibleSheaf f L).toPic * M.toPic) =
    -Additive.ofMul (schemePicardPullbackHom f L.toPic) + -Additive.ofMul M.toPic
  rw [schemePicardPullbackHom_toPic, ofMul_mul]
  abel

variable {k : Type u} [Field k]

/-- The original recursive ideal contributes the actual new exceptional class at each step. -/
theorem translatedIdealClass_succ (p : ℕ) (a : k) (N : ℕ) :
    -Additive.ofMul (totalExceptionalIdealLine (translatedInitial p a) (N + 1)).toPic =
      (schemePicardPullbackHom ((translatedInitial p a).stepProjection N)).toAdditive
        (-Additive.ofMul (totalExceptionalIdealLine (translatedInitial p a) N).toPic) +
      translatedStepExceptionalClass p a N :=
  tensorPullback_neg_toPic ((translatedInitial p a).stepProjection N)
    (totalExceptionalIdealLine (translatedInitial p a) N)
    (translatedStepExceptionalIdealLine p a N)

/-- The inverse class of the actual recursive ideal tensor is the sum of the accepted
original total exceptional classes, with their original tower projections. -/
theorem translatedIdealClass (p : ℕ) (a : k) (N : ℕ) :
    -Additive.ofMul (totalExceptionalIdealLine (translatedInitial p a) N).toPic =
      ∑ j : Fin N, translatedTotalExceptionalClass p a N j := by
  induction N with
  | zero =>
      have h : (totalExceptionalIdealLine (translatedInitial p a) 0).toPic = 1 :=
        (toPic_eq_one_iff_iso_unit _).mpr ⟨Iso.refl _⟩
      rw [h, ofMul_one, neg_zero, Fin.sum_univ_zero]
  | succ N ih =>
      rw [translatedIdealClass_succ, ih, map_sum, Fin.sum_univ_castSucc,
        translatedTotalExceptionalClass_last]
      simp only [translatedTotalExceptionalClass_castSucc]

end KltDP.Examples.FrobeniusContactTowerCanonicalFactorPicard


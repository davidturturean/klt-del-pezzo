import KltDP.Geometry.OriginalUnbranchedRationalTreeGram
import KltDP.Geometry.RationalComponentPrimeCurvesIncidence
import KltDP.Geometry.ActualExceptionalNegativeGram
import KltDP.LinearAlgebra.RemovedConfigurationDimension
import Mathlib.Logic.Equiv.Prod

/-!
# Actual doubled exceptional-tree negativity and independence

The original proper birational contraction supplies negative definiteness
of its actual component curves; injectivity is proved from the original
tree immersion. The unchanged quadratic-cover component classes have that
same Gram matrix on each coherent sheet and are mutually orthogonal.
Existing orthogonal-copy and reindexing theorems therefore give the actual
doubled negative Gram, independence, and exact span dimension. Neither a
target matrix/sign condition nor independence nor a dimension equation is
supplied as an input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
open scoped BigOperators
universe u

namespace KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry

open NormalProjectiveSurface RationalTreePicard DisjointNegativeCurvesRank
open KltDP.LinearAlgebra.CanonicalCorrection

variable {k : Type u} [Field k] [IsAlgClosed k]
    (S : NormalProjectiveSurface k) [IsSmooth S.structureMorphism]

local instance originalUnbranchedTreeIndependenceSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance originalUnbranchedTreeIndependenceMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

variable {C : Scheme.{u}} [NoetherianSpace C] [IsLocallyNoetherian C] [IsReduced C]
    [ConnectedSpace C] [C.IsSeparated]
    (sC : C ⟶ Spec (CommRingCat.of k)) [IsProper sC]
    (hdim : topologicalKrullDim C ≤ 1)
    (hTree : (componentPointIncidenceGraph C).IsTree)
    (htrans : HasTransverseComponentBranches C)
    (eC : ∀ D : ↥(irreducibleComponents C), componentUnionScheme C {D} ≅ projectiveSpace k 1)
    (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
    (hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hsm : IsSmooth
      ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism))
    (f : C ⟶ S.toScheme) [IsClosedImmersion f]
    (hdisj : Disjoint (Set.range f.base)
      (Set.range (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo.base))

local instance originalUnbranchedTreeComponentFintype : Fintype ↥(irreducibleComponents C) :=
  NoetherianSpace.finite_irreducibleComponents.fintype

local notation "CoverSurface" =>
  OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
local notation "CoverRegular" =>
  OriginalCartierRamificationSmooth.regularPoints_of_smooth_base_and_branch
    S E hE L e h2 hred hne hsm
local notation "CoverForm" =>
  NormalProjectiveSurface.numericalIntersectionBilinForm CoverSurface CoverRegular
local notation "baseCurve" => RationalComponentPrimeCurves.curve S f eC
local notation "copyClass" =>
  numericalCopy S sC hdim hTree htrans eC E hE L e h2 hred hne hsm f hdisj

variable {X : NormalProjectiveSurface k} (r : S.toScheme ⟶ X.toScheme) [IsProper r]
    (hr : r ≫ X.structureMorphism = S.structureMorphism) (hbir : IsBirationalScheme r)
    (hcontracted : ∀ D : ↥(irreducibleComponents C),
      IsExceptionalCurve r (RationalComponentPrimeCurves.curve S f eC D))

include f eC hr hbir hcontracted

/-- The two actual coherent sheets have positive-definite negative Gram as an orthogonal union. -/
theorem actual_sum_negativeGram_posDef :
    (negativeGram CoverForm (Sum.elim (copyClass false) (copyClass true))).PosDef := by
  have hbase := ActualExceptionalNegativeDefinite.negativeGram_posDef r hr hbir
    S.regularPoints_of_isSmooth (baseCurve)
    (RationalComponentPrimeCurves.curve_injective S f eC) hcontracted
  apply KltDP.LinearAlgebra.orthogonal_sum_negativeGram_posDef
    CoverForm (copyClass false) (copyClass true)
  · rw [negativeGram_numericalCopy S sC hdim hTree htrans eC E hE L e h2 hred hne hsm f hdisj false]
    exact hbase
  · rw [negativeGram_numericalCopy S sC hdim hTree htrans eC E hE L e h2 hred hne hsm f hdisj true]
    exact hbase
  · intro D F
    exact numericalCopy_pairing_opposite S sC hdim hTree htrans eC E hE L e h2 hred hne hsm f hdisj false D F
  · intro F D
    exact numericalCopy_pairing_opposite S sC hdim hTree htrans eC E hE L e h2 hred hne hsm f hdisj true F D

/-- The original Bool-indexed actual curve family itself has positive-definite negative Gram. -/
theorem actual_doubled_negativeGram_posDef :
    (negativeGram CoverForm (fun i : Bool × ↥(irreducibleComponents C) => copyClass i.1 i.2)).PosDef := by
  have h := KltDP.LinearAlgebra.negativeGram_reindex_posDef
    CoverForm (Sum.elim (copyClass false) (copyClass true))
    (actual_sum_negativeGram_posDef S sC hdim hTree htrans eC E hE L e h2 hred hne hsm f hdisj
      r hr hbir hcontracted)
    (Equiv.boolProdEquivSum ↥(irreducibleComponents C)) (Equiv.boolProdEquivSum _).injective
  have hf : (Sum.elim (copyClass false) (copyClass true) ∘
      Equiv.boolProdEquivSum ↥(irreducibleComponents C)) =
      fun i : Bool × ↥(irreducibleComponents C) => copyClass i.1 i.2 := by
    funext i
    rcases i with ⟨ε, D⟩
    cases ε <;> rfl
  rw [hf] at h
  exact h

/-- Every nonzero coefficient vector on the actual doubled classes has strictly negative square. -/
theorem actual_numericalCopies_quadratic_neg (a : Bool × ↥(irreducibleComponents C) → ℚ)
    (ha : a ≠ 0) :
    CoverForm (∑ i, a i • copyClass i.1 i.2) (∑ i, a i • copyClass i.1 i.2) < 0 :=
  KltDP.LinearAlgebra.negativeGram_posDef_strictly_negative CoverForm
    (fun i : Bool × ↥(irreducibleComponents C) => copyClass i.1 i.2)
    (actual_doubled_negativeGram_posDef S sC hdim hTree htrans eC E hE L e h2 hred hne hsm f hdisj
      r hr hbir hcontracted) a ha

/-- The original numerical classes of all actual component copies are linearly independent. -/
theorem actual_numericalCopies_linearIndependent :
    LinearIndependent ℚ (fun i : Bool × ↥(irreducibleComponents C) => copyClass i.1 i.2) :=
  KltDP.LinearAlgebra.negativeGram_posDef_linearIndependent CoverForm
    (fun i : Bool × ↥(irreducibleComponents C) => copyClass i.1 i.2)
    (actual_doubled_negativeGram_posDef S sC hdim hTree htrans eC E hE L e h2 hred hne hsm f hdisj
      r hr hbir hcontracted)

/-- The actual doubled numerical span has exactly twice the original component count. -/
theorem actual_numericalCopies_span_finrank :
    Module.finrank ℚ (Submodule.span ℚ
      (Set.range (fun i : Bool × ↥(irreducibleComponents C) => copyClass i.1 i.2))) =
        2 * Nat.card ↥(irreducibleComponents C) := by
  rw [finrank_span_eq_card (actual_numericalCopies_linearIndependent
    S sC hdim hTree htrans eC E hE L e h2 hred hne hsm f hdisj r hr hbir hcontracted),
    Fintype.card_prod, Fintype.card_bool, Nat.card_eq_fintype_card]

end KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry

#print axioms KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry.actual_doubled_negativeGram_posDef
#print axioms KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry.actual_numericalCopies_linearIndependent
#print axioms KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry.actual_numericalCopies_span_finrank

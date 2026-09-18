import KltDP.Geometry.OriginalUnbranchedForestIntersectionMatrix
import KltDP.Geometry.ActualExceptionalNegativeGram
import KltDP.LinearAlgebra.OrthogonalCopyGram
import KltDP.LinearAlgebra.RemovedConfigurationDimension
import Mathlib.Logic.Equiv.Prod

/-!
# The actual whole-forest negative Gram and exact doubled numerical rank

The original proper birational map gives negative definiteness of ALL
retained exceptional primes, with injectivity supplied by the actual
component dictionary. The actual cover's two whole-forest sheets have
that same matrix and are orthogonal. Existing Gram lemmas therefore
prove negativity, independence, and exact doubled r minus n cardinality.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.UnbranchedExceptionalBlocks

open NormalProjectiveSurface ActualExceptionalIncidence ExceptionalForestClosedBlocks RationalTreePicard
open DisjointNegativeCurvesRank KltDP.LinearAlgebra.CanonicalCorrection

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (N : Finset S.PrimeCurve)
    [IsProper π] (hbir : IsBirationalScheme π)
    (hmin : IsMinimalResolution S X π) (hklt : IsKlt X)

local instance originalUnbranchedForestGramSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance originalUnbranchedForestGramMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

variable (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
    (hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hIJ : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
      Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N))
    (hiso : IsolatedSelection π N)

local notation "CoverSurface" =>
  OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
local notation "CoverAtlas" => effectiveCartierQuadraticAtlas S.toScheme E hE L e

variable (hsm : IsSmooth
  ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism))

local notation "CoverRegular" =>
  MinimalResolutionQuadraticRegular.cover_regularPoints
    π hmin E hE L e h2 hred hne hsm
local notation "copy" => forestCurve π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso
local notation "base" => baseCurve π N hbir hmin hklt

local instance originalUnbranchedForestComponentsFinite : Finite (Components π N hbir) := by
  letI : Finite (Vertices π) := finite_vertices π hbir
  exact Finite.of_injective (originalVertex π N hbir) (originalVertex_injective π N hbir)

local instance originalUnbranchedForestComponentsFintype : Fintype (Components π N hbir) :=
  Fintype.ofFinite _

local notation "CoverForm" =>
  NormalProjectiveSurface.numericalIntersectionBilinForm CoverSurface CoverRegular

/-- The original numerical class of each actual coherent whole-forest curve. -/
def forestClass (ε : Bool) (i : Components π N hbir) : (CoverSurface).NumericalClassGroup :=
  curveClass CoverSurface CoverRegular (copy ε i)

local notation "copyClass" => forestClass π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso hsm

/-- Each coherent whole-forest sheet preserves the original numerical pairing. -/
theorem forestClass_pairing_same (ε : Bool) (i j : Components π N hbir) :
    CoverForm (copyClass ε i) (copyClass ε j) =
      S.numericalIntersectionBilinForm hmin.regular
        (curveClass S hmin.regular (base i))
        (curveClass S hmin.regular (base j)) := by
  rw [forestClass, forestClass, curveClass_pairing, curveClass_pairing,
    PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber
      CoverSurface CoverRegular (copy ε i) (copy ε j),
    PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber
      S hmin.regular (base i) (base j)]
  exact congrArg (fun n : ℤ => (n : ℚ))
    (forestCurve_intersection_same π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso hsm ε i j)

/-- Opposite whole-forest sheets are orthogonal in the original numerical class group. -/
theorem forestClass_pairing_opposite (ε : Bool) (i j : Components π N hbir) :
    CoverForm (copyClass ε i) (copyClass (!ε) j) = 0 :=
  curveClass_pairing_eq_zero_of_disjoint CoverSurface CoverRegular (copy ε i) (copy (!ε) j)
    (forestCurve_disjoint_opposite π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso ε i j)

/-- Each complete coherent sheet has the original retained-prime negative Gram matrix. -/
theorem forestClass_negativeGram_eq (ε : Bool) :
    negativeGram CoverForm (copyClass ε) =
      negativeGram (S.numericalIntersectionBilinForm hmin.regular)
        (fun i => curveClass S hmin.regular (base i)) := by
  ext i j
  change -CoverForm (copyClass ε i) (copyClass ε j) = _
  rw [forestClass_pairing_same π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso hsm ε i j]
  rfl

/-- The actual union of both complete sheets has positive-definite negative Gram. -/
theorem forestClass_sum_negativeGram_posDef :
    (negativeGram CoverForm (Sum.elim (copyClass false) (copyClass true))).PosDef := by
  have hbase := ActualExceptionalNegativeDefinite.negativeGram_posDef π hmin.toIsResolution.over_base hbir
    hmin.regular (baseCurve π N hbir hmin hklt)
    (baseCurve_injective π N hbir hmin hklt) (baseCurve_contracted π N hbir hmin hklt)
  apply KltDP.LinearAlgebra.orthogonal_sum_negativeGram_posDef
    CoverForm (copyClass false) (copyClass true)
  · rw [forestClass_negativeGram_eq π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso hsm false]
    exact hbase
  · rw [forestClass_negativeGram_eq π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso hsm true]
    exact hbase
  · intro i j
    exact forestClass_pairing_opposite π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso hsm false i j
  · intro i j
    exact forestClass_pairing_opposite π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso hsm true i j

/-- The complete Bool by block-component family has positive-definite negative Gram. -/
theorem forestClass_negativeGram_posDef :
    (negativeGram CoverForm (fun i : Bool × Components π N hbir => copyClass i.1 i.2)).PosDef := by
  have h := KltDP.LinearAlgebra.negativeGram_reindex_posDef
    CoverForm (Sum.elim (copyClass false) (copyClass true))
    (forestClass_sum_negativeGram_posDef π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso hsm)
    (Equiv.boolProdEquivSum (Components π N hbir)) (Equiv.boolProdEquivSum _).injective
  have hf : (Sum.elim (copyClass false) (copyClass true) ∘ Equiv.boolProdEquivSum (Components π N hbir)) =
      fun i : Bool × Components π N hbir => copyClass i.1 i.2 := by
    funext i
    rcases i with ⟨ε, D⟩
    cases ε <;> rfl
  rw [hf] at h
  exact h

/-- Every actual lifted prime in the whole doubled forest has an independent numerical class. -/
theorem forestClass_linearIndependent :
    LinearIndependent ℚ (fun i : Bool × Components π N hbir => copyClass i.1 i.2) :=
  KltDP.LinearAlgebra.negativeGram_posDef_linearIndependent CoverForm
    (fun i : Bool × Components π N hbir => copyClass i.1 i.2)
    (forestClass_negativeGram_posDef π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso hsm)

include hsm

/-- All actual primes in the complete doubled forest are distinct. -/
theorem forestCurve_injective : Function.Injective
    (fun i : Bool × Components π N hbir => copy i.1 i.2) := by
  intro i j h
  apply (forestClass_linearIndependent π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso hsm).injective
  exact congrArg (curveClass CoverSurface CoverRegular) h

/-- The unchanged cover has exactly two copies of every original exceptional prime outside N. -/
theorem forestCurve_card (hN : ∀ A ∈ N, IsExceptionalCurve π A) :
    Nat.card (Set.range (fun i : Bool × Components π N hbir => copy i.1 i.2)) =
      2 * (Nat.card (Vertices π) - N.card) := by
  rw [Nat.card_range_of_injective
    (forestCurve_injective π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso hsm), Nat.card_prod,
    card_components π N hbir hiso hN]
  have hBool : Nat.card Bool = 2 := by simp only [Nat.card_eq_fintype_card, Fintype.card_bool]
  rw [hBool]

end KltDP.Geometry.UnbranchedExceptionalBlocks

#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.forestClass_negativeGram_posDef
#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.forestCurve_card

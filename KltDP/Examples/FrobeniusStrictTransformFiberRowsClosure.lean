import KltDP.Geometry.RationalTreePicardPulledFrameCoordinate
import KltDP.Examples.FrobeniusStrictTransformFiberRowsExponents

/-!
# Closing the pullback-compatibility hypothesis (BRIEF18, item 1)

Lane A1's accepted `pullbackGluedClass` (`RationalTreePicardPulledFrameCoordinate`) discharges the
hypothesis `PullbackGluedClass` of `ProjectiveLineCocycleRefinement` — the two statements use the same
pulled-back cocycle (`pullbackGluedClass'`). Hence the exponent of a pulled-back glued line bundle on `P¹`
is unconditionally the Laurent exponent of the refined pulled-back transition unit
(`exponent_pullback_eq_unconditional`, `exponent_pullback_eq_of_monomial_unconditional`), and for the
graph section against the graph ideal line
`exponent ((projectiveGraphMorphism p)^* graphIdealLine q) = overlapExponent (overlapRestriction (graphSectionUnit p q))`
(`exponent_graphSection_graphIdealLine_unconditional`); **`B · b = p`** on `stageSurface (n+1) hproj` now
depends only on the Laurent form `c · T^{−p}` of `graphSectionUnit p 0`
(`graphStrictPairing_secondFiber_of_monomial_unconditional`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusStrictTransformFiberRowsClosure

open KltDP.Geometry KltDP.Geometry.TransitionUnitGluing KltDP.Geometry.ProjectiveLineSheafExponent
open KltDP.Geometry.ProjectiveLineTransitionExtension KltDP.Geometry.ProjectiveLineTransitionExponent
open KltDP.Geometry.ProjectiveLineCocycleRefinement
open FrobeniusGlobalBlowupStages FrobeniusStrictTransformPairing
open FrobeniusStrictTransformFiberRowsExponents FrobeniusGraphClosed FrobeniusProjectiveMorphism
open FrobeniusProjectivePoints FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassTotalTransform

/-- **The pullback compatibility holds** (lane A1's accepted `pullbackGluedClass`). -/
theorem pullbackGluedClass' : PullbackGluedClass.{u} := by
  intro Y X f ι U g hg hU
  exact KltDP.Geometry.RationalTreePicard.pullbackGluedClass f U g hg hU

variable (k : Type u) [Field k]

/-- The exponent of a pulled-back glued line bundle, unconditionally. -/
theorem exponent_pullback_eq_unconditional {X : Scheme.{u}} (K : InvertibleSheaf X) {J : Type u}
    (U : J → X.Opens) (g : ∀ j j' : J, Γ(X, U j ⊓ U j')ˣ) (hg : IsCocycle X U g)
    (hU : (⨆ j, U j) = ⊤) (hK : K.toPic = picardClass X U g hg hU) (s : projectiveSpace k 1 ⟶ X)
    (σ : ULift.{u} (Fin 2) → J) (hσ : ∀ i, standardOpens k i ≤ s ⁻¹ᵁ U (σ i)) :
    exponent k (pullbackInvertibleSheaf s K) =
      cocycleExponent k (refinedUnits (projectiveSpace k 1) (fun j => s ⁻¹ᵁ U j)
        (pullbackUnits s U g) (standardOpens k) σ hσ) :=
  exponent_pullback_eq k pullbackGluedClass' K U g hg hU hK s σ hσ

/-- `exponent_of_frames`, unconditionally. -/
theorem exponent_pullback_eq_of_monomial_unconditional {X : Scheme.{u}} (K : InvertibleSheaf X)
    {J : Type u} (U : J → X.Opens) (g : ∀ j j' : J, Γ(X, U j ⊓ U j')ˣ) (hg : IsCocycle X U g)
    (hU : (⨆ j, U j) = ⊤) (hK : K.toPic = picardClass X U g hg hU) (s : projectiveSpace k 1 ⟶ X)
    (σ : ULift.{u} (Fin 2) → J) (hσ : ∀ i, standardOpens k i ≤ s ⁻¹ᵁ U (σ i)) (c : kˣ) (n : ℤ)
    (h : ((overlapLaurentUnit k (overlapRestriction k (refinedUnits (projectiveSpace k 1)
        (fun j => s ⁻¹ᵁ U j) (pullbackUnits s U g) (standardOpens k) σ hσ ⟨0⟩ ⟨1⟩)) :
          (LaurentPolynomial k)ˣ) : LaurentPolynomial k) =
      LaurentPolynomial.C (c : k) * LaurentPolynomial.T n) :
    exponent k (pullbackInvertibleSheaf s K) = n :=
  exponent_pullback_eq_of_monomial k pullbackGluedClass' K U g hg hU hK s σ hσ c n h

variable {k}

/-- **The exponent of the graph section against the graph ideal line**, unconditionally. -/
theorem exponent_graphSection_graphIdealLine_unconditional (p q : ℕ) :
    exponent k (pullbackInvertibleSheaf (projectiveGraphMorphism (k := k) p) (graphIdealLine q)) =
      overlapExponent k (overlapRestriction k (graphSectionUnit p q)) :=
  exponent_graphSection_graphIdealLine pullbackGluedClass' p q

section Rows

variable [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- **`B · b = p`** on `stageSurface (n+1) hproj`, given only the Laurent form `c · T^{−p}` of the
pulled-back diagonal transition unit `graphSectionUnit p 0`. -/
theorem graphStrictPairing_secondFiber_of_monomial_unconditional (m : ℕ) (c : kˣ)
    (h : ((overlapLaurentUnit k (overlapRestriction k (graphSectionUnit (k := k) (m + (n + 1)) 0)) :
        (LaurentPolynomial k)ˣ) : LaurentPolynomial k) =
      LaurentPolynomial.C (c : k) * LaurentPolynomial.T (-(m + (n + 1) : ℤ))) :
    graphStrictPairing n hproj m (secondFiberTotalClass (n + 1)) = (m + (n + 1) : ℤ) :=
  graphStrictPairing_secondFiber_of_monomial n hproj pullbackGluedClass' m c h

end Rows

end KltDP.Examples.FrobeniusStrictTransformFiberRowsClosure

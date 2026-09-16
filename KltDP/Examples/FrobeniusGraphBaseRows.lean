import KltDP.Geometry.InvertibleSheaf
import KltDP.Geometry.InvertibleSheafPicard
import KltDP.Geometry.SchemeInvertibleSheafPullback
import KltDP.Geometry.PrimeCurveRestrictionDegree
import KltDP.Geometry.NumericalEquivalence
import KltDP.Geometry.ProjectiveLineSheafExponent
import KltDP.Geometry.ProjectiveLineIdealLineDegree
import KltDP.Examples.FrobeniusProjectivePoints
import KltDP.Examples.FrobeniusProjectiveMorphism
import KltDP.Examples.FrobeniusGlobalBlowupStages
import KltDP.Examples.FrobeniusStageZeroProjective
import KltDP.Examples.FrobeniusStrictTransformPairing
import KltDP.Examples.FrobeniusGraphPicardClassFrames
import KltDP.Examples.FrobeniusGraphPicardClassTotalTransform
import KltDP.Examples.FrobeniusGraphPicardClassFiberClasses
import KltDP.Examples.FrobeniusGraphPrimeCurve
import KltDP.Examples.FrobeniusGraphBasePairing

/-!
# The base row of the F29 table: `Γ·a`, `Γ·b`, `Γ·Γ` on `P¹ ×_k P¹`

`FrobeniusGraphPrimeCurve` realises the Frobenius graph as a prime curve `Γ` of the accepted normal
projective surface `projectiveProductSurface = P¹ ×_k P¹`, and `FrobeniusGraphBasePairing` computes
the degree on `Γ` of an invertible sheaf as a transition exponent on `P¹`
(`graphPrimeCurve_restrictionDegree_exponent`). This module reads the *whole base row* of the F29
intersection table off that computation.

The pairing is the accepted `picardRestrictionDegreeHom` of `Γ` (the same construction that defines
the accepted `graphStrictPairing` of `B` and `exceptionalPairing` of `E_n`), so it is additive
without any new degree law:

* `graphBasePairing p : Additive (projectiveProduct k).Pic →+ ℤ`, the pairing `Γ · (−)`;
* `graphBasePairing_ofMul`: on the class of an invertible sheaf `L` it is
  `exponent k ((projectiveGraphMorphism p)^* L)`;
* **`graphBasePairing_firstFiberClass : Γ·a = −exponent ((projectiveGraphMorphism p)^*
  verticalFiberIdealLine)`** and **`graphBasePairing_secondFiberClass : Γ·b = −exponent
  ((projectiveGraphMorphism p)^* graphIdealLine 0)`**, the two ruling rows;
* **`graphBasePairing_graphBaseClass : Γ·Γ = p·(Γ·a) + (Γ·b)`**, unconditionally, from the accepted
  integral relation `inverse_graphIdeal_picard_eq_actual_fibers` (`[Γ] = p·a + b` in `Pic`).

Two consequences worth stating separately:

* **`graphStrictPairing_firstFiber_eq_base`, `graphStrictPairing_secondFiber_eq_base`:** the ruling
  rows of the *strict transform* `B` on `stageSurface (n+1) hproj` are literally the base graph's
  ruling rows, with `p = m + (n + 1)`. Both sides are the same exponent, by the accepted
  `ProjectiveLineIdealLineDegree` rows and the ones proved here; no isomorphism between the two
  curve schemes is used or assumed.
* the conditional values `Γ·a = 1`, `Γ·b = p`, `Γ·Γ = 2p` from the two exponents `−1` and `−p`.

**Deliberately not proved here.** The two exponents themselves. They are exactly the two open
quantities of the accepted `ProjectiveLineIdealLineDegree` (`B·a`, `B·b`); the `graphIdealLine 0`
one is reduced, unconditionally, by the accepted
`FrobeniusStrictTransformFiberRowsClosure.exponent_graphSection_graphIdealLine_unconditional` to
the Laurent form of the pulled-back diagonal transition unit `graphSectionUnit p 0`, and the
`verticalFiberIdealLine` one additionally needs a swap-compatible atlas. Nothing here assumes a
value for either, and no numerical row is claimed unconditionally beyond `Γ·Γ = p·(Γ·a) + (Γ·b)`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusGraphBaseRows

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.ProjectiveLineSheafExponent
open KltDP.Geometry.ProjectiveLineIdealLineDegree
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGlobalBlowupStages FrobeniusStageZeroProjective
open FrobeniusStrictTransformPairing
open FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassTotalTransform
open FrobeniusGraphPicardClassFiberClasses
open FrobeniusGraphPrimeCurve FrobeniusGraphBasePairing

variable {k : Type u} [Field k]

/-- The divisor class of the graph `Γ = {y = x^p}` itself on `P¹ ×_k P¹`, as the inverse of the
class of its ideal line — the same convention as the accepted `firstFiberClass`,
`secondFiberClass`. -/
def graphBaseClass (p : ℕ) : Additive (projectiveProduct k).Pic :=
  -Additive.ofMul (graphIdealLine (k := k) p).toPic

section Base

variable [IsAlgClosed k]

/-- **The pairing `Γ · (−)`** of the base graph against the Picard classes of `P¹ ×_k P¹`, as the
accepted restriction-degree homomorphism of the prime curve `Γ`. -/
abbrev graphBasePairing (p : ℕ) : Additive (projectiveProduct k).Pic →+ ℤ :=
  (projectiveProductSurface (k := k)).picardRestrictionDegreeHom (graphPrimeCurve p)

/-- On the class of an invertible sheaf the pairing is the transition exponent of the pullback
along the accepted global graph morphism. -/
theorem graphBasePairing_ofMul (p : ℕ) (L : InvertibleSheaf (projectiveProduct k)) :
    graphBasePairing (k := k) p (Additive.ofMul L.toPic) =
      exponent k (pullbackInvertibleSheaf (projectiveGraphMorphism (k := k) p) L) := by
  show (graphPrimeCurve (k := k) p).picardRestrictionDegree L.toPic = _
  rw [PrimeCurve.picardRestrictionDegree_toPic]
  exact graphPrimeCurve_restrictionDegree_exponent p L

/-- **`Γ · a = −exponent ((projectiveGraphMorphism p)^* verticalFiberIdealLine)`.** -/
theorem graphBasePairing_firstFiberClass (p : ℕ) :
    graphBasePairing (k := k) p firstFiberClass =
      -exponent k (pullbackInvertibleSheaf (projectiveGraphMorphism (k := k) p)
        (verticalFiberIdealLine (k := k))) := by
  simp only [firstFiberClass, map_neg]
  rw [graphBasePairing_ofMul]

/-- **`Γ · b = −exponent ((projectiveGraphMorphism p)^* graphIdealLine 0)`.** -/
theorem graphBasePairing_secondFiberClass (p : ℕ) :
    graphBasePairing (k := k) p secondFiberClass =
      -exponent k (pullbackInvertibleSheaf (projectiveGraphMorphism (k := k) p)
        (graphIdealLine (k := k) 0)) := by
  simp only [secondFiberClass, map_neg]
  rw [graphBasePairing_ofMul]

/-- **`Γ · Γ = p · (Γ · a) + (Γ · b)`**, from the accepted integral relation `[Γ] = p·a + b`. -/
theorem graphBasePairing_graphBaseClass (p : ℕ) :
    graphBasePairing (k := k) p (graphBaseClass p) =
      (p : ℤ) * graphBasePairing (k := k) p (firstFiberClass (k := k)) +
        graphBasePairing (k := k) p (secondFiberClass (k := k)) := by
  simp only [graphBaseClass]
  rw [inverse_graphIdeal_picard_eq_actual_fibers, map_add, map_nsmul, nsmul_eq_mul]

/-! ### The strict transform's ruling rows are the base graph's ruling rows -/

section Rows

variable (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- **`B · a = Γ · a`** with `p = m + (n + 1)`: both are the same transition exponent on `P¹`. -/
theorem graphStrictPairing_firstFiber_eq_base (m : ℕ) :
    graphStrictPairing n hproj m (firstFiberTotalClass (n + 1)) =
      graphBasePairing (k := k) (m + (n + 1)) firstFiberClass := by
  rw [graphStrictPairing_firstFiber_exponent, graphBasePairing_firstFiberClass]

/-- **`B · b = Γ · b`** with `p = m + (n + 1)`: both are the same transition exponent on `P¹`. -/
theorem graphStrictPairing_secondFiber_eq_base (m : ℕ) :
    graphStrictPairing n hproj m (secondFiberTotalClass (n + 1)) =
      graphBasePairing (k := k) (m + (n + 1)) secondFiberClass := by
  rw [graphStrictPairing_secondFiber_exponent, graphBasePairing_secondFiberClass]

end Rows

/-! ### The numerical rows, from the two exponents -/

/-- **`Γ · a = 1`**, given the exponent `−1`. -/
theorem graphBasePairing_firstFiberClass_of_exponent (p : ℕ)
    (h : exponent k (pullbackInvertibleSheaf (projectiveGraphMorphism (k := k) p)
      (verticalFiberIdealLine (k := k))) = -1) :
    graphBasePairing (k := k) p firstFiberClass = 1 := by
  rw [graphBasePairing_firstFiberClass, h, neg_neg]

/-- **`Γ · b = p`**, given the exponent `−p`. -/
theorem graphBasePairing_secondFiberClass_of_exponent (p : ℕ)
    (h : exponent k (pullbackInvertibleSheaf (projectiveGraphMorphism (k := k) p)
      (graphIdealLine (k := k) 0)) = -(p : ℤ)) :
    graphBasePairing (k := k) p secondFiberClass = (p : ℤ) := by
  rw [graphBasePairing_secondFiberClass, h, neg_neg]

/-- **`Γ · Γ = 2p`**, given both exponents. -/
theorem graphBasePairing_graphBaseClass_of_exponents (p : ℕ)
    (ha : exponent k (pullbackInvertibleSheaf (projectiveGraphMorphism (k := k) p)
      (verticalFiberIdealLine (k := k))) = -1)
    (hb : exponent k (pullbackInvertibleSheaf (projectiveGraphMorphism (k := k) p)
      (graphIdealLine (k := k) 0)) = -(p : ℤ)) :
    graphBasePairing (k := k) p (graphBaseClass p) = 2 * (p : ℤ) := by
  rw [graphBasePairing_graphBaseClass, graphBasePairing_firstFiberClass_of_exponent p ha,
    graphBasePairing_secondFiberClass_of_exponent p hb]
  ring

end Base

end KltDP.Examples.FrobeniusGraphBaseRows

namespace KltDP.Examples

open KltDP.Geometry KltDP.Geometry.ProjectiveLineSheafExponent
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassFiberClasses
open FrobeniusGraphBaseRows

/-- **The base row of the F29 intersection table on `P¹ ×_k P¹`.** The pairing of the graph prime
curve `Γ` against the two ruling classes is the negated transition exponent of the corresponding
ideal line pulled back along the accepted global graph morphism, and the self-pairing `Γ·Γ` is
`p·(Γ·a) + (Γ·b)`. -/
theorem f29_graph_base_rows (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) :
    graphBasePairing (k := k) p firstFiberClass =
        -exponent k (pullbackInvertibleSheaf (projectiveGraphMorphism (k := k) p)
          (verticalFiberIdealLine (k := k))) ∧
      graphBasePairing (k := k) p secondFiberClass =
        -exponent k (pullbackInvertibleSheaf (projectiveGraphMorphism (k := k) p)
          (graphIdealLine (k := k) 0)) ∧
      graphBasePairing (k := k) p (graphBaseClass p) =
        (p : ℤ) * graphBasePairing (k := k) p (firstFiberClass (k := k)) +
          graphBasePairing (k := k) p (secondFiberClass (k := k)) :=
  ⟨graphBasePairing_firstFiberClass p, graphBasePairing_secondFiberClass p,
    graphBasePairing_graphBaseClass p⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_graph_base_rows_universe_check (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) :
    True := by
  have _ := f29_graph_base_rows.{u} k p
  trivial

end KltDP.Examples

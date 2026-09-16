import KltDP.Geometry.InvertibleSheaf
import KltDP.Geometry.SchemeInvertibleSheafPullback
import KltDP.Geometry.SchemePicardPullback
import KltDP.Geometry.PrimeCurveRestrictionDegree
import KltDP.Geometry.PrimeCurveDegreeTransport
import KltDP.Geometry.ProjectiveLineSheafExponent
import KltDP.Geometry.ProjectiveLineIdealLineDegree
import KltDP.Examples.FrobeniusGlobalBlowupStages
import KltDP.Examples.FrobeniusProjectivePoints
import KltDP.Examples.FrobeniusProjectiveMorphism
import KltDP.Examples.FrobeniusStrictTransformPairing
import KltDP.Examples.FrobeniusStrictTransformFiberRows
import KltDP.Examples.FrobeniusGraphPrimeCurve

/-!
# `B · π^*q = Γ · q`: the strict transform pairs with pulled-back classes exactly as the base graph

`FrobeniusGraphPrimeCurve.graphPrimeCurve_picardRestrictionDegree` computes the degree of a Picard
class `q` of `P¹ ×_k P¹` on the base graph `Γ` as the Euler degree on `P¹` of `q` pulled back along
the accepted `projectiveGraphMorphism p`. The accepted
`FrobeniusStrictTransformFiberRows.graphStrictPairing_pullback` computes the pairing of the *strict
transform* `B` on `stageSurface (n+1) hproj` with `π^*q` as the Euler degree of the very same
pullback, relative to `graphSectionBase (m + (n+1))`; and the accepted
`ProjectiveLineIdealLineDegree.graphSectionBase_eq` identifies that base with
`projectiveSpaceToSpec k 1`. The two right-hand sides are therefore literally the same integer, so

  **`graphStrictPairing_eq_graphPrimeCurve : B · π^*q = Γ · q`**   (`p = m + (n + 1)`).

**Why this matters.** The route previously recorded for `B · π^*Γ` went through a curve-level
transport (`PrimeCurveTransportPullback.picardRestrictionDegree_eq_of_isoFactor`) whose input is an
isomorphism `φ : B.toScheme ≅ Γ.toScheme` with `B.inclusion ≫ π = φ ≫ Γ.inclusion` — i.e. the
global isomorphism `graph p ≅ strictTransform n p`, which the accepted tree does not have
(`FrobeniusGlobalStrictTransform.wholeGraphToStrictTransform` is defined on the *punctured* graph
only, and `FrobeniusStrictImageIso.graphRestrictIso` is a base change over the isomorphism open).
**That transport is not needed for this statement**: both sides were already reduced, in accepted
work, to the same Euler degree along the same morphism `projectiveGraphMorphism p`. No isomorphism
between the two curve schemes is constructed or assumed here.

Also `graphPrimeCurve_restrictionDegree_exponent`, the invertible-sheaf form of the base degree as a
`P¹` transition exponent, matching the shape in which
`ProjectiveLineIdealLineDegree` states the `B · a`, `B · b` rows.

**Deliberately not proved here.** No numerical value: `Γ·a`, `Γ·b`, `Γ·Γ`, `B·B` are not claimed.
Getting from these Picard-class degrees to `intersectionNumber` against a *Cartier divisor* `π^*D`
additionally needs `CartierPullbackComparison.cartierPicardHom_pullbackDivisor_eq`, which is queued
and not certified; this module's dependencies are entirely accepted apart from
`FrobeniusGraphPrimeCurve`, which sits beside it in the same lane round.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusGraphBasePairing

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.ProjectiveLineSheafExponent KltDP.Geometry.ProjectiveLineIdealLineDegree
open FrobeniusGlobalBlowupStages FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusStrictTransformPairing FrobeniusStrictTransformFiberRows
open FrobeniusGraphPrimeCurve

variable {k : Type u} [Field k]

section Base

variable [IsAlgClosed k]

/-- **The base degree as a `P¹` transition exponent**: the degree on `Γ` of an invertible sheaf of
the product is the exponent of its pullback along the accepted global graph morphism. -/
theorem graphPrimeCurve_restrictionDegree_exponent (p : ℕ)
    (L : InvertibleSheaf (projectiveProduct k)) :
    (graphPrimeCurve (k := k) p).restrictionDegree L =
      exponent k (pullbackInvertibleSheaf (projectiveGraphMorphism (k := k) p) L) := by
  have h := graphPrimeCurve_picardRestrictionDegree (k := k) p L.toPic
  rw [PrimeCurve.picardRestrictionDegree_toPic, schemePicardPullbackHom_toPic,
    eulerDegree_toPic_eq_exponent] at h
  exact h

end Base

section Rows

variable [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- **`B · π^*q = Γ · q`**: the pairing of the strict transform `B` on `stageSurface (n+1) hproj`
with a class pulled back from the product equals the degree of that class on the base graph `Γ`.
No isomorphism between the two curve schemes is used: both sides are the same Euler degree on `P¹`
of the pullback along `projectiveGraphMorphism (m + (n + 1))`. -/
theorem graphStrictPairing_eq_graphPrimeCurve (m : ℕ) (q : (projectiveProduct k).Pic) :
    graphStrictPairing n hproj m
        ((schemePicardPullbackHom (projectiveContactProjection (n + 1))).toAdditive
          (Additive.ofMul q)) =
      (graphPrimeCurve (k := k) (m + (n + 1))).picardRestrictionDegree q := by
  rw [graphStrictPairing_pullback, graphSectionBase_eq, graphPrimeCurve_picardRestrictionDegree]
  all_goals rfl

end Rows

end KltDP.Examples.FrobeniusGraphBasePairing

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusProjectivePoints
open FrobeniusStrictTransformPairing FrobeniusGraphPrimeCurve FrobeniusGraphBasePairing

/-- **The strict transform of the graph pairs with pulled-back classes exactly as the base graph
does.** For every Picard class `q` of `P¹ ×_k P¹`, the pairing `B · π^*q` on `stageSurface (n+1)`
equals the degree of `q` on the prime curve `Γ ⊆ P¹ ×_k P¹`. -/
theorem f29_graph_base_pairing (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap) (m : ℕ)
    (q : (projectiveProduct k).Pic) :
    graphStrictPairing n hproj m
        ((schemePicardPullbackHom (projectiveContactProjection (n + 1))).toAdditive
          (Additive.ofMul q)) =
      (graphPrimeCurve (k := k) (m + (n + 1))).picardRestrictionDegree q :=
  graphStrictPairing_eq_graphPrimeCurve n hproj m q

/-- The bundle has exactly one universe parameter. -/
theorem f29_graph_base_pairing_universe_check (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap) (m : ℕ)
    (q : (projectiveProduct k).Pic) : True := by
  have _ := f29_graph_base_pairing.{u} k n hproj m q
  trivial

end KltDP.Examples

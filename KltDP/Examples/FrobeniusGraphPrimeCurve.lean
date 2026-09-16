import KltDP.Geometry.PrimeCurveOfClosedImmersion
import KltDP.Geometry.PrimeCurveInclusionLift
import KltDP.Geometry.PrimeCurveSubscheme
import KltDP.Geometry.PrimeCurveLineDegree
import KltDP.Geometry.PrimeCurveRestrictionDegree
import KltDP.Geometry.PrimeCurveDegreeTransport
import KltDP.Geometry.SchemePicardPullback
import KltDP.Geometry.SheafPicard
import KltDP.Geometry.Surface
import KltDP.Examples.FrobeniusProjectivePoints
import KltDP.Examples.FrobeniusProjectiveMorphism
import KltDP.Examples.FrobeniusGraphClosed
import KltDP.Examples.FrobeniusStageZeroProjective

/-!
# The Frobenius graph `Γ` as a prime curve of `P¹ ×_k P¹`

The accepted tree realises the strict transforms `B`, `F̃` and the exceptional curves `C_j`, `P` as
`PrimeCurve`s of the blown-up stages, but never realises the *base* curve: the Frobenius graph
`Γ = {y = x^p} ⊆ P¹ ×_k P¹` itself. This module supplies it, so that the intersection numbers
`Γ·Γ`, `Γ·a`, `Γ·b` on the product become stateable, and so that the curve-level transport of
`PrimeCurveTransportPullback` has a target curve `C` to transport onto.

Everything here is assembled from accepted inputs, with no new geometry:

* `graphPrimeCurve p` is `PrimeCurveOfClosedImmersion.primeCurveOfIsoProjectiveLine` applied to the
  accepted normal projective surface `projectiveProductSurface` (stage `0` of the origin contact
  tower, which needs no `hproj`), the accepted closed immersion `graphι p` and the accepted
  isomorphism `graphIsoProjectiveLine p : graph p ≅ P¹`;
* `graphPrimeCurveLift p` identifies the accepted equalizer scheme `graph p` with the prime curve's
  own glued scheme `(graphPrimeCurve p).toScheme`, through the generic
  `PrimeCurveInclusionLift.lift`; the graph is reduced because it is integral
  (`isIntegral_of_iso_projectiveLine`);
* `graphPrimeCurveIsoProjectiveLine p : (graphPrimeCurve p).toScheme ≅ P¹` is the composite, and
  `graphPrimeCurveIsoProjectiveLine_toSpec` says it is an isomorphism **over `k`**, which is the
  hypothesis `hφ` that both `PrimeCurveDegreeTransport.picardDegree_pullback_iso` and the queued
  `PrimeCurveTransportPullback.picardRestrictionDegree_eq_of_isoFactor` consume;
* `graphPrimeCurve_inclusion_eq` factors the prime-curve inclusion as that isomorphism followed by
  the accepted global graph morphism `projectiveGraphMorphism p : P¹ ⟶ P¹ ×_k P¹`;
* consequently `graphPrimeCurve_picardRestrictionDegree` computes every degree `Γ · q` of a Picard
  class `q` of the product as the Euler degree on `P¹` of its pullback along
  `projectiveGraphMorphism p`. This is the engine for the base row of the F29 intersection table.

**Deliberately not proved here.** The numerical values `Γ·a = 1`, `Γ·b = p`, `Γ·Γ = 2p` are not
claimed: they need the Euler degrees on `P¹` of the pulled-back ruling classes, which is separate
work. Nothing here touches the strict transform `B` on a blown-up stage, and in particular the
global isomorphism `graph p ≅ strictTransform n p` — the one remaining gap on the `B·π^*Γ` route —
is neither built nor assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusGraphPrimeCurve

open KltDP.Geometry KltDP.Geometry.PrimeCurveOfClosedImmersion
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusGraphClosed
open FrobeniusStageZeroProjective

variable {k : Type u} [Field k]

-- The equalizer graph is integral, hence reduced: it is isomorphic to the projective line by the
-- accepted `graphIsoProjectiveLine`.  Needed to lift `graphι` through the prime-curve inclusion.
local instance graphScheme_isIntegral (p : ℕ) : IsIntegral (graph (k := k) p) :=
  isIntegral_of_iso_projectiveLine (graphIsoProjectiveLine p)

/-- Reading the product's structure morphism along the graph through the first projection: both
sides are `graphι p ≫ pullback.fst ≫ projectiveSpaceToSpec k 1`. -/
theorem graphToLine_toSpec (p : ℕ) :
    graphToLine (k := k) p ≫ projectiveSpaceToSpec k 1 =
      graphι p ≫ projectiveProductToSpec (k := k) :=
  Category.assoc (graphι (k := k) p) firstProjection (projectiveSpaceToSpec k 1)

/-- The first projection restricted to the graph is a section of the accepted global graph
morphism, so composing them recovers the graph's inclusion. -/
theorem graphToLine_projectiveGraphMorphism (p : ℕ) :
    graphToLine (k := k) p ≫ projectiveGraphMorphism p = graphι p := by
  rw [← lineToGraph_ι p, ← Category.assoc, graphToLine_lineToGraph, Category.id_comp]

section Surface

variable [IsAlgClosed k]

/-- **The Frobenius graph `Γ = {y = x^p}` as a prime curve of `P¹ ×_k P¹`.** -/
def graphPrimeCurve (p : ℕ) : (projectiveProductSurface (k := k)).PrimeCurve :=
  primeCurveOfIsoProjectiveLine projectiveProductSurface (graphι p) (graphIsoProjectiveLine p)

@[simp] theorem coe_graphPrimeCurve (p : ℕ) :
    (graphPrimeCurve (k := k) p : Set (projectiveProductSurface (k := k)).toScheme) =
      Set.range (graphι (k := k) p).base := rfl

/-- The accepted equalizer scheme maps to the prime curve's own glued scheme. -/
def graphPrimeCurveLift (p : ℕ) :
    graph (k := k) p ⟶ (graphPrimeCurve (k := k) p).toScheme :=
  PrimeCurveInclusionLift.lift (graphPrimeCurve (k := k) p) (graphι p) (coe_graphPrimeCurve p)

instance graphPrimeCurveLift_isIso (p : ℕ) : IsIso (graphPrimeCurveLift (k := k) p) :=
  PrimeCurveInclusionLift.lift_isIso (graphPrimeCurve (k := k) p) (graphι p)
    (coe_graphPrimeCurve p)

@[reassoc] theorem graphPrimeCurveLift_inclusion (p : ℕ) :
    graphPrimeCurveLift (k := k) p ≫ (graphPrimeCurve (k := k) p).inclusion = graphι p :=
  PrimeCurveInclusionLift.lift_inclusion (graphPrimeCurve (k := k) p) (graphι p)
    (coe_graphPrimeCurve p)

/-- The prime-curve inclusion is the accepted closed immersion, transported. -/
theorem graphPrimeCurve_inclusion (p : ℕ) :
    (graphPrimeCurve (k := k) p).inclusion =
      inv (graphPrimeCurveLift (k := k) p) ≫ graphι p :=
  PrimeCurveInclusionLift.inclusion_eq_inv_lift (graphPrimeCurve (k := k) p) (graphι p)
    (coe_graphPrimeCurve p)

/-- The curve's structure morphism is its inclusion followed by the product's own structure
morphism; the surface `projectiveProductSurface` carries `projectiveProductToSpec` on the nose. -/
theorem graphPrimeCurve_toSpec (p : ℕ) :
    (graphPrimeCurve (k := k) p).toSpec =
      (graphPrimeCurve (k := k) p).inclusion ≫ projectiveProductToSpec (k := k) := rfl

/-- **`Γ ≅ P¹`.** -/
def graphPrimeCurveIsoProjectiveLine (p : ℕ) :
    (graphPrimeCurve (k := k) p).toScheme ≅ projectiveSpace k 1 :=
  (asIso (graphPrimeCurveLift (k := k) p)).symm ≪≫ graphIsoProjectiveLine p

theorem graphPrimeCurveIsoProjectiveLine_hom (p : ℕ) :
    (graphPrimeCurveIsoProjectiveLine (k := k) p).hom =
      inv (graphPrimeCurveLift (k := k) p) ≫ graphToLine p := rfl

/-- **The isomorphism `Γ ≅ P¹` is an isomorphism over `k`.** This is the hypothesis `hφ` consumed
by `PrimeCurveDegreeTransport.picardDegree_pullback_iso` and by the curve-level transport. -/
theorem graphPrimeCurveIsoProjectiveLine_toSpec (p : ℕ) :
    (graphPrimeCurveIsoProjectiveLine (k := k) p).hom ≫ projectiveSpaceToSpec k 1 =
      (graphPrimeCurve (k := k) p).toSpec := by
  simp only [graphPrimeCurveIsoProjectiveLine_hom, graphPrimeCurve_toSpec,
    graphPrimeCurve_inclusion, Category.assoc, graphToLine_toSpec]

/-- **The inclusion of `Γ` factors through `P¹` as the accepted global graph morphism.** -/
theorem graphPrimeCurve_inclusion_eq (p : ℕ) :
    (graphPrimeCurve (k := k) p).inclusion =
      (graphPrimeCurveIsoProjectiveLine (k := k) p).hom ≫ projectiveGraphMorphism p := by
  rw [graphPrimeCurveIsoProjectiveLine_hom, Category.assoc,
    graphToLine_projectiveGraphMorphism, graphPrimeCurve_inclusion]

theorem graphPrimeCurve_picardRestrictionDegree_eq (p : ℕ) (q : (projectiveProduct k).Pic) :
    (graphPrimeCurve (k := k) p).picardRestrictionDegree q =
      (graphPrimeCurve (k := k) p).picardDegree
        (schemePicardPullbackHom (graphPrimeCurve (k := k) p).inclusion q) := rfl

/-- **Every degree `Γ · q` on `P¹ ×_k P¹` is an Euler degree on `P¹`**, namely that of the pullback
of `q` along the accepted global graph morphism. -/
theorem graphPrimeCurve_picardRestrictionDegree (p : ℕ) (q : (projectiveProduct k).Pic) :
    (graphPrimeCurve (k := k) p).picardRestrictionDegree q =
      PrimeCurveDegreeTransport.eulerDegree (projectiveSpaceToSpec k 1)
        (schemePicardPullbackHom (projectiveGraphMorphism (k := k) p) q) := by
  rw [graphPrimeCurve_picardRestrictionDegree_eq, graphPrimeCurve_inclusion_eq,
    schemePicardPullbackHom_comp]
  all_goals
    exact PrimeCurveDegreeTransport.picardDegree_pullback_iso
      (graphPrimeCurve (k := k) p) (graphPrimeCurveIsoProjectiveLine (k := k) p).hom
      (projectiveSpaceToSpec k 1) (graphPrimeCurveIsoProjectiveLine_toSpec p)
      (schemePicardPullbackHom (projectiveGraphMorphism (k := k) p) q)

end Surface

end KltDP.Examples.FrobeniusGraphPrimeCurve

namespace KltDP.Examples

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGraphClosed FrobeniusStageZeroProjective FrobeniusGraphPrimeCurve

/-- **The Frobenius graph is a prime curve of `P¹ ×_k P¹`, isomorphic to `P¹` over `k`, whose
inclusion is the accepted global graph morphism read through that isomorphism.** -/
theorem f29_graph_prime_curve (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) :
    ∃ C : (projectiveProductSurface (k := k)).PrimeCurve,
      (C : Set (projectiveProductSurface (k := k)).toScheme) =
          Set.range (graphι (k := k) p).base ∧
        ∃ e : C.toScheme ≅ projectiveSpace k 1,
          e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec ∧
            C.inclusion = e.hom ≫ projectiveGraphMorphism p :=
  ⟨graphPrimeCurve (k := k) p, rfl, graphPrimeCurveIsoProjectiveLine (k := k) p,
    graphPrimeCurveIsoProjectiveLine_toSpec p, graphPrimeCurve_inclusion_eq p⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_graph_prime_curve_universe_check (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) :
    True := by
  have _ := f29_graph_prime_curve.{u} k p
  trivial

end KltDP.Examples

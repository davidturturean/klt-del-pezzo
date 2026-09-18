import KltDP.Geometry.SurfaceNakaiMoishezonSource

/-!
# Hartshorne V Theorem 1.10, complete surface Nakai--Moishezon criterion

Robin Hartshorne, Algebraic Geometry, GTM52 (1977), printed page365.
DOI: 10.1007/978-1-4757-3849-0.
Frozen primary PDF SHA256:
55cee9c730cfb03ed9ecac25444c87579fe411077ddb14bc4b31c98cc3be2d5e.

The entire iff is retained on every original Weil divisor and every actual
prime curve. All regular integral projective dimension-two surfaces over
algebraically closed fields are included, in arbitrary characteristic.
Individually approved only for this isolated candidate; see the root decision
and independent source/object review in hartshorne_nakai_admission.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.SurfaceRiemannRochSource
open KltDP.Geometry.SurfaceHodgeIndexSource

universe u

namespace KltDP.Literature.Hartshorne

/-- The published complete surface numerical ampleness criterion. -/
axiom surface_nakai_moishezon_literal :
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of k))
    (hIntegral : IsIntegral Y) (hprojective : IsProjectiveOverField f)
    (hdimension : topologicalKrullDim Y = 2)
    (hregular : ∀ y : Y, RegularPoint Y y),
    let X := sourceSurface Y f hIntegral hprojective hdimension hregular
    ∀ D : X.WeilDivisor,
      AmpleSerre.IsAmple (divisorLine X hregular D) ↔
        0 < divisorPairing X hregular D D ∧
          ∀ C : X.PrimeCurve, 0 < divisorPairing X hregular D (Finsupp.single C 1)

end KltDP.Literature.Hartshorne

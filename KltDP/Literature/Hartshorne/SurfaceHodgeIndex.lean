import KltDP.Geometry.SurfaceHodgeIndexSource

/-!
# Hartshorne V Theorem 1.9: the full strict integral Hodge-index theorem

Robin Hartshorne, Algebraic Geometry, GTM52, Springer, first edition 1977
(softcover reprint), printed p.364; DOI 10.1007/978-1-4757-3849-0.
Full source SHA256: 55cee9c730cfb03ed9ecac25444c87579fe411077ddb14bc4b31c98cc3be2d5e.

The exact published theorem retains every original integral Weil divisor,
actual ample H, the all-divisor numerical test, and strict negativity.
Root's isolated admission decision and source/object/consumer review are in
hartshorne_hodge_admission/ROOT_CANDIDATE_ADMISSION_DECISION.json.
This literal is not part of the accepted production checkpoint.
-/

universe u

namespace KltDP.Literature.Hartshorne

open AlgebraicGeometry CategoryTheory TopologicalSpace KltDP.Geometry
open KltDP.Geometry.SurfaceRiemannRochSource
open KltDP.Geometry.SurfaceHodgeIndexSource

axiom surface_hodge_index_literal :
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of k))
    (hIntegral : IsIntegral Y) (hprojective : IsProjectiveOverField f)
    (hdimension : topologicalKrullDim Y = 2)
    (hregular : ∀ y : Y, RegularPoint Y y),
    let X := sourceSurface Y f hIntegral hprojective hdimension hregular
    ∀ H D : X.WeilDivisor,
      AmpleSerre.IsAmple (divisorLine X hregular H) →
      (¬ ∀ E : X.WeilDivisor, divisorPairing X hregular D E = 0) →
      divisorPairing X hregular D H = 0 →
      divisorPairing X hregular D D < 0

end KltDP.Literature.Hartshorne

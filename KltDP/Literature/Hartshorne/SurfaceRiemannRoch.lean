import KltDP.Geometry.SurfaceRiemannRochSource

/-!
# Hartshorne V Theorem 1.6, the full surface Riemann--Roch formula

Algebraic Geometry, GTM52, Springer, first edition1977 (softcover reprint),
printed p.362; DOI10.1007/978-1-4757-3849-0. Complete source SHA256:
55cee9c730cfb03ed9ecac25444c87579fe411077ddb14bc4b31c98cc3be2d5e.

All original source hypotheses and arbitrary divisors are retained. The
preceding source definitions of l, s and arithmetic genus are unfolded via
independently defined scalar cohomology and the actual Euler characteristic.
The isolated literal decision and exact object/consumer evidence are in
hartshorne_rr_admission/ROOT_CANDIDATE_ADMISSION_DECISION.json.
This is not yet part of the accepted production checkpoint.
-/

universe u

namespace KltDP.Literature.Hartshorne

open AlgebraicGeometry CategoryTheory TopologicalSpace KltDP.Geometry
open KltDP.Geometry.SurfaceRiemannRochSource

axiom surface_riemannRoch_literal :
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of k))
    (hIntegral : IsIntegral Y) (hprojective : IsProjectiveOverField f)
    (hdimension : topologicalKrullDim Y = 2)
    (hregular : ∀ y : Y, RegularPoint Y y),
    let X := sourceSurface Y f hIntegral hprojective hdimension hregular
    ∀ D K : X.WeilDivisor, IsCanonical X hregular K →
      (hDimension X hregular D 0 : ℚ) - (hDimension X hregular D 1 : ℚ) +
        (hDimension X hregular (K - D) 0 : ℚ) = rrNumber X hregular D K

end KltDP.Literature.Hartshorne

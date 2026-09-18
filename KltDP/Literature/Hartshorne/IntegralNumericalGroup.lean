import KltDP.Geometry.SurfaceNumericalFinitenessSource

/-!
# Hartshorne V Remark 1.9.1: the complete integral Num assertion

Robin Hartshorne, Algebraic Geometry, GTM52, Springer, first edition 1977
(softcover reprint), printed p.364; DOI 10.1007/978-1-4757-3849-0.
Full source SHA256: 55cee9c730cfb03ed9ecac25444c87579fe411077ddb14bc4b31c98cc3be2d5e.

This is the complete independent assertion that integral Num is free and
finitely generated. Both conclusions are retained on the original quotient.
It is not a substitute for the full algebraic-equivalence Neron-Severi theorem.
The exact assertion boundary, definitions and isolated root decision are in
hartshorne_numerical_finiteness_admission/ROOT_CANDIDATE_ADMISSION_DECISION.json.
The literal is not part of the accepted production checkpoint.
-/

universe u

namespace KltDP.Literature.Hartshorne

open AlgebraicGeometry CategoryTheory TopologicalSpace KltDP.Geometry
open KltDP.Geometry.NormalProjectiveSurface KltDP.Geometry.SurfaceRiemannRochSource

axiom integral_numerical_group_free_finite_literal :
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of k))
    (hIntegral : IsIntegral Y) (hprojective : IsProjectiveOverField f)
    (hdimension : topologicalKrullDim Y = 2)
    (hregular : ∀ y : Y, RegularPoint Y y),
    let X := sourceSurface Y f hIntegral hprojective hdimension hregular
    Module.Free ℤ X.IntegralNumericalClassGroup ∧
      Module.Finite ℤ X.IntegralNumericalClassGroup

end KltDP.Literature.Hartshorne

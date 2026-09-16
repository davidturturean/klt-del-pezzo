import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Limits

/-!
# Affine intersections on an actual separated scheme

The diagonal of a separated scheme makes the comparison from a fiber
product over that scheme to the fiber product over the terminal scheme a
closed immersion. When the two factors are affine, the target is affine,
so the source is affine. The actual open-intersection pullback then gives
pair and triple intersection affineness.

Reuse: pinned Mathlib supplies `pullback.mapDesc` and its closed-immersion
instance in `AlgebraicGeometry/Morphisms/Separated.lean:100`, affine
pullbacks in `AlgebraicGeometry/Pullbacks.lean:452`, and the actual
`isPullback_opens_inf` in `AlgebraicGeometry/Restrict.lean:472`.
Official Mathlib revision 80cbd0498ab39e21d24d6730b3f932cec672a702,
`AlgebraicGeometry/Morphisms/Separated.lean:114-117`, retains the same
closed-immersion comparison (Apache 2.0; Lean 4.34.0-rc2). Its separated
and affine-scheme files were also inspected for a direct intersection
adapter. This file uses the pinned proofs without importing or copying
newer code. The only local addition is the affine-pullback/intersection
composition; no intersection-affineness conclusion is an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.SeparatedAffineIntersections

/-- Two affine schemes have affine fiber product over an actual separated scheme. -/
theorem isAffine_pullback {A B X : Scheme.{u}} [IsAffine A] [IsAffine B]
    [X.IsSeparated] (f : A ⟶ X) (g : B ⟶ X) : IsAffine (pullback f g) := by
  haveI : IsAffine (pullback (f ≫ terminal.from X) (g ≫ terminal.from X)) :=
    inferInstance
  haveI : IsClosedImmersion (pullback.mapDesc f g (terminal.from X)) := inferInstance
  exact isAffine_of_isAffineHom (pullback.mapDesc f g (terminal.from X))

/-- The actual intersection of affine opens in a separated scheme is affine. -/
theorem isAffineOpen_inf {X : Scheme.{u}} [X.IsSeparated] {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) := by
  letI : IsAffine U.toScheme := hU
  letI : IsAffine V.toScheme := hV
  haveI : IsAffine (pullback U.ι V.ι) := isAffine_pullback U.ι V.ι
  change IsAffine (U ⊓ V).toScheme
  exact IsAffine.of_isIso (isPullback_opens_inf U V).isoPullback.hom

/-- Actual triple intersections are affine with the atlas's left-associated convention. -/
theorem isAffineOpen_inf_inf {X : Scheme.{u}} [X.IsSeparated] {U V W : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    IsAffineOpen ((U ⊓ V) ⊓ W) :=
  isAffineOpen_inf (isAffineOpen_inf hU hV) hW

end KltDP.Geometry.SeparatedAffineIntersections

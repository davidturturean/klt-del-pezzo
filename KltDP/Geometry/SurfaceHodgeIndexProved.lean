import KltDP.Literature.Hartshorne.SurfaceHodgeIndex

/-!
# Original surface consequences of the full Hodge-index source

The source adapters preserve the original Weil, Cartier and Picard objects.
An ample sheaf is constructed from the original projective embedding; its
positive square is proved from actual effective divisors and curve degrees.
The final existential Hodge statement has no supplied polarization or Hodge
hypothesis. Finite dimensionality is a separate obligation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface

universe u

namespace KltDP.Geometry.SurfaceHodgeIndexProved

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- The admitted literal has exactly the separately compiled raw statement. -/
theorem published : SurfaceHodgeIndexSource.RawStatement.{u} :=
  KltDP.Literature.Hartshorne.surface_hodge_index_literal

/-- Strict negativity for the original integral Weil divisors. -/
theorem weil_neg_of_orthogonal (H D : X.WeilDivisor)
    (hH : AmpleSerre.IsAmple (SurfaceHodgeIndexSource.divisorLine X hregular H))
    (hD : ¬ SurfaceHodgeIndexSource.NumericallyZero X hregular D)
    (hperp : SurfaceHodgeIndexSource.divisorPairing X hregular D H = 0) :
    SurfaceHodgeIndexSource.divisorPairing X hregular D D < 0 :=
  SurfaceHodgeIndexSource.raw_apply X hregular published H D hH hD hperp

/-- Strict negativity for every original Cartier divisor. -/
theorem cartier_neg_of_orthogonal (H D : CartierDivisor X.toScheme)
    (hH : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme H))
    (hD : ¬ X.NumericallyTrivial (cartierPicardClass X.toScheme D))
    (hperp : intersectionPairing X hregular D H = 0) :
    intersectionPairing X hregular D D < 0 :=
  SurfaceHodgeIndexSource.cartier_neg_of_orthogonal X hregular published
    H D hH hD hperp

/-- Strict negativity on the actual integral Picard group. -/
theorem picard_neg_of_orthogonal
    (L : InvertibleSheaf X.toScheme) (hL : AmpleSerre.IsAmple L)
    (p : X.toScheme.Pic) (hperp : X.picardPairing hregular L.toPic p = 0)
    (hp : ¬ X.NumericallyTrivial p) : X.picardPairing hregular p p < 0 :=
  SurfaceHodgeIndexSource.picard_neg_of_orthogonal X hregular published
    L hL p hperp hp

/-- Semidefiniteness is proved for every actual ample sheaf. -/
theorem semidefinite_of_isAmple
    (L : InvertibleSheaf X.toScheme) (hL : AmpleSerre.IsAmple L) :
    X.HodgeIndexSemidefinite hregular L.toPic :=
  SurfaceHodgeIndexSource.semidefinite_of_isAmple X hregular published L hL

/-- The original projective surface supplies its ample class internally. -/
theorem signature : X.HodgeIndexSignature hregular :=
  SurfaceHodgeIndexSource.signature X hregular published

end KltDP.Geometry.SurfaceHodgeIndexProved

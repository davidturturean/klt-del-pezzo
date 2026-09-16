import KltDP.Geometry.IntersectionPairingSymmetry
import KltDP.Geometry.AdjunctionFormulaSeed

/-!
# Adjunction and the arithmetic genus in pairing form (F04/F03)

The accepted `KltDP.Geometry.AdjunctionSeed.adjunction_degree` states `K_X · C + C · C = deg K_C`
with `C · C` the accepted `selfIntersectionNumber`, conditional on the accepted hypothesis
`AdjunctionIso` (the adjunction isomorphism `Ω_C ≅ (ω ⊗ O_X(D_C))|_C`, which the accepted tree does
not prove). Since E7 makes `selfIntersection` of the class `[O_X(D_C)]` *unconditionally* equal to
that number (`selfIntersection_primeCurveClass`), adjunction can now be stated against the bilinear
pairing:

* `adjunction_degree_pairing`: `K_X · C + [O_X(D_C)]² = deg K_C`.
* `CurveGenusDegreeStatement`: the curve identity `deg K_C = 2g(C) − 2` in the accepted vocabulary
  (`CurveCanonical.canonicalDegree`, `CurveCanonical.genus = dim_k H¹(C, O_C)`). **Stated only.** It
  is the second clause of Stacks 0BS6 (Lemma 53.5.2, `deg(ω_X) = −2χ(X, O_X)`) for a proper Gorenstein
  equidimensional curve; neither the Gorenstein hypothesis nor the dualizing sheaf is expressible in
  the accepted tree, so it is recorded in `laneE/F10_LITERALS.md` and never assumed.
* `adjunction_genus`: under that statement, adjunction reads `K_X · C + [O_X(D_C)]² = 2g(C) − 2`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open KltDP.Geometry KltDP.Geometry.AdjunctionSeed

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- **Adjunction in pairing form**: `K_X · C + [O_X(D_C)]² = deg K_C`, with the self-intersection
taken in the unconditional bilinear pairing. -/
theorem adjunction_degree_pairing (ω : InvertibleSheaf X.toScheme) (C : X.PrimeCurve)
    (h : AdjunctionIso X hregular ω C) :
    canonicalRestrictionDegree X ω C +
        selfIntersection X hregular
          (cartierDivisorInvertibleSheaf X.toScheme (X.primeCurveCartier hregular C)) =
      CurveCanonical.canonicalDegree C.toSpec := by
  rw [X.selfIntersection_primeCurveClass hregular C]
  exact adjunction_degree X hregular ω C h

omit [IsAlgClosed k] in
/-- The curve identity `deg K_C = 2g(C) − 2` in the accepted vocabulary. **Stated only**: it is the
`deg(ω) = −2χ(O)` clause of Stacks 0BS6, whose Gorenstein/dualizing hypotheses are not expressible
here. -/
def CurveGenusDegreeStatement (C : X.PrimeCurve) : Prop :=
  CurveCanonical.canonicalDegree C.toSpec = 2 * (CurveCanonical.genus C.toSpec : ℤ) - 2

/-- **The genus form of adjunction**, under `CurveGenusDegreeStatement`. -/
theorem adjunction_genus (ω : InvertibleSheaf X.toScheme) (C : X.PrimeCurve)
    (h : AdjunctionIso X hregular ω C) (hg : CurveGenusDegreeStatement X C) :
    canonicalRestrictionDegree X ω C +
        selfIntersection X hregular
          (cartierDivisorInvertibleSheaf X.toScheme (X.primeCurveCartier hregular C)) =
      2 * (CurveCanonical.genus C.toSpec : ℤ) - 2 :=
  (X.adjunction_degree_pairing hregular ω C h).trans hg

end KltDP.Geometry.NormalProjectiveSurface

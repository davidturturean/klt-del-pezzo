import KltDP.Geometry.PrimeCurveDegreeTransport
import KltDP.Geometry.PrimeCurveRestrictionDegree
import KltDP.Geometry.PrimeCurveSubscheme
import KltDP.Geometry.SchemePicardPullback
import KltDP.Geometry.SchemeInvertibleSheafPullback
import KltDP.Geometry.InvertibleSheaf
import KltDP.Geometry.Surface
import KltDP.Geometry.PrimeDivisor

/-!
# The curve-level transport `C' · π^*L = C · L`

Let `π : X ⟶ Y` be a morphism of normal projective surfaces, `C'` a prime curve of `X` and `C` a
prime curve of `Y`, and suppose `π` carries `C'` isomorphically onto `C`, in the precise sense that
there is an isomorphism `φ : C'.toScheme ⟶ C.toScheme` with

* `hfac : C'.inclusion ≫ π = φ ≫ C.inclusion` — the square commutes, so `π` restricted to `C'` *is*
  `φ` followed by the inclusion of `C`;
* `hφ : φ ≫ C.toSpec = C'.toSpec` — the isomorphism is over `k`.

Then the degree on `C'` of anything pulled back along `π` is the degree on `C` of the original
(`picardRestrictionDegree_eq_of_isoFactor` on Picard classes,
`restrictionDegree_eq_of_isoFactor` on invertible sheaves).

**Nothing here is new mathematics.**  The engine is the accepted
`PrimeCurveDegreeTransport.picardDegree_pullback_iso`, which computes the degree on a curve of a
class pulled back along an isomorphism as the Euler degree on the target, and whose own docstring
already observes that "two prime curves isomorphic over `k` to the same scheme therefore have the
same degree on pulled-back classes".  This module supplies the corollary in the shape consumers
need — one curve on each of two surfaces, related by a morphism — which the accepted tree states
nowhere.  The proof is `picardRestrictionDegree_pullback`, the factorisation, the accepted
`schemePicardPullbackHom_comp`, and then the transport; the final step is `rfl`, because
`eulerDegree C.toSpec` and `C.picardDegree` have literally the same body
(`picardEulerValue C.toSpec · − picardEulerValue C.toSpec 1`).

The accepted tree already had the degenerate case of this statement, where the composite factors
through a point and the degree is therefore `0`
(`PrimeCurveInclusionLift.restrictionDegree_pullback_eq_zero`, and its Frobenius specialisation
`restrictionDegree_pullback_stepProjection`, i.e. `E · π^*L = 0`).  This is the complementary,
non-degenerate case: the composite factors through an *isomorphism* rather than a point.

**Deliberately not stated here: the `intersectionNumber`/`pullbackDivisor` form.**  Getting from
`C' · π^*L` to `C' · (π^*D)` for a Cartier divisor `D` needs the Picard compatibility of the Cartier
pullback, `CartierPullbackComparison.cartierPicardHom_pullbackDivisor_eq`, which is **queued and not
yet certified**.  Keeping this module's dependencies entirely accepted is deliberate; the composite
statement belongs in a module that may depend on queued work.  Given that lemma, the chain is
`intersectionNumber_eq_picardRestrictionDegree`, then `cartierPicardHom_pullbackDivisor_eq` to
rewrite the class of `π^*D` as `π^*` of the class of `D`, then
`picardRestrictionDegree_eq_of_isoFactor` below.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PrimeCurveTransportPullback

open KltDP.Geometry

variable {k : Type u} [Field k] {X Y : NormalProjectiveSurface k}
  (C' : X.PrimeCurve) (C : Y.PrimeCurve) (π : X.toScheme ⟶ Y.toScheme)
  (φ : C'.toScheme ⟶ C.toScheme) [IsIso φ]
  (hfac : C'.inclusion ≫ π = φ ≫ C.inclusion)
  (hφ : φ ≫ C.toSpec = C'.toSpec)

include hfac hφ in
/-- **Curve-level transport, Picard-class form**: if `π` carries `C'` isomorphically onto `C` over
`k`, the restriction degree along `C'` of a class pulled back along `π` is the restriction degree of
that class along `C`. -/
theorem picardRestrictionDegree_eq_of_isoFactor (p : Y.toScheme.Pic) :
    C'.picardRestrictionDegree (schemePicardPullbackHom π p) = C.picardRestrictionDegree p := by
  rw [C'.picardRestrictionDegree_pullback π p, hfac, schemePicardPullbackHom_comp]
  show C'.picardDegree (schemePicardPullbackHom φ (schemePicardPullbackHom C.inclusion p)) = _
  rw [PrimeCurveDegreeTransport.picardDegree_pullback_iso C' φ C.toSpec hφ]
  rfl

include hfac hφ in
/-- **Curve-level transport, invertible-sheaf form**: `deg_{C'} (π^*L) = deg_C L`. -/
theorem restrictionDegree_eq_of_isoFactor (L : InvertibleSheaf Y.toScheme) :
    C'.restrictionDegree (pullbackInvertibleSheaf π L) = C.restrictionDegree L := by
  rw [← C'.picardRestrictionDegree_toPic, ← C.picardRestrictionDegree_toPic,
    ← schemePicardPullbackHom_toPic]
  exact picardRestrictionDegree_eq_of_isoFactor C' C π φ hfac hφ L.toPic

end KltDP.Geometry.PrimeCurveTransportPullback

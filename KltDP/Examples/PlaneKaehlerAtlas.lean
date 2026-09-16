import KltDP.Geometry.SmoothSurfaceKaehlerAtlas
import KltDP.Examples.FrobeniusBlowupSmooth
import KltDP.Examples.FrobeniusBlowupContact
import KltDP.Geometry.AffineBlowup

/-!
# Actual surfaces carrying the Kähler chart atlas

`SmoothSurfaceKaehlerAtlas` builds `ω_X` and `K_X` for any scheme smooth of relative dimension two
over a field, with no atlas hypothesis. That is only worth having if the hypothesis class is
inhabited, so this module instantiates it at two surfaces the accepted tree already constructs and
already proves smooth of relative dimension two:

* **`planeCanonicalClass`** — `K_X` for the affine plane `A²_k = Spec k[u,v]`, whose structure map
  carries the accepted instance `FrobeniusBlowupSmooth.planeStructure_smoothTwo`.
* **`blowupCanonicalClass`** — `K_X` for the Rees blowup of that plane at the point `(u,v)`, via
  `FrobeniusBlowupSmooth.blowupStructure_smoothTwo`.

Both are elements of the actual Picard group, produced with no hypothesis beyond `[Field k]`. So
`KaehlerChartAtlas.canonicalClass` is applied here to surfaces that exist independently of it, and
the construction is not true by construction: were the chart-frame definition different, these two
terms would not exist.

The accepted tree registers the same instance for every stage of the blowup towers
(`FrobeniusGlobalBlowupSmooth.stageStructure_smoothTwo`,
`FrobeniusContactTowerInfinity`), so the same one-liner applies verbatim to each of those.

`KltDP.Geometry.AffineBlowup.scheme` is written fully qualified: five accepted declarations share
the bare name `scheme`.

Nothing is admitted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.SmoothSurfaceKaehlerAtlas
open KltDP.Examples.FrobeniusBlowupSmooth
open KltDP.Examples.FrobeniusBlowupContact

universe u

namespace KltDP.Examples.PlaneKaehlerAtlas

variable {k : Type u} [Field k]

/-- **The canonical class of the affine plane**, produced by the Kähler chart atlas. -/
def planeCanonicalClass : (Spec (CommRingCat.of (planeRing k))).Pic :=
  canonicalClassOfSmoothSurface (planeStructure (k := k))

/-- **The canonical class of the blowup of the plane at a point**, by the same construction. -/
def blowupCanonicalClass :
    (KltDP.Geometry.AffineBlowup.scheme (centerIdeal (k := k))).Pic :=
  canonicalClassOfSmoothSurface (blowupStructure (k := k))

end KltDP.Examples.PlaneKaehlerAtlas

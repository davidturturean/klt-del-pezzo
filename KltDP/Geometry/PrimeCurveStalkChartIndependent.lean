import KltDP.Geometry.StalkPrimeCurve
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-!
# The stalk prime of a curve does not depend on the affine chart

BRIEF51. `PrimeCurve.stalkHeightOnePrime C hU x hx` is built from a chosen affine open `U`:
the accepted `PrimeCurveStalkCoordinates` proves `stalkHeightOnePrime_comap` and
`stalkHeightOnePrime_injective`, but **not** that the resulting prime of `𝒪_{X,x}` is the same for two
different charts. That was the single obligation left open by BRIEF50, and it is what stopped
`curveMultiplicityAt` from being definable: a chart-dependent multiplicity would be worse than none,
because a consumer could not tell.

## The chart-free object was already in the pin

The key is that Mathlib already proves chart-independence one level up, for the canonical morphism:

* `IsAffineOpen.fromSpecStalk hU hxU := Spec.map (germ U x hxU) ≫ hU.fromSpec`;
* `IsAffineOpen.fromSpecStalk_eq : hU.fromSpecStalk hxU = hV.fromSpecStalk hxV` — **the morphism does
  not depend on the chart**, and `fromSpecStalk_eq_fromSpecStalk` names the chart-free
  `X.fromSpecStalk x`;
* `X.fromSpecStalk x` is an `IsPreimmersion`, so `Scheme.Hom.isEmbedding` gives that its base map is
  injective.

So it suffices to characterise the stalk prime by a property mentioning no chart, and the natural one
is its image point. `fromSpecStalk_base_stalkHeightOnePrime` says that image is exactly
`C.genericPoint`; injectivity of the base map then forces two charts to give the same prime.

## What is *not* enough, recorded so a successor does not retry it

`stalkHeightOnePrime_bijective` (accepted, `StalkPrimeCurveEquiv`) does **not** close this. For each
chart it gives a bijection `{C // x ∈ C} ≃ AffineHeightOnePrime (𝒪_{X,x})` between the *same* two
sets, and two bijections between the same sets need not be equal. Nor does injectivity of
`stalkPrimeChartPoint` help: that map is itself chart-indexed, so it cannot compare across charts.
The comparison has to be made against an object that carries no chart at all.

## Statement shape

The theorem fixes **one** point `y : X.toScheme` with two membership proofs `y ∈ U`, `y ∈ V`, rather
than two subtype points `x₁ : U`, `x₂ : V`. With two subtype points the two stalks would be
`𝒪_{X,↑x₁}` and `𝒪_{X,↑x₂}` — different types, forcing a transport. With one `y` both sides live in
`AffineHeightOnePrime (X.stalk y)` on the nose, since `↑⟨y, h⟩` reduces to `y` by `rfl`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PrimeCurveStalkChartIndependent

open KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k}

/-! ## Bridging the chart-indexed point to the chart-free morphism -/

/-- The chart-free morphism `Spec 𝒪_{X,y} ⟶ X` sends a stalk prime to the accepted chart point
`stalkPrimeChartPoint`. This is what lets a chart-indexed construction be compared across charts. -/
theorem fromSpecStalk_base_apply {U : X.toScheme.Opens} (hU : IsAffineOpen U)
    (y : X.toScheme) (hyU : y ∈ U) (q : RingTheory.AffineHeightOnePrime (X.stalk y)) :
    (X.toScheme.fromSpecStalk y).base q.1 =
      (X.stalkPrimeChartPoint hU ⟨y, hyU⟩ q : X.toScheme) := by
  have h1 : (X.toScheme.fromSpecStalk y).base q.1
      = hU.fromSpec.base (X.stalkPrimeInChart (⟨y, hyU⟩ : U) q) := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk hyU, IsAffineOpen.fromSpecStalk,
      Scheme.comp_base_apply]
    rfl
  rw [h1, ← X.stalkPrimeChartPoint_primeIdealOf hU ⟨y, hyU⟩ q]
  exact hU.fromSpec_primeIdealOf _

/-! ## The chart point of a curve's stalk prime is the curve's generic point -/

/-- Contracting the stalk prime of `C` back to the chart recovers the generic point of `C`. -/
theorem stalkPrimeChartPoint_stalkHeightOnePrime (C : X.PrimeCurve) {U : X.toScheme.Opens}
    (hU : IsAffineOpen U) (x : U) (hx : (x : X.toScheme) ∈ C) :
    (X.stalkPrimeChartPoint hU x (C.stalkHeightOnePrime hU x hx) : X.toScheme) =
      C.genericPoint := by
  have hprime : hU.primeIdealOf (X.stalkPrimeChartPoint hU x (C.stalkHeightOnePrime hU x hx))
      = hU.primeIdealOf ⟨C.genericPoint, C.genericPoint_mem_of_mem x hx⟩ := by
    rw [X.stalkPrimeChartPoint_primeIdealOf hU x _]
    apply PrimeSpectrum.ext
    exact C.stalkHeightOnePrime_comap hU x hx
  have himg := congrArg (fun p => hU.fromSpec.base p) hprime
  simpa only [hU.fromSpec_primeIdealOf] using himg

/-! ## The chart-free characterisation, and chart-independence -/

/-- **The chart-free characterisation.** Under the canonical `Spec 𝒪_{X,y} ⟶ X`, which mentions no
chart, the stalk prime of `C` at `y` goes to the generic point of `C`. -/
theorem fromSpecStalk_base_stalkHeightOnePrime (C : X.PrimeCurve) {U : X.toScheme.Opens}
    (hU : IsAffineOpen U) (y : X.toScheme) (hyU : y ∈ U) (hy : y ∈ C) :
    (X.toScheme.fromSpecStalk y).base (C.stalkHeightOnePrime hU ⟨y, hyU⟩ hy).1 =
      C.genericPoint := by
  rw [fromSpecStalk_base_apply hU y hyU _]
  exact stalkPrimeChartPoint_stalkHeightOnePrime C hU ⟨y, hyU⟩ hy

/-- **The obligation, closed: the stalk prime of a curve at a point is independent of the affine
chart used to construct it.** Two charts containing the same point give the same height-one prime of
`𝒪_{X,y}`, because both are sent to `C.genericPoint` by a map that mentions no chart and is
injective. -/
theorem stalkHeightOnePrime_chart_independent (C : X.PrimeCurve)
    {U V : X.toScheme.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (y : X.toScheme) (hyU : y ∈ U) (hyV : y ∈ V) (hy : y ∈ C) :
    C.stalkHeightOnePrime hU ⟨y, hyU⟩ hy = C.stalkHeightOnePrime hV ⟨y, hyV⟩ hy := by
  apply Subtype.ext
  apply (X.toScheme.fromSpecStalk y).isEmbedding.injective
  rw [fromSpecStalk_base_stalkHeightOnePrime C hU y hyU hy,
    fromSpecStalk_base_stalkHeightOnePrime C hV y hyV hy]

end KltDP.Geometry.PrimeCurveStalkChartIndependent

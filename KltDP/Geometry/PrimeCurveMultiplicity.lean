import KltDP.Geometry.PrimeCurveStalkChartIndependent
import KltDP.RingTheory.LocalMultiplicity
import KltDP.Geometry.RegularStalkUFD

/-!
# The multiplicity of a curve at a point of a surface

BRIEF51, second half. With the chart-independence obligation closed
(`PrimeCurveStalkChartIndependent.stalkHeightOnePrime_chart_independent`), the multiplicity of a
prime curve at a point of a regular surface becomes definable, which BRIEF50 had to stop short of.

## Why this was blocked, and what unblocked it

`primeMultiplicity` (queued, `KltDP.RingTheory.LocalMultiplicity`) is the multiplicity of a
**height-one prime** of a Noetherian local UFD — the germ at `y` of a curve through `y`. To read it
off a curve one needs that germ, and the accepted route to it, `PrimeCurve.stalkHeightOnePrime`,
takes an **affine chart `U` as an argument**. BRIEF50 therefore declined to define a geometric
multiplicity: a chart-dependent one would be worse than none, since a consumer could not tell.

`chartMultiplicity_chart_independent` below is the payoff: the number does not depend on the chart.

## The two independence statements are different, and both are needed

* `primeMultiplicity_eq_of_span` (BRIEF50) — independence of the chosen **local equation**, since a
  local equation is determined only up to a unit;
* `chartMultiplicity_chart_independent` (here) — independence of the chosen **affine chart**.

Neither implies the other, and without both the number is not an invariant of `(C, y)`.

## Instances, and one deliberate design choice

The stalk of a normal projective surface already carries `IsDomain` and `IsNoetherianRing` as global
instances, and `IsLocalRing` comes from `LocallyRingedSpace` in the pin. The remaining requirement,
`UniqueFactorizationMonoid (X.stalk y)`, is **not** automatic: it follows from regularity at `y`
(`stalk_uniqueFactorizationMonoid_of_regularPoint`), which is why `hreg` appears in the signature of
`curveMultiplicityAt` rather than being hidden.

`chartMultiplicity` takes that instance as an **instance-implicit argument** rather than introducing
it with `letI` in its body, so that its body stays a direct application: a `def` whose body is a
direct application supplies no useful equation lemmas, and `congrArg` would then need `unfold` to see
through it. Because `UniqueFactorizationMonoid` is `Prop`-valued, the instance supplied here and any
instance in scope at a use site are definitionally equal, so no transport ever arises.

## Scope — what is *not* claimed

Nothing here relates this multiplicity to the exceptional coefficient of a blowup. The identity
`σ^*C = C̃ + m·E` needs the comparison of `m`, computed on the base from the curve's own germ, with
the coefficient of `E` in the pullback — a genuine theorem rather than a composition, and untouched.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PrimeCurveMultiplicity

open KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
open KltDP.RingTheory.LocalMultiplicity
open KltDP.Geometry.PrimeCurveStalkChartIndependent

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-! ## An affine chart around an arbitrary point -/

/-- Every point of the surface lies in some affine open. The accepted idiom, isolated so the
multiplicity below can pick a chart. -/
theorem exists_affineOpen_mem (y : X.toScheme) :
    ∃ U : X.toScheme.Opens, IsAffineOpen U ∧ y ∈ U := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    (isBasis_affine_open X.toScheme).exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hU' : IsAffineOpen U := hU
  exact ⟨U, hU', hyU⟩

/-! ## The multiplicity computed in a chart, and its independence of the chart -/

/-- The multiplicity of `C` at `y`, computed through a given affine chart. -/
def chartMultiplicity (C : X.PrimeCurve) {U : X.toScheme.Opens} (hU : IsAffineOpen U)
    {y : X.toScheme} (hyU : y ∈ U) (hy : y ∈ C)
    [UniqueFactorizationMonoid (X.stalk y)] : ℕ :=
  primeMultiplicity (X.stalk y) (C.stalkHeightOnePrime hU ⟨y, hyU⟩ hy)

/-- **The payoff of the chart-independence obligation**: the multiplicity does not depend on the
affine chart in which it is computed. -/
theorem chartMultiplicity_chart_independent (C : X.PrimeCurve)
    {U V : X.toScheme.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    {y : X.toScheme} (hyU : y ∈ U) (hyV : y ∈ V) (hy : y ∈ C)
    [UniqueFactorizationMonoid (X.stalk y)] :
    chartMultiplicity X C hU hyU hy = chartMultiplicity X C hV hyV hy :=
  congrArg (primeMultiplicity (X.stalk y))
    (stalkHeightOnePrime_chart_independent C hU hV y hyU hyV hy)

/-- A curve through a point has multiplicity at least one there. -/
theorem one_le_chartMultiplicity (C : X.PrimeCurve) {U : X.toScheme.Opens} (hU : IsAffineOpen U)
    {y : X.toScheme} (hyU : y ∈ U) (hy : y ∈ C)
    [UniqueFactorizationMonoid (X.stalk y)] :
    1 ≤ chartMultiplicity X C hU hyU hy :=
  one_le_primeMultiplicity (X.stalk y) _

/-! ## The chart-free multiplicity -/

/-- **The multiplicity of a curve at a point of a regular surface.** Chart-free: a chart is chosen
internally, and `curveMultiplicityAt_eq_chartMultiplicity` shows every chart gives this value.
Regularity of `X` appears explicitly because it is what supplies factoriality of the stalk. -/
def curveMultiplicityAt (hreg : ∀ x : X.Point, RegularPoint X.toScheme x)
    (C : X.PrimeCurve) {y : X.toScheme} (hy : y ∈ C) : ℕ :=
  letI : UniqueFactorizationMonoid (X.stalk y) :=
    X.stalk_uniqueFactorizationMonoid_of_regularPoint y (hreg y)
  chartMultiplicity X C (exists_affineOpen_mem X y).choose_spec.1
    (exists_affineOpen_mem X y).choose_spec.2 hy

/-- **Every affine chart computes the chart-free multiplicity.** -/
theorem curveMultiplicityAt_eq_chartMultiplicity
    (hreg : ∀ x : X.Point, RegularPoint X.toScheme x) (C : X.PrimeCurve)
    {U : X.toScheme.Opens} (hU : IsAffineOpen U)
    {y : X.toScheme} (hyU : y ∈ U) (hy : y ∈ C)
    [UniqueFactorizationMonoid (X.stalk y)] :
    curveMultiplicityAt X hreg C hy = chartMultiplicity X C hU hyU hy := by
  letI : UniqueFactorizationMonoid (X.stalk y) :=
    X.stalk_uniqueFactorizationMonoid_of_regularPoint y (hreg y)
  show chartMultiplicity X C (exists_affineOpen_mem X y).choose_spec.1
      (exists_affineOpen_mem X y).choose_spec.2 hy = chartMultiplicity X C hU hyU hy
  exact chartMultiplicity_chart_independent X C _ hU _ hyU hy

/-- Positivity for the chart-free multiplicity. -/
theorem one_le_curveMultiplicityAt (hreg : ∀ x : X.Point, RegularPoint X.toScheme x)
    (C : X.PrimeCurve) {y : X.toScheme} (hy : y ∈ C) :
    1 ≤ curveMultiplicityAt X hreg C hy := by
  letI : UniqueFactorizationMonoid (X.stalk y) :=
    X.stalk_uniqueFactorizationMonoid_of_regularPoint y (hreg y)
  show 1 ≤ chartMultiplicity X C (exists_affineOpen_mem X y).choose_spec.1
      (exists_affineOpen_mem X y).choose_spec.2 hy
  exact one_le_chartMultiplicity X C _ _ hy

end KltDP.Geometry.PrimeCurveMultiplicity

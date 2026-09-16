import KltDP.Geometry.PointBlowupWeilCartier
import KltDP.Geometry.PointBlowupWeilDecomposition
import KltDP.Geometry.PointBlowupPicardSplitting
import KltDP.Geometry.PointBlowupSurface
import KltDP.Geometry.CartierDivisorPullback
import KltDP.Geometry.PrimeCurveCartierVanishingIdeal
import KltDP.Geometry.CartierWeilMap
import KltDP.Geometry.PrimeCurveOrder

/-!
# Pulling a curve back to the point blowup, and reading off its centre-fibre coefficient

BRIEF53, steps 0-3 of `σ^*C = C̃ + m·E`, plus the reduction of the centre-fibre coefficient to an
**order**. The one identity this thread still owes — that this order equals `curveMultiplicityAt` —
is **not** proved here and is stated precisely in the closing section below.

## What is built

For a regular normal projective surface `S` over an algebraically closed field, a closed point
`y = j.base q` of an affine chart, and a prime curve `C` of `S`:

* `projection_genericPointPreserving` — the blowup projection preserves the generic point, so the
  accepted `pullbackDivisor` applies to it. See the note on why this cannot be an `instance`.
* `pullbackPrimeCurveDivisor` — `σ^*D_C`, the pullback of the accepted `primeCurveCartier` along the
  projection, with `pullbackPrimeCurveDivisor_hasRegularEquations`.
* `pullbackPrimeCurveWeil` — its Weil divisor on the blowup surface, through the queued
  `blowupCartierWeilEquiv`.
* `pullbackWeilDecomposition` — that Weil divisor split by the accepted `sourceWeilDecomposition`
  into a centre-fibre part and a part indexed by prime curves of the base. This is the *shape* of
  `σ^*C = C̃ + m·E`.
* `exceptionalCenterFiberCurve` — the accepted exceptional prime curve `E` packaged as a
  `CenterFiberCurve`, which is what the first component of the decomposition is indexed by. The
  subtype condition is discharged by the accepted `coe_exceptionalCurve`, whose underlying set is
  *equal* to the centre fibre, not merely contained in it.
* `projection_base_exceptionalCurve_genericPoint` — `σ` sends the generic point of `E` to `y`. This
  is what lets a chart of `D_C` around `y` be used to compute the coefficient along `E`.

## The reduction that is the point of this module

`centreCoefficient_eq_order`: **the centre-fibre coefficient of `σ^*C` is the order along `E` of any
local equation of `σ^*D_C` near the generic point of `E`**, and
`centreCoefficient_eq_order_pulledEquation` instantiates that at the accepted `pulledEquation`, i.e.
at `σ^*f` for `f` a local equation of `C` on any chart containing `y`.

The general form is deliberate. Stating it for *any* `f` satisfying the equation-class hypothesis,
rather than only for the chosen `pulledEquation`, is what makes it usable and keeps it from being a
restatement of the construction: nothing in its hypotheses mentions the order, and the conclusion
forces the coefficient.

## What is NOT proved here — the remaining theorem, stated exactly

Writing `m = curveMultiplicityAt S hreg C hy` for the multiplicity of `C` at `y` (queued,
`Geometry/PrimeCurveMultiplicity`), the outstanding identity is

  `(exceptionalCurve …).order (pulledEquation σ D_C hD c) = (m : ℤ)`

i.e. **the order along `E` of the pulled-back local equation equals the `m_y`-adic order of that
equation's germ at `y`**. That identifies an order in the discrete valuation ring `𝒪_{T,η_E}` with an
order in the two-dimensional regular local ring `𝒪_{S,y}`, and it is a genuine theorem, not a
composition. It is *not* attempted here, and no weakened surrogate for it is stated. Its two missing
inputs, as far as this lane has established them, are:

1. the extension of the centre ideal to the blowup being the exceptional ideal, at the stalk of
   `η_E` — the accepted `AffineBlowup.exceptionalIdeal` is `extendedCenter`, but no accepted result
   computes `𝒪_{T,η_E}` or identifies its maximal ideal with that extension;
2. the sharpness that forces equality rather than only `m ≤ ord`, which needs the associated graded
   ring of `𝒪_{S,y}` to be a domain. The accepted `RingTheory/AssociatedGradedPrime` and
   `RingTheory/LeadingFormAdditivity` supply exactly that implication from `SharpProduct`, and the
   accepted `Examples/PlaneAssociatedGradedDomain` discharges it **for the polynomial plane only**;
   the regular-local case (`gr` of a regular local ring is a polynomial ring) is recorded there as
   explicitly out of scope and is still unbuilt.

`m` is defined on the base from the curve's own germ, with no reference to any blowup, and must stay
that way: defining it as the coefficient below would make the missing identity true by construction
and would carry no geometry.

## Why `projection_genericPointPreserving` is a theorem and not an `instance`

`GenericPointPreserving (projection j q hclosed)` is discharged by the accepted
`surface_projection_genericPoint`, which needs the *surface* `S` — its proof runs through
`S.affine_closed_point_ideal_ne_bot`, i.e. through `dimension_two`. But `S` does not occur in
`projection j q hclosed`; it occurs only as the codomain `S.toScheme` of `j`, and recovering `S` from
`S.toScheme` means inverting a structure projection. So no declaration of this fact can ever be
*found* by instance synthesis, whatever it is labelled. It is therefore a `theorem`, supplied with
`letI` at each use, and this module does the supplying so that consumers need not.

## Conditionality — carried, not discharged

Everything past the divisor level carries `hR : BlowupChartRegularLiteral` (Stacks 0AGR, chart form),
which is **queued and undischarged** and is *not* one of the project's four admitted axioms;
`hP : RegularProperProjectiveLiteral` (Stacks 0C5P), accepted but likewise an undischarged
`structure … : Prop`; and `hreg`, regularity of `S`. `eF` is the Stacks 0AGQ `P¹` identification of
the centre fibre, taken as data exactly as the accepted `exceptionalCurve` takes it. The Weil-side
inputs `blowupNPS`/`blowupCartierWeilEquiv` are **queued, not accepted**
(`Geometry/PointBlowupWeilCartier`).

`IsIntegral (PointBlowupGluing.scheme j q hclosed)` appears as an instance-implicit section variable
rather than a local instance, for the same reason recorded in `PointBlowupExceptionalCartier`: the
accepted discharge `surface_scheme_isIntegral S j q hclosed` carries explicit non-instance arguments
and so can never be found by synthesis. Consumers supply it with that term.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.PointBlowupPullbackWeil

open KltDP.Geometry
open KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.PointBlowupGluing
open KltDP.Geometry.BlowupExceptional
open KltDP.Geometry.PointBlowupWeil
open KltDP.Geometry.PointBlowupSplitting
open KltDP.Literature.Stacks

variable {k : Type u} [Field k] [IsAlgClosed k] {R : Type u} [CommRing R]
    (S : NormalProjectiveSurface k)
    (j : Spec (CommRingCat.of R) ⟶ S.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set S.toScheme))

/-! ## Step 0: the projection preserves the generic point -/

section Divisor

variable [IsIntegral (PointBlowupGluing.scheme j q hclosed)]

/-- **The blowup projection is `GenericPointPreserving`**, so the accepted `pullbackDivisor` applies
to it. This is the accepted `surface_projection_genericPoint` wrapped in the class's anonymous
constructor. It is a `theorem` rather than an `instance` because `S` is not determined by
`projection j q hclosed`: `S` occurs only as the codomain `S.toScheme` of `j`, so synthesis could
never recover it. See the module docstring. -/
theorem projection_genericPointPreserving :
    GenericPointPreserving (PointBlowupGluing.projection j q hclosed) :=
  ⟨PointBlowupGluing.surface_projection_genericPoint S j q hclosed⟩

variable (hreg : ∀ x : S.Point, RegularPoint S.toScheme x)

/-! ## Step 1: pull the curve's Cartier divisor back along the projection -/

/-- **`σ^*D_C`.** The pullback along the blowup projection of the accepted Cartier divisor of the
prime curve `C`. -/
def pullbackPrimeCurveDivisor (C : S.PrimeCurve) :
    CartierDivisor (PointBlowupGluing.scheme j q hclosed) :=
  letI : GenericPointPreserving (PointBlowupGluing.projection j q hclosed) :=
    projection_genericPointPreserving S j q hclosed
  pullbackDivisor (PointBlowupGluing.projection j q hclosed) (S.primeCurveCartier hreg C)
    (S.primeCurveCartier_hasRegularEquations hreg C)

/-- The pullback again has regular local equations, so the whole effective-divisor API applies. -/
theorem pullbackPrimeCurveDivisor_hasRegularEquations (C : S.PrimeCurve) :
    HasRegularCartierEquations (PointBlowupGluing.scheme j q hclosed)
      (pullbackPrimeCurveDivisor S j q hclosed hreg C) := by
  letI : GenericPointPreserving (PointBlowupGluing.projection j q hclosed) :=
    projection_genericPointPreserving S j q hclosed
  exact pullbackDivisor_hasRegularEquations (PointBlowupGluing.projection j q hclosed)
    (S.primeCurveCartier hreg C) (S.primeCurveCartier_hasRegularEquations hreg C)

section Weil

variable (hR : BlowupChartRegularLiteral k) (hP : RegularProperProjectiveLiteral k)

/-! ## Step 2: cross to Weil divisors on the blowup surface -/

/-- **The Weil divisor of `σ^*C` on the blowup**, through the queued `blowupCartierWeilEquiv`. -/
def pullbackPrimeCurveWeil (C : S.PrimeCurve) :
    (blowupNPS S j q hclosed hR hP hreg).WeilDivisor :=
  blowupCartierWeilEquiv S j q hclosed hR hP hreg
    (pullbackPrimeCurveDivisor S j q hclosed hreg C)

/-- It is the accepted Cartier-to-Weil homomorphism of the blowup surface, not a replacement map. -/
theorem pullbackPrimeCurveWeil_eq (C : S.PrimeCurve) :
    pullbackPrimeCurveWeil S j q hclosed hreg hR hP C =
      (blowupNPS S j q hclosed hR hP hreg).cartierToWeilHom
        (pullbackPrimeCurveDivisor S j q hclosed hreg C) :=
  blowupCartierWeilEquiv_apply S j q hclosed hR hP hreg _

/-! ## Step 3: decompose into a centre-fibre part and a base part -/

/-- **The decomposition of `σ^*C`** by the accepted `sourceWeilDecomposition`: a finite integer
combination of curves in the centre fibre, together with a Weil divisor of the base. This is the
shape of `σ^*C = C̃ + m·E`. -/
def pullbackWeilDecomposition (C : S.PrimeCurve) :
    (PointBlowupGluing.CenterFiberCurve S j q hclosed →₀ ℤ) × S.WeilDivisor :=
  PointBlowupGluing.sourceWeilDecomposition S j q hclosed
    (pullbackPrimeCurveWeil S j q hclosed hreg hR hP C)

/-- Each centre-fibre coefficient of the decomposition is the coefficient of that curve in `σ^*C`
itself; the accepted transport lemma, instantiated. -/
theorem pullbackWeilDecomposition_centre_apply (C : S.PrimeCurve)
    (Z : PointBlowupGluing.CenterFiberCurve S j q hclosed) :
    (pullbackWeilDecomposition S j q hclosed hreg hR hP C).1 Z =
      pullbackPrimeCurveWeil S j q hclosed hreg hR hP C Z.val :=
  PointBlowupGluing.sourceWeilDecomposition_center_coefficient S j q hclosed _ Z

/-- Each base coefficient of the decomposition is the coefficient of `σ^*C` at the corresponding
non-exceptional source curve; the accepted transport lemma, instantiated. -/
theorem pullbackWeilDecomposition_outside_apply (C D : S.PrimeCurve) :
    (pullbackWeilDecomposition S j q hclosed hreg hR hP C).2 D =
      pullbackPrimeCurveWeil S j q hclosed hreg hR hP C
        ((PointBlowupGluing.outsideCurveEquiv S j q hclosed).symm D).val :=
  PointBlowupGluing.sourceWeilDecomposition_original_coefficient S j q hclosed _ D

/-! ## The exceptional curve as a centre-fibre curve -/

variable (eF : PointBlowupGluing.globalCenterFiber j q hclosed ≅ projectiveSpace k 1)

omit [IsIntegral (PointBlowupGluing.scheme j q hclosed)] in
/-- **`σ` sends the generic point of `E` to the centre.** The underlying set of the accepted
exceptional curve *is* the fibre over `y`, and a curve contains its own generic point. -/
theorem projection_base_exceptionalCurve_genericPoint :
    (PointBlowupGluing.projection j q hclosed).base
        (exceptionalCurve S j q hclosed hR hP hreg eF).genericPoint = j.base q := by
  have hmem : (exceptionalCurve S j q hclosed hR hP hreg eF).genericPoint ∈
      ((exceptionalCurve S j q hclosed hR hP hreg eF :
        (blowupSurf S j q hclosed hR hP hreg).PrimeCurve) :
        Set (blowupSurf S j q hclosed hR hP hreg).toScheme) :=
    NormalProjectiveSurface.PrimeCurve.genericPoint_mem _
  rw [coe_exceptionalCurve S j q hclosed hR hP hreg eF] at hmem
  exact hmem

/-- **The exceptional curve packaged as a `CenterFiberCurve`**, which is the index type of the
first component of `pullbackWeilDecomposition`. The subtype condition is the accepted
`coe_exceptionalCurve`, which gives equality with the centre fibre. -/
def exceptionalCenterFiberCurve : PointBlowupGluing.CenterFiberCurve S j q hclosed :=
  ⟨(exceptionalCurve S j q hclosed hR hP hreg eF :
      (blowupSurf S j q hclosed hR hP hreg).PrimeCurve),
    by
      intro z hz
      have hz' : z ∈ ((exceptionalCurve S j q hclosed hR hP hreg eF :
          (blowupSurf S j q hclosed hR hP hreg).PrimeCurve) :
          Set (blowupSurf S j q hclosed hR hP hreg).toScheme) := hz
      rw [coe_exceptionalCurve S j q hclosed hR hP hreg eF] at hz'
      exact hz'⟩

omit [IsIntegral (PointBlowupGluing.scheme j q hclosed)] in
@[simp] theorem exceptionalCenterFiberCurve_val :
    (exceptionalCenterFiberCurve S j q hclosed hreg hR hP eF).val =
      (exceptionalCurve S j q hclosed hR hP hreg eF :
        (blowupSurf S j q hclosed hR hP hreg).PrimeCurve) := rfl

/-! ## The reduction of the centre-fibre coefficient to an order -/

/-- **The centre-fibre coefficient of `σ^*C` is the order along `E` of a local equation of
`σ^*D_C`.** Stated for *any* rational function representing the pulled-back divisor near the generic
point of `E`: no hypothesis mentions an order, and the conclusion forces the coefficient. -/
theorem centreCoefficient_eq_order (C : S.PrimeCurve)
    (U : (PointBlowupGluing.scheme j q hclosed).Opens) [Nonempty U]
    (hE : (exceptionalCurve S j q hclosed hR hP hreg eF).genericPoint ∈ U)
    (f : (PointBlowupGluing.scheme j q hclosed).functionFieldˣ)
    (hf : cartierEquationClassHom (PointBlowupGluing.scheme j q hclosed) U (Additive.ofMul f) =
      (cartierDivisorSheaf (PointBlowupGluing.scheme j q hclosed)).val.map
        (homOfLE (show U ≤ ⊤ from le_top)).op
        (pullbackPrimeCurveDivisor S j q hclosed hreg C)) :
    (pullbackWeilDecomposition S j q hclosed hreg hR hP C).1
        (exceptionalCenterFiberCurve S j q hclosed hreg hR hP eF) =
      (exceptionalCurve S j q hclosed hR hP hreg eF).order f := by
  rw [pullbackWeilDecomposition_centre_apply, exceptionalCenterFiberCurve_val,
    pullbackPrimeCurveWeil_eq]
  exact NormalProjectiveSurface.cartierToWeilHom_apply_of_equation
    (blowupNPS S j q hclosed hR hP hreg) (pullbackPrimeCurveDivisor S j q hclosed hreg C)
    (exceptionalCurve S j q hclosed hR hP hreg eF) U hE f hf

/-- **The centre-fibre coefficient, computed from a chart of `C` around the centre.** For any
regular equation chart `(U, f, c)` of `D_C` whose open contains `y`, the coefficient of `E` in
`σ^*C` is the order along `E` of the pulled-back equation `σ^*f`.

This is the statement the outstanding theorem has to be compared against: what remains is that this
order equals `curveMultiplicityAt S hreg C`, the `m_y`-adic order of `f`'s germ at `y`. -/
theorem centreCoefficient_eq_order_pulledEquation (C : S.PrimeCurve)
    (c : RegularCartierEquationChart S.toScheme (S.primeCurveCartier hreg C))
    (hy : j.base q ∈ c.chart.openSet) :
    (pullbackWeilDecomposition S j q hclosed hreg hR hP C).1
        (exceptionalCenterFiberCurve S j q hclosed hreg hR hP eF) =
      (exceptionalCurve S j q hclosed hR hP hreg eF).order
        (@pulledEquation _ _ _ _ (PointBlowupGluing.projection j q hclosed)
          (projection_genericPointPreserving S j q hclosed) (S.primeCurveCartier hreg C) c) := by
  letI : GenericPointPreserving (PointBlowupGluing.projection j q hclosed) :=
    projection_genericPointPreserving S j q hclosed
  have hE : (exceptionalCurve S j q hclosed hR hP hreg eF).genericPoint ∈
      PointBlowupGluing.projection j q hclosed ⁻¹ᵁ c.chart.openSet := by
    show (PointBlowupGluing.projection j q hclosed).base
      (exceptionalCurve S j q hclosed hR hP hreg eF).genericPoint ∈ c.chart.openSet
    rw [projection_base_exceptionalCurve_genericPoint S j q hclosed hreg hR hP eF]
    exact hy
  exact centreCoefficient_eq_order S j q hclosed hreg hR hP eF C
    (PointBlowupGluing.projection j q hclosed ⁻¹ᵁ c.chart.openSet) hE _
    (pullbackDivisor_restrict (PointBlowupGluing.projection j q hclosed)
      (S.primeCurveCartier hreg C) (S.primeCurveCartier_hasRegularEquations hreg C) c).symm

end Weil

end Divisor

end KltDP.Geometry.PointBlowupPullbackWeil

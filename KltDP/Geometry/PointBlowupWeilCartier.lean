import KltDP.Geometry.BlowupExceptionalCurve
import KltDP.Geometry.RegularSurfaceWeilPicard
import KltDP.Geometry.PointBlowupCurveDimension

/-!
# Weil and Cartier divisors agree on the glued point blowup

BRIEF49 task 1. `cartierWeilEquiv` carries the instance hypothesis
`[∀ x, UniqueFactorizationMonoid (X.stalk x)]`, recorded in `docs/GAPS.md` as threaded through
consumers but never discharged, and named there as one of the two surviving blockers of the entire
Weil-side family for the point blowup. **It is dischargeable, and with no hypothesis beyond the ones
the blowup surface already carries.**

## The chain, and why nothing new was needed

`BlowupExceptional.blowupSurface` packages the accepted glued point blowup as a
`NormalProjectiveSurface`, and the regularity it consumes for its `normal` field —
`hR.regular S R j q hclosed hreg`, Stacks 0AGR in its chart form — is regularity at **every** point of
the blowup, not merely over the centre. The accepted
`NormalProjectiveSurface.stalks_uniqueFactorizationMonoid_of_regular` (`RegularStalkUFD:34`) turns
exactly that into the factorial-stalk family, and the accepted `RegularSurfaceWeilPicard` already
routes the whole Cartier/Weil/Picard package through a regularity hypothesis, supplying the instance
internally with `letI`. So **one term discharges both `normal` and the factorial stalks**, and this
module is their composition; it introduces no mathematics of its own.

The factorial-stalk requirement was invisible to a search for the type `UniqueFactorizationMonoid`
applied to a blowup stalk, because the producer never mentions a blowup: it is a statement about an
arbitrary surface, and the blowup enters only through its regularity.

## Conditionality, stated exactly

`blowupSurface` takes two literal hypotheses, and they are **carried here, not discharged**:

* `RegularProperProjectiveLiteral` (Stacks 0C5P) is **accepted**, but is an undischarged
  `structure … : Prop`;
* `BlowupChartRegularLiteral` (Stacks 0AGR, chart form) is **queued and undischarged** — nothing in
  the tree or any lane discharges it, and it is *not* one of the project's four admitted axioms;

together with `hreg`, regularity of the base surface `S`. Every statement below therefore holds
**conditionally on those three**, which is materially weaker than an unconditional claim. That is why
all three appear in every signature rather than being hidden in a section variable that a reader
might miss.

## On the strict transform (BRIEF49 task 2 — verification only; nothing is constructed)

`NormalProjectiveSurface.PrimeCurve X` unfolds to
`{Z : IrreducibleCloseds X.toScheme // topologicalKrullDim (Z : Set X.toScheme) = 1}`, which is
character-for-character the return type of the **accepted**
`PointBlowupGluing.strictTransformCurve`. Since `blowupSurface_toScheme` holds by `rfl`, a general
strict transform therefore already **is** a prime curve of the blowup surface.
`strictTransformPrimeCurve` below is that observation typechecked — a re-statement of an accepted
definition at a type it already inhabits, not a construction.

A companion restatement of `strictTransformCurve_image` at the prime-curve type was drafted and then
**deliberately dropped**. It failed only on coercion bookkeeping — `.val` lands in
`IrreducibleCloseds` where the accepted statement is phrased with a `Set` — and since
`strictTransformPrimeCurve` is *definitionally* `PointBlowupGluing.strictTransformCurve`, any
consumer can cite the accepted `strictTransformCurve_image` directly. The restatement would have
carried no content beyond it, so it was removed rather than plumbed.

What remains genuinely absent, and is *not* supplied here: the exceptional divisor in **Cartier**
form in general (only the prime-curve and family-specific Cartier forms exist), and the multiplicity
`m`. No statement of `σ^*C = C̃ + m·E` as an identity of divisors exists anywhere, and none is made
here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PointBlowupWeil

open KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.BlowupExceptional
open KltDP.Literature.Stacks

variable {k : Type u} [Field k] [IsAlgClosed k] {R : Type u} [CommRing R]
    (S : NormalProjectiveSurface k)
    (j : Spec (CommRingCat.of R) ⟶ S.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set S.toScheme))
    (hR : BlowupChartRegularLiteral k) (hP : RegularProperProjectiveLiteral k)
    (hreg : ∀ x : S.Point, RegularPoint S.toScheme x)

/-- The glued point blowup packaged as a normal projective surface (lane E's `blowupSurface`,
Stacks 0AGR for regularity and 0C5P for projectivity). -/
abbrev blowupNPS : NormalProjectiveSurface k :=
  blowupSurface S j q hclosed hR hP hreg

/-! ## The factorial stalks -/

/-- Regularity at every point of the blowup surface — Stacks 0AGR in its chart form. This is the
single term that discharges both the `normal` field and the factorial stalks. -/
theorem blowupSurface_regularPoints :
    ∀ y : (blowupNPS S j q hclosed hR hP hreg).Point,
      RegularPoint (blowupNPS S j q hclosed hR hP hreg).toScheme y :=
  hR.regular S R j q hclosed hreg

/-- **The factorial-stalk family for the point blowup, discharged.** This is the hypothesis
`cartierWeilEquiv` carries and that `GAPS.md` records as never discharged. -/
theorem blowupSurface_stalks_uniqueFactorizationMonoid :
    ∀ x : (blowupNPS S j q hclosed hR hP hreg).toScheme,
      UniqueFactorizationMonoid ((blowupNPS S j q hclosed hR hP hreg).stalk x) :=
  (blowupNPS S j q hclosed hR hP hreg).stalks_uniqueFactorizationMonoid_of_regular
    (blowupSurface_regularPoints S j q hclosed hR hP hreg)

/-! ## The Weil-side comparisons for the blowup -/

/-- **Cartier and Weil divisors agree on the glued point blowup.** -/
def blowupCartierWeilEquiv :
    CartierDivisor (blowupNPS S j q hclosed hR hP hreg).toScheme ≃+
      (blowupNPS S j q hclosed hR hP hreg).WeilDivisor :=
  (blowupNPS S j q hclosed hR hP hreg).regularCartierWeilEquiv
    (blowupSurface_regularPoints S j q hclosed hR hP hreg)

/-- The equivalence is the accepted Cartier-to-Weil homomorphism, not a replacement map. -/
theorem blowupCartierWeilEquiv_apply
    (D : CartierDivisor (blowupNPS S j q hclosed hR hP hreg).toScheme) :
    blowupCartierWeilEquiv S j q hclosed hR hP hreg D =
      (blowupNPS S j q hclosed hR hP hreg).cartierToWeilHom D := rfl

/-- **Cartier and Weil divisor classes agree on the blowup.** -/
def blowupCartierWeilClassEquiv :
    CartierClassGroup (blowupNPS S j q hclosed hR hP hreg).toScheme ≃+
      (blowupNPS S j q hclosed hR hP hreg).WeilClassGroup :=
  (blowupNPS S j q hclosed hR hP hreg).regularCartierWeilClassEquiv
    (blowupSurface_regularPoints S j q hclosed hR hP hreg)

/-- **Weil divisor classes on the blowup are its Picard group.** -/
def blowupWeilClassPicardEquiv :
    (blowupNPS S j q hclosed hR hP hreg).WeilClassGroup ≃+
      Additive (blowupNPS S j q hclosed hR hP hreg).toScheme.Pic :=
  (blowupNPS S j q hclosed hR hP hreg).regularWeilClassPicardEquiv
    (blowupSurface_regularPoints S j q hclosed hR hP hreg)

/-! ## The general strict transform, as a prime curve of the blowup

Verification of an accepted definition at a type it already inhabits. Nothing is constructed. -/

/-- **The accepted general strict transform is already a prime curve of the blowup surface.**
`PrimeCurve` unfolds to the dimension-one `IrreducibleCloseds` subtype, which is exactly the return
type of `PointBlowupGluing.strictTransformCurve`. -/
def strictTransformPrimeCurve (C : S.PrimeCurve) :
    (blowupNPS S j q hclosed hR hP hreg).PrimeCurve :=
  PointBlowupGluing.strictTransformCurve S j q hclosed C

end KltDP.Geometry.PointBlowupWeil

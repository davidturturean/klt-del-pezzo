import KltDP.Geometry.PrimeCurveStalkCoordinates
import KltDP.Geometry.UFDDivisorCoordinates

/-!
# Local rational equations from factoriality of an actual stalk

At a point whose actual stalk is a UFD, a finite Weil divisor has a
rational equation on an open neighborhood. First restrict its coefficients
to the actual curves through the point. Their injective map into the
stalk's height-one primes gives finite stalk coordinates. The explicit UFD
product realizes those coordinates in the original function field.

The difference from the original divisor has finite curve support and
does not contain the point. Its actual geometric complement is the
required open neighborhood. No factorial affine neighborhood, reverse
curve/prime correspondence, or Cartier representative is an assumption.
Gluing these local equations as Cartier sections requires a separate
transition-unit argument.

The finite-coordinate operations reuse pinned Mathlib `Finsupp.subtypeDomain`
and `Finsupp.embDomain` (c44e0c8ee63ca166450922a373c7409c5d26b00b,
Apache-2.0). All geometry and orders use the project's actual schemes,
curve stalks, and function field.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The finite coefficients of a divisor on curves through a point,
extended by zero to the actual stalk's height-one-prime carrier. -/
def stalkDivisorCoordinates {U : X.toScheme.Opens} (hU : IsAffineOpen U)
    (x : U) (D : X.WeilDivisor) : RingTheory.AffineHeightOnePrime (X.stalk x) →₀ ℤ :=
  Finsupp.embDomain
    ⟨fun C : {C : X.PrimeCurve // (x : X.toScheme) ∈ C} =>
        C.1.stalkHeightOnePrime hU x C.2,
      PrimeCurve.stalkHeightOnePrime_injective hU x⟩
    (D.subtypeDomain (fun C => (x : X.toScheme) ∈ C))

/-- At every curve through the point the stalk coordinates recover the
original coefficient. Injectivity prevents combining different curves. -/
theorem stalkDivisorCoordinates_apply {U : X.toScheme.Opens} (hU : IsAffineOpen U)
    (x : U) (D : X.WeilDivisor) (C : X.PrimeCurve) (hx : (x : X.toScheme) ∈ C) :
    X.stalkDivisorCoordinates hU x D (C.stalkHeightOnePrime hU x hx) = D C := by
  exact Finsupp.embDomain_apply _ _ (⟨C, hx⟩ : {C : X.PrimeCurve // (x : X.toScheme) ∈ C})

/-- A concrete fraction-field product realizing all divisor coefficients
on curves through the point. The UFD hypothesis is on the actual stalk. -/
def stalkRationalEquation {U : X.toScheme.Opens} (hU : IsAffineOpen U)
    (x : U) [UniqueFactorizationMonoid (X.stalk x)] (D : X.WeilDivisor) :
    X.toScheme.functionFieldˣ :=
  RingTheory.fractionOfDivisorCoordinates (X.stalk x) X.toScheme.functionField
    (X.stalkDivisorCoordinates hU x D)

/-- The constructed rational function has the prescribed order along
every actual curve through the point. -/
theorem stalkRationalEquation_order {U : X.toScheme.Opens} (hU : IsAffineOpen U)
    (x : U) [UniqueFactorizationMonoid (X.stalk x)] (D : X.WeilDivisor)
    (C : X.PrimeCurve) (hx : (x : X.toScheme) ∈ C) :
    C.order (X.stalkRationalEquation hU x D) = D C := by
  rw [C.order_eq_stalkHeightOnePrime_order hU x hx]
  exact (RingTheory.affinePrincipalOrder_fractionOfDivisorCoordinates
    (X.stalk x) X.toScheme.functionField (X.stalkDivisorCoordinates hU x D)
    (C.stalkHeightOnePrime hU x hx)).trans
      (X.stalkDivisorCoordinates_apply hU x D C hx)

/-- Factoriality of the actual stalk gives an actual open neighborhood
and a rational equation for the Weil divisor there. The neighborhood is
obtained by removing the closed support of the computed difference. -/
theorem exists_rationalEquation_near_of_stalk_ufd (x : X.toScheme)
    [UniqueFactorizationMonoid (X.stalk x)] (D : X.WeilDivisor) :
    ∃ (V : X.toScheme.Opens), x ∈ V ∧ ∃ f : X.toScheme.functionFieldˣ,
      ∀ C : X.PrimeCurve, C.genericPoint ∈ V → C.order f = D C := by
  let U : X.toScheme.Opens := (X.toScheme.affineCover.map x).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.toScheme.affineCover.map x)
  have hxU : x ∈ U := X.toScheme.affineCover.covers x
  let xu : U := ⟨x, hxU⟩
  let f : X.toScheme.functionFieldˣ := X.stalkRationalEquation hU xu D
  have horders (C : X.PrimeCurve) (hxC : x ∈ C) : C.order f = D C :=
    X.stalkRationalEquation_order hU xu D C hxC
  let E : X.WeilDivisor := D - X.principalDivisor f
  let V : X.toScheme.Opens := ⟨(divisorSupport E)ᶜ, (divisorSupport_isClosed E).isOpen_compl⟩
  have hxV : x ∈ V := by
    intro hxE
    obtain ⟨C, hC, hxC⟩ := (mem_divisorSupport E x).mp hxE
    apply hC
    change D C - C.order f = 0
    rw [horders C hxC, sub_self]
  refine ⟨V, hxV, f, fun C hCV => ?_⟩
  have hzero : E C = 0 := by
    by_contra hne
    exact hCV ((mem_divisorSupport E C.genericPoint).mpr ⟨C, hne, C.genericPoint_mem⟩)
  change D C - C.order f = 0 at hzero
  exact (sub_eq_zero.mp hzero).symm

end KltDP.Geometry.NormalProjectiveSurface

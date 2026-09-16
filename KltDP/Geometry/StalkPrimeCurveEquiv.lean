import KltDP.Geometry.StalkPrimeCurve
import KltDP.Geometry.ClosedPointDimension

/-!
# Curves through a point and actual height-one stalk primes

Over the algebraically closed base field, every closed point of the actual
surface has a two-dimensional stalk. A height-one stalk prime contracts
to a point with a one-dimensional stalk, so that point is nonclosed.
Its actual closure therefore is a prime curve. The previously constructed
extension and contraction maps give a bijection, with the original
function-field orders preserved.

The closed-point dimension theorem is proved from finite type and
Noether normalization in the imported modules. It is not a new literature
assumption or an extra field in the surface or curve definitions.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

/-- A height-one stalk prime contracts to a nonclosed scheme point. -/
theorem stalkPrimeChartPoint_not_isClosed {U : X.toScheme.Opens}
    (hU : IsAffineOpen U) (x : U)
    (q : RingTheory.AffineHeightOnePrime (X.stalk x)) :
    ¬ IsClosed ({(X.stalkPrimeChartPoint hU x q : X.toScheme)} : Set X.toScheme) := by
  intro hc
  have hone := X.stalkPrimeChartPoint_stalk_dimension hU x q
  have htwo := X.closed_stalk_dimension_two (X.stalkPrimeChartPoint hU x q) hc
  have h : (1 : WithBot ℕ∞) = 2 := hone.symm.trans htwo
  norm_num at h

/-- Every actual height-one stalk prime comes from an actual curve
through the original point, with no stalk-dimension input. -/
theorem stalkHeightOnePrime_surjective {U : X.toScheme.Opens}
    (hU : IsAffineOpen U) (x : U) :
    Function.Surjective (fun C : {C : X.PrimeCurve // (x : X.toScheme) ∈ C} =>
      C.1.stalkHeightOnePrime hU x C.2) := by
  intro q
  obtain ⟨C, hxC, hC⟩ :=
    X.exists_primeCurve_of_stalkPrimeChartPoint_nonclosed hU x q
      (X.stalkPrimeChartPoint_not_isClosed hU x q)
  exact ⟨⟨C, hxC⟩, hC⟩

/-- The actual extension map from curves through a point to height-one
primes of its stalk is bijective. -/
theorem stalkHeightOnePrime_bijective {U : X.toScheme.Opens}
    (hU : IsAffineOpen U) (x : U) :
    Function.Bijective (fun C : {C : X.PrimeCurve // (x : X.toScheme) ∈ C} =>
      C.1.stalkHeightOnePrime hU x C.2) :=
  ⟨PrimeCurve.stalkHeightOnePrime_injective hU x,
    X.stalkHeightOnePrime_surjective hU x⟩

/-- Actual curves through a point are equivalent to actual height-one
prime ideals in the point's structure-sheaf stalk. -/
def primeCurveStalkEquiv {U : X.toScheme.Opens} (hU : IsAffineOpen U) (x : U) :
    {C : X.PrimeCurve // (x : X.toScheme) ∈ C} ≃
      RingTheory.AffineHeightOnePrime (X.stalk x) :=
  Equiv.ofBijective (fun C => C.1.stalkHeightOnePrime hU x C.2)
    (X.stalkHeightOnePrime_bijective hU x)

theorem primeCurveStalkEquiv_apply {U : X.toScheme.Opens}
    (hU : IsAffineOpen U) (x : U)
    (C : {C : X.PrimeCurve // (x : X.toScheme) ∈ C}) :
    X.primeCurveStalkEquiv hU x C = C.1.stalkHeightOnePrime hU x C.2 := rfl

/-- The equivalence preserves the original normalized orders in the
original function field. -/
theorem primeCurveStalkEquiv_order {U : X.toScheme.Opens}
    (hU : IsAffineOpen U) (x : U)
    (C : {C : X.PrimeCurve // (x : X.toScheme) ∈ C})
    (f : X.toScheme.functionFieldˣ) :
    C.1.order f = RingTheory.affinePrincipalOrder (X.stalk x)
      X.toScheme.functionField (X.primeCurveStalkEquiv hU x C) f :=
  C.1.order_eq_stalkHeightOnePrime_order hU x C.2 f

end KltDP.Geometry.NormalProjectiveSurface

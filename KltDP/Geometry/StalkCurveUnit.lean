import KltDP.Geometry.StalkPrimeCurveEquiv
import KltDP.Geometry.UFDDivisorCoordinates

/-!
# Vanishing curve orders and actual stalk units

The actual curve–stalk-prime correspondence makes the UFD unit criterion
applicable to the original curves on the surface. A nonzero rational
function has zero order on every curve through a point if and only if it
is the image of a unit of that point's actual structure-sheaf stalk.

Factoriality is assumed only for the actual stalk. No factorial affine
neighborhood or Cartier–Weil comparison is assumed. The algebraic unit
criterion is the proved theorem in `UFDDivisorCoordinates`, using the
pinned unique-factorization and reduced-fraction APIs; the geometric
correspondence is proved in `StalkPrimeCurveEquiv`.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

/-- Zero order on all actual curves through a point is equivalent to
being the image of an actual unit in its factorial stalk. -/
theorem curve_orders_eq_zero_iff_stalk_unit (x : X.toScheme)
    [UniqueFactorizationMonoid (X.stalk x)] (f : X.toScheme.functionFieldˣ) :
    (∀ C : X.PrimeCurve, x ∈ C → C.order f = 0) ↔
      ∃ a : (X.stalk x)ˣ,
        Units.map (algebraMap (X.stalk x) X.toScheme.functionField) a = f := by
  let U : X.toScheme.Opens := (X.toScheme.affineCover.map x).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.toScheme.affineCover.map x)
  let xu : U := ⟨x, X.toScheme.affineCover.covers x⟩
  constructor
  · intro hzero
    apply (RingTheory.affinePrincipalDivisor_eq_zero_iff
      (X.stalk x) X.toScheme.functionField f).mp
    ext q
    change RingTheory.affinePrincipalOrder (X.stalk x) X.toScheme.functionField q f = 0
    obtain ⟨C, hC⟩ := X.stalkHeightOnePrime_surjective hU xu q
    rw [← hC, ← C.1.order_eq_stalkHeightOnePrime_order hU xu C.2 f]
    exact hzero C.1 C.2
  · rintro ⟨a, rfl⟩ C hxC
    rw [C.order_eq_stalkHeightOnePrime_order hU xu hxC]
    exact RingTheory.affinePrincipalOrder_map_base_unit (X.stalk x)
      X.toScheme.functionField (C.stalkHeightOnePrime hU xu hxC) a

/-- The stalk unit representing a nonzero rational function is unique,
because the actual stalk embeds into the original function field. -/
theorem existsUnique_stalk_unit_of_curve_orders_eq_zero (x : X.toScheme)
    [UniqueFactorizationMonoid (X.stalk x)] (f : X.toScheme.functionFieldˣ)
    (hzero : ∀ C : X.PrimeCurve, x ∈ C → C.order f = 0) :
    ∃! a : (X.stalk x)ˣ,
      Units.map (algebraMap (X.stalk x) X.toScheme.functionField) a = f := by
  obtain ⟨a, ha⟩ := (X.curve_orders_eq_zero_iff_stalk_unit x f).mp hzero
  refine ⟨a, ha, fun b hb => ?_⟩
  apply Units.ext
  apply IsFractionRing.injective (X.stalk x) X.toScheme.functionField
  exact congrArg (fun c : X.toScheme.functionFieldˣ => (c : X.toScheme.functionField))
    (hb.trans ha.symm)

/-- Two rational equations with equal curve orders through a point
differ by an actual unit of that point's factorial stalk. -/
theorem exists_stalk_unit_of_equal_curve_orders (x : X.toScheme)
    [UniqueFactorizationMonoid (X.stalk x)] (f g : X.toScheme.functionFieldˣ)
    (horders : ∀ C : X.PrimeCurve, x ∈ C → C.order f = C.order g) :
    ∃ a : (X.stalk x)ˣ,
      Units.map (algebraMap (X.stalk x) X.toScheme.functionField) a = f * g⁻¹ := by
  apply (X.curve_orders_eq_zero_iff_stalk_unit x (f * g⁻¹)).mp
  intro C hxC
  rw [PrimeCurve.order_mul, PrimeCurve.order_inv, horders C hxC, add_neg_cancel]

end KltDP.Geometry.NormalProjectiveSurface

import KltDP.Geometry.PrimeCurveOrder
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Local Cartier equations and their normalized orders

For a domain in a field, a local equation is a nonzero field element modulo
the image of the units of the given ring. We use the existing additive-group
quotient to construct this group. At a DVR, the previously constructed order
identifies this quotient with the integers: its kernel is proved to consist
exactly of the local units, and an actual uniformizer proves surjectivity.

The geometric specialization uses the original scheme stalk and function
field. At prime curves on the existing normal surface, the DVR hypothesis
is supplied by the proved generic-point theorem.

This is local equation data, not a construction of the global Cartier
divisor sheaf or its global sections. Gluing local equations, constructing
their invertible module sheaves, and comparing Cartier classes with the
scheme Picard group remain separate constructions. No such comparison or
surjectivity is assumed as structure data.

Reuse: pinned Mathlib's `HeightOneSpectrum.mem_integers_of_valuation_le_one`,
`Valuation.Integers.isUnit_of_one'`, and the quotient first isomorphism theorem.
All have actual proof bodies at c44e0c8ee63ca166450922a373c7409c5d26b00b
under Apache-2.0. No external source port or literature input is used.
-/

noncomputable section

universe u v

namespace KltDP.RingTheory

section LocalEquations

variable (R : Type u) [CommRing R] (K : Type v) [Field K] [Algebra R K]

/-- The actual regular units, viewed in the additive version of the
multiplicative group of nonzero rational functions. -/
def regularUnitImage : AddSubgroup (Additive Kˣ) :=
  (Units.map (algebraMap R K).toMonoidHom).toAdditive.range

/-- The group of local rational equations modulo actual regular units.
For a local domain with its fraction field, this is the local Cartier
equation group. Its definition does not require a DVR hypothesis. -/
abbrev CartierLocalClass := Additive Kˣ ⧸ regularUnitImage R K

/-- The canonical quotient map on actual rational equations. -/
def cartierLocalClassMap : Additive Kˣ →+ CartierLocalClass R K :=
  QuotientAddGroup.mk' (regularUnitImage R K)

theorem mem_regularUnitImage_iff (f : Kˣ) :
    Additive.ofMul f ∈ regularUnitImage R K ↔
      ∃ r : Rˣ, Units.map (algebraMap R K).toMonoidHom r = f := by
  change (∃ r : Additive Rˣ,
    Additive.ofMul (Units.map (algebraMap R K).toMonoidHom r.toMul) = Additive.ofMul f) ↔ _
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r.toMul, congrArg Additive.toMul hr⟩
  · rintro ⟨r, hr⟩
    exact ⟨Additive.ofMul r, congrArg Additive.ofMul hr⟩

/-- A local equation represents zero exactly when it is the image of an
actual unit of the original local ring. -/
theorem cartierLocalClassMap_eq_zero_iff (f : Kˣ) :
    cartierLocalClassMap R K (Additive.ofMul f) = 0 ↔
      ∃ r : Rˣ, Units.map (algebraMap R K).toMonoidHom r = f := by
  change (↑(Additive.ofMul f) : CartierLocalClass R K) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff, mem_regularUnitImage_iff]

/-- Every local class has an actual nonzero rational equation. -/
theorem cartierLocalClassMap_surjective :
    Function.Surjective (cartierLocalClassMap R K) :=
  QuotientAddGroup.mk'_surjective (regularUnitImage R K)

@[simp]
theorem cartierLocalClassMap_map_unit (r : Rˣ) :
    cartierLocalClassMap R K
      (Additive.ofMul (Units.map (algebraMap R K).toMonoidHom r)) = 0 :=
  (cartierLocalClassMap_eq_zero_iff R K _).mpr ⟨r, rfl⟩

end LocalEquations

section DVR

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The ring of integers of the pinned fraction-field valuation is the
actual DVR itself. All nonzero primes of this local Dedekind domain are
its maximal ideal, so the pinned intersection theorem applies. -/
theorem fractionFieldValuation_integers :
    (fractionFieldValuation R K).Integers R where
  hom_inj := IsFractionRing.injective R K
  map_le_one r := (dvrHeightOnePrime R).valuation_le_one (K := K) r
  exists_of_le_one {f} hf := by
    apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K f
    intro p
    have hp : p = dvrHeightOnePrime R := by
      apply IsDedekindDomain.HeightOneSpectrum.ext
      exact IsLocalRing.eq_maximalIdeal p.isMaximal
    simpa only [hp, fractionFieldValuation] using hf

/-- The converse to unit-vanishing: zero order is witnessed by an actual
unit in the original DVR, using its canonical map to the fraction field. -/
theorem divisorOrder_eq_zero_iff_exists_unit (f : Kˣ) :
    divisorOrder R K f = 0 ↔
      ∃ r : Rˣ, Units.map (algebraMap R K).toMonoidHom r = f := by
  constructor
  · intro hf
    have hv : fractionFieldValuation R K (f : K) = 1 := by
      simpa using (divisorOrder_eq_iff R K f 0).mp hf
    obtain ⟨r, hr⟩ := (fractionFieldValuation_integers R K).exists_of_le_one hv.le
    have hu : IsUnit r :=
      (fractionFieldValuation_integers R K).isUnit_of_one' (by simpa only [hr] using hv)
    refine ⟨hu.unit, ?_⟩
    apply Units.ext
    change algebraMap R K (hu.unit : R) = (f : K)
    simpa only [hu.unit_spec] using hr
  · rintro ⟨r, rfl⟩
    exact divisorOrder_map_unit R K r

/-- The kernel of the actual normalized order is exactly the image of
regular units; neither inclusion is an extra input. -/
theorem regularUnitImage_eq_divisorOrderHom_ker :
    regularUnitImage R K = (divisorOrderHom R K).ker := by
  ext f
  change Additive.ofMul f.toMul ∈ regularUnitImage R K ↔
    divisorOrder R K f.toMul = 0
  exact (mem_regularUnitImage_iff R K f.toMul).trans
    (divisorOrder_eq_zero_iff_exists_unit R K f.toMul).symm

/-- An actual uniformizer and its integer powers make the normalized
order onto the integers. This proves surjectivity rather than assuming it. -/
theorem divisorOrderHom_surjective : Function.Surjective (divisorOrderHom R K) := by
  obtain ⟨r, hr, horder⟩ := exists_uniformizer_divisorOrder_one R K
  intro n
  refine ⟨n • Additive.ofMul (fractionFieldUnit R K r hr.ne_zero), ?_⟩
  rw [map_zsmul]
  change n • divisorOrder R K (fractionFieldUnit R K r hr.ne_zero) = n
  rw [horder]
  simp

/-- Local Cartier equations on a DVR are identified with integers by
their actual divisor order, normalized to send a uniformizer to `+1`. -/
def cartierLocalOrderEquiv : CartierLocalClass R K ≃+ ℤ :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (regularUnitImage_eq_divisorOrderHom_ker R K)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (divisorOrderHom R K)
      (divisorOrderHom_surjective R K))

/-- The isomorphism uses the existing order on each representative. -/
@[simp]
theorem cartierLocalOrderEquiv_class (f : Kˣ) :
    cartierLocalOrderEquiv R K (cartierLocalClassMap R K (Additive.ofMul f)) =
      divisorOrder R K f := rfl

/-- Equality of local equations is exactly equality of their orders at
a DVR. This is the local compatibility needed for Cartier-to-Weil order. -/
theorem cartierLocalClassMap_eq_iff_order_eq (f g : Kˣ) :
    cartierLocalClassMap R K (Additive.ofMul f) =
        cartierLocalClassMap R K (Additive.ofMul g) ↔
      divisorOrder R K f = divisorOrder R K g :=
  (cartierLocalOrderEquiv R K).injective.eq_iff.symm

end DVR

end KltDP.RingTheory

namespace KltDP.Geometry

open AlgebraicGeometry

variable (X : Scheme.{u}) [IsIntegral X] (x : X)

/-- Actual local Cartier equations at a point of the original integral
scheme. No claim about a global Cartier-divisor sheaf is folded into this
local quotient construction. -/
abbrev StalkCartierClass :=
  RingTheory.CartierLocalClass (X.presheaf.stalk x) X.functionField

local instance : IsDomain (X.presheaf.stalk x) := integralSchemeStalk_isDomain X x

/-- At an actual DVR stalk, the constructed local quotient has its
canonical normalized integer order. -/
def stalkCartierOrderEquiv [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    StalkCartierClass X x ≃+ ℤ :=
  RingTheory.cartierLocalOrderEquiv (X.presheaf.stalk x) X.functionField

@[simp]
theorem stalkCartierOrderEquiv_class [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (f : X.functionFieldˣ) :
    stalkCartierOrderEquiv X x
      (RingTheory.cartierLocalClassMap (X.presheaf.stalk x) X.functionField
        (Additive.ofMul f)) = stalkDivisorOrder X x f := rfl

namespace NormalProjectiveSurface.PrimeCurve

variable {k : Type u} [Field k] {S : NormalProjectiveSurface k}

local instance (C : S.PrimeCurve) : IsDiscreteValuationRing (S.stalk C.genericPoint) :=
  C.genericPoint_isDiscreteValuationRing

/-- At the generic point of an actual prime curve the DVR property is
proved from normal surface geometry, so this isomorphism needs no extra
local-ring assumption. -/
def cartierOrderEquiv (C : S.PrimeCurve) :
    StalkCartierClass S.toScheme C.genericPoint ≃+ ℤ :=
  stalkCartierOrderEquiv S.toScheme C.genericPoint

@[simp]
theorem cartierOrderEquiv_class (C : S.PrimeCurve) (f : S.toScheme.functionFieldˣ) :
    C.cartierOrderEquiv
      (RingTheory.cartierLocalClassMap (S.stalk C.genericPoint) S.toScheme.functionField
        (Additive.ofMul f)) = C.order f := rfl

end NormalProjectiveSurface.PrimeCurve

end KltDP.Geometry

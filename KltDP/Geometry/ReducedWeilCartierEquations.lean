import KltDP.Geometry.EffectiveWeilCartierEquations
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Reduced quotients for the original multiplicity-one Cartier equations

The actual regular product of the selected height-one prime generators
is squarefree when the original divisor coefficients lie between zero
and one. Distinct height-one ideals prevent repeated prime factors.
Pinned radical-principal-ideal and reduced-quotient theorems then apply
to the literal quotient by this product.

For an original regular equation chart of an original Cartier divisor
on the normal surface, the original Cartier--Weil formula and the actual
stalk divisor coordinates give equal curve orders. The existing stalk
unit theorem derives the unit relating its coefficient germ to that
regular product. Thus the quotient by the original coefficient germ is
reduced; neither that conclusion nor the unit comparison is supplied.

Factoriality is required only at the selected actual stalk. Effectivity
and the upper bound one are on the original Weil coefficients. No field
characteristic condition is needed. Identifying the manuscript's node
divisor with these coefficients, and transporting the canonical Cartier
section to the original square-line-bundle atlas, remain separate.

Reuse: existing original UFD generators, stalk/curve order comparison,
regular divisor products and Cartier equations; pinned squarefree product,
radical principal ideal and quotient reducedness APIs. Newer Mathlib has
the same reusable algebraic implications, with changed foundational
typeclass/module syntax; no port or dependency modification is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.RingTheory

variable (R : Type u) [CommRing R] [IsDomain R]
  [IsNoetherianRing R] [UniqueFactorizationMonoid R]

/-- A finite set of distinct actual height-one ideals gives a squarefree
product of their original selected generators. -/
theorem heightOnePrimeGenerator_finset_squarefree (S : Finset (AffineHeightOnePrime R)) :
    Squarefree (∏ p ∈ S, heightOnePrimeGenerator R p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using (squarefree_one : Squarefree (1 : R))
  | @insert p S hp ih =>
      rw [Finset.prod_insert hp]
      have hprime := heightOnePrimeGenerator_prime R p
      refine squarefree_mul_iff.mpr ⟨hprime.irreducible.isRelPrime_iff_not_dvd.mpr ?_,
        hprime.squarefree, ih⟩
      apply hprime.not_dvd_finset_prod
      intro q hq hdvd
      have hmem : heightOnePrimeGenerator R q ∈ p.1.asIdeal := by
        rw [← heightOnePrimeGenerator_span R p]
        exact Ideal.mem_span_singleton.mpr hdvd
      have hqp : q = p := (heightOnePrimeGenerator_mem_iff R q p).mp hmem
      exact hp (hqp ▸ hq)

/-- Literal original coefficients between zero and one make the existing
regular divisor product squarefree. -/
theorem regularDivisorProduct_squarefree (D : AffineHeightOnePrime R →₀ ℤ)
    (hD : ∀ p, 0 ≤ D p) (hD_one : ∀ p, D p ≤ 1) :
    Squarefree (regularDivisorProduct R D) := by
  classical
  have hprod : regularDivisorProduct R D =
      ∏ p ∈ D.support, heightOnePrimeGenerator R p := by
    unfold regularDivisorProduct
    apply Finset.prod_congr rfl
    intro p hp
    have hn : D p ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hzero := hD p
    have hone := hD_one p
    have he : D p = 1 := by omega
    simp only [he, Int.toNat_one, pow_one]
  rw [hprod]
  exact heightOnePrimeGenerator_finset_squarefree R D.support

/-- The actual quotient by the original regular divisor product is
reduced, including the empty-support case. -/
theorem regularDivisorProduct_quotient_isReduced (D : AffineHeightOnePrime R →₀ ℤ)
    (hD : ∀ p, 0 ≤ D p) (hD_one : ∀ p, D p ≤ 1) :
    IsReduced (R ⧸ Ideal.span ({regularDivisorProduct R D} : Set R)) := by
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  exact isRadical_iff_span_singleton.mp (regularDivisorProduct_squarefree R D hD hD_one).isRadical

end KltDP.RingTheory

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

/-- Extension by zero to the actual stalk-prime carrier preserves the
original upper bound one, without merging distinct original curves. -/
theorem stalkDivisorCoordinates_le_one {U : X.toScheme.Opens} (hU : IsAffineOpen U)
    (x : U) (D : X.WeilDivisor) (hD : ∀ C, D C ≤ 1)
    (p : RingTheory.AffineHeightOnePrime (X.stalk x)) :
    X.stalkDivisorCoordinates hU x D p ≤ 1 := by
  classical
  let f : {C : X.PrimeCurve // (x : X.toScheme) ∈ C} ↪
      RingTheory.AffineHeightOnePrime (X.stalk x) :=
    ⟨fun C => C.1.stalkHeightOnePrime hU x C.2,
      PrimeCurve.stalkHeightOnePrime_injective hU x⟩
  change Finsupp.embDomain f
    (D.subtypeDomain (fun C => (x : X.toScheme) ∈ C)) p ≤ 1
  by_cases hp : p ∈ Set.range f
  · obtain ⟨C, rfl⟩ := hp
    rw [Finsupp.embDomain_apply]
    exact hD C.1
  · simpa only [Finsupp.embDomain_notin_range f _ p hp] using (zero_le_one : (0 : ℤ) ≤ 1)

/-- The quotient by the germ of an original regular Cartier coefficient
is reduced when the original Weil multiplicities are zero or one. The
unit relating it to the actual stalk product is derived from curve orders. -/
theorem regularCartierEquation_stalk_quotient_isReduced
    (E : CartierDivisor X.toScheme) (hE : EffectiveDivisor (X.cartierToWeilHom E))
    (hE_one : ∀ C, X.cartierToWeilHom E C ≤ 1)
    (c : RegularCartierEquationChart X.toScheme E) (x : c.chart.openSet)
    [UniqueFactorizationMonoid (X.stalk x)] :
    IsReduced (X.stalk x ⧸ Ideal.span
      ({X.toScheme.presheaf.germ c.chart.openSet x x.property c.coefficient} : Set (X.stalk x))) := by
  classical
  let A : X.toScheme.Opens := (X.toScheme.affineCover.map (x : X.toScheme)).opensRange
  have hA : IsAffineOpen A := isAffineOpen_opensRange (X.toScheme.affineCover.map (x : X.toScheme))
  let xa : A := ⟨x, X.toScheme.affineCover.covers x⟩
  let B := X.cartierToWeilHom E
  let D := X.stalkDivisorCoordinates hA xa B
  let P : X.stalk x := RingTheory.regularDivisorProduct (X.stalk x) D
  let f := X.stalkRationalEquation hA xa B
  let a : X.stalk x := X.toScheme.presheaf.germ c.chart.openSet x x.property c.coefficient
  have hP : algebraMap (X.stalk x) X.toScheme.functionField P =
      (f : X.toScheme.functionField) :=
    RingTheory.map_regularDivisorProduct (X.stalk x) X.toScheme.functionField D
      (X.stalkDivisorCoordinates_nonneg hA xa B hE)
  have ha : algebraMap (X.stalk x) X.toScheme.functionField a =
      (c.chart.equation : X.toScheme.functionField) :=
    (ConcreteCategory.congr_hom (X.toScheme.presheaf.germ_stalkSpecializes x.property
      ((genericPoint_spec X.toScheme).specializes trivial)) c.coefficient).trans c.germ_eq
  have horders (C : X.PrimeCurve) (hxC : (x : X.toScheme) ∈ C) :
      C.order c.chart.equation = C.order f :=
    (X.cartierToWeilHom_apply_of_equation E C c.chart.openSet
      (C.genericPoint_mem_of_mem x hxC) c.chart.equation c.chart.represents).symm.trans
      (X.stalkRationalEquation_order hA xa B C hxC).symm
  obtain ⟨b, hb⟩ := X.exists_stalk_unit_of_equal_curve_orders x c.chart.equation f horders
  have hbf : Units.map (algebraMap (X.stalk x) X.toScheme.functionField) b * f =
      c.chart.equation := by
    rw [hb]
    exact inv_mul_cancel_right c.chart.equation f
  have hbfval : algebraMap (X.stalk x) X.toScheme.functionField (b : X.stalk x) *
      (f : X.toScheme.functionField) = (c.chart.equation : X.toScheme.functionField) :=
    congrArg (fun z : X.toScheme.functionFieldˣ => (z : X.toScheme.functionField)) hbf
  have heq : a = (b : X.stalk x) * P := by
    apply IsFractionRing.injective (X.stalk x) X.toScheme.functionField
    rw [map_mul, ha, hP]
    exact hbfval.symm
  have hspan : Ideal.span ({a} : Set (X.stalk x)) = Ideal.span ({P} : Set (X.stalk x)) := by
    rw [heq]
    exact Ideal.span_singleton_mul_left_unit b.isUnit P
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  change (Ideal.span ({a} : Set (X.stalk x))).IsRadical
  rw [hspan]
  exact isRadical_iff_span_singleton.mp
    (RingTheory.regularDivisorProduct_squarefree (X.stalk x) D
      (X.stalkDivisorCoordinates_nonneg hA xa B hE)
      (X.stalkDivisorCoordinates_le_one hA xa B hE_one)).isRadical

end KltDP.Geometry.NormalProjectiveSurface

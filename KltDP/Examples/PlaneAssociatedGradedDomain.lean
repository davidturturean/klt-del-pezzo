import KltDP.RingTheory.AssociatedGradedPrime
import KltDP.RingTheory.LeadingFormAdditivity
import KltDP.RingTheory.MvPolynomialSharpProduct
import KltDP.Examples.FrobeniusStageDimension
import KltDP.Examples.FrobeniusBlowupChartIteration

/-!
# The associated graded ring of the polynomial plane at the origin is a domain

BRIEF39 task 1. This supplies the one remaining input of the F09 multiplicity chain:

  `IsDomain (AssociatedGraded (centerIdeal (k := k)))`

for the concrete plane `planeRing k = k[u][v]` at the blowup centre `centerIdeal = (u, v)`. With it,
`HasAdditiveAdicOrder centerIdeal` is **discharged rather than assumed**, for every consumer in this
thread, with no literature hypothesis.

## How it is assembled, and what it does not need

Three accepted or queued pieces meet here, and nothing new is proved about the geometry:

* `MvPolynomialSharpProduct.sharp_product` — over a domain, orders add sharply for the ideal generated
  by the variables. This is where `k[u,v]` being a domain enters, and the only place it does.
* `AssociatedGradedPrime.isDomain_of_sharpProduct` — sharp products make `I·R[It]` prime, hence `gr_I R`
  a domain. Proved through homogeneity of `I·R[It]`, not through a coefficient computation.
* The accepted `planeRingMvPolynomialEquiv : MvPolynomial (Fin 2) k ≃+* planeRing k`, transported here
  on the two variables.

**The regular-local theorem is not used and not proved**, per BRIEF38/39: `gr` of a regular local ring
being a polynomial ring is a separate, much larger item. Nothing here needs it. Equally, no initial-form
ring homomorphism `Θ` is constructed: the domain property is obtained from primality of a homogeneous
ideal, so `Function.Injective.isDomain` is not needed either.

## The transport

`planeRingMvPolynomialEquiv` is a composite of `finSuccEquiv` and `Polynomial.mapEquiv`, so its action
on the variables is computed rather than assumed: `X 0 ↦ Polynomial.X = vCoord` and
`X 1 ↦ Polynomial.C Polynomial.X = uCoord`. That identifies `varIdeal (Fin 2) k` with `centerIdeal`,
and membership in powers transports along the equivalence by `Ideal.symm_apply_mem_of_equiv_iff`.
-/

noncomputable section

universe u

namespace KltDP.Examples.PlaneAssociatedGradedDomain

open KltDP.RingTheory.AssociatedGradedRees
open KltDP.RingTheory.AssociatedGradedPrime
open KltDP.RingTheory.LocalAdicOrder
open KltDP.RingTheory.LeadingForm
open KltDP.RingTheory.MvPolynomialVarOrder
open KltDP.RingTheory.MvPolynomialSharpProduct
open KltDP.Examples.FrobeniusBlowupContact
open KltDP.Examples.FrobeniusStageDimension

variable {k : Type u} [Field k]

/-! ## The transport on the two variables -/

theorem equiv_X_zero :
    planeRingMvPolynomialEquiv (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) = vCoord := by
  simp [planeRingMvPolynomialEquiv, vCoord, MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]

theorem equiv_X_one :
    planeRingMvPolynomialEquiv (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) = uCoord := by
  -- The `Fin` rewrite is done in isolation: `simp` normalises `Fin.succ 0` straight back to `1`,
  -- so `finSuccEquiv_X_succ` must fire before `simp` ever runs.
  have key : (MvPolynomial.finSuccEquiv k 1) (MvPolynomial.X (1 : Fin 2))
      = Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
    rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl,
      MvPolynomial.finSuccEquiv_X_succ]
  simp [planeRingMvPolynomialEquiv, uCoord, key, MvPolynomial.finSuccEquiv_X_zero,
    Polynomial.map_C, Polynomial.map_X]

/-- The variable ideal of the two-variable polynomial ring is the blowup centre. -/
theorem map_varIdeal :
    Ideal.map
        (planeRingMvPolynomialEquiv (k := k) : MvPolynomial (Fin 2) k →+* planeRing k)
        (varIdeal (Fin 2) k)
      = centerIdeal := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, varIdeal]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · show planeRingMvPolynomialEquiv (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ∈ centerIdeal
      rw [equiv_X_zero]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    · show planeRingMvPolynomialEquiv (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ∈ centerIdeal
      rw [equiv_X_one]
      exact Ideal.subset_span (Set.mem_insert _ _)
  · refine Ideal.span_le.mpr ?_
    intro x hx
    rcases hx with rfl | hx
    · rw [← equiv_X_one]
      exact Ideal.mem_map_of_mem _ (X_mem_varIdeal 1)
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [← equiv_X_zero]
      exact Ideal.mem_map_of_mem _ (X_mem_varIdeal 0)

/-- Membership in the powers transports along the equivalence. -/
theorem mem_centerIdeal_pow_iff (n : ℕ) (z : planeRing k) :
    z ∈ centerIdeal ^ n ↔
      (planeRingMvPolynomialEquiv (k := k)).symm z ∈ varIdeal (Fin 2) k ^ n := by
  rw [← map_varIdeal, ← Ideal.map_pow]
  exact Ideal.symm_apply_mem_of_equiv_iff.symm

/-! ## Sharp products on the plane, and the domain instance -/

/-- **Orders add sharply at the blowup centre.** -/
theorem sharpProduct_centerIdeal : SharpProduct (centerIdeal (k := k)) := by
  intro a b x y hxa hxa' hyb hyb' hmem
  have hx1 := (mem_centerIdeal_pow_iff a x).mp hxa
  have hx2 : (planeRingMvPolynomialEquiv (k := k)).symm x ∉ varIdeal (Fin 2) k ^ (a + 1) :=
    fun h => hxa' ((mem_centerIdeal_pow_iff (a + 1) x).mpr h)
  have hy1 := (mem_centerIdeal_pow_iff b y).mp hyb
  have hy2 : (planeRingMvPolynomialEquiv (k := k)).symm y ∉ varIdeal (Fin 2) k ^ (b + 1) :=
    fun h => hyb' ((mem_centerIdeal_pow_iff (b + 1) y).mpr h)
  have hsharp := sharp_product hx1 hx2 hy1 hy2
  apply hsharp
  have hxy := (mem_centerIdeal_pow_iff (a + b + 1) (x * y)).mp hmem
  rwa [map_mul] at hxy

theorem centerIdeal_ne_top : (centerIdeal (k := k)) ≠ ⊤ :=
  Ideal.IsMaximal.ne_top inferInstance

/-- **The associated graded ring of the plane at the origin is a domain.** -/
instance isDomain_associatedGraded_centerIdeal :
    IsDomain (AssociatedGraded (centerIdeal (k := k))) :=
  isDomain_of_sharpProduct _ centerIdeal_ne_top sharpProduct_centerIdeal

/-! ## The consumer: multiplicity at the origin is additive -/

/-- **`HasAdditiveAdicOrder` is discharged for the plane at the blowup centre.** This was introduced as a
named `Prop` in `LocalAdicOrder` precisely because "the associated graded ring is a domain" could not be
stated at this pin. It can now be stated *and* proved here, so the order of vanishing at the origin is
**additive on products** as a theorem, with no literature hypothesis and no regular-local theorem. -/
theorem hasAdditiveAdicOrder_centerIdeal :
    HasAdditiveAdicOrder (centerIdeal (k := k)) :=
  hasAdditiveAdicOrder_of_isDomain centerIdeal centerIdeal_ne_top

/-- The additivity, in the form consumers use it. -/
theorem adicOrder_mul_centerIdeal {f g : planeRing k} (hf : f ≠ 0) (hg : g ≠ 0) :
    adicOrder (centerIdeal (k := k)) (f * g)
      = adicOrder (centerIdeal (k := k)) f + adicOrder (centerIdeal (k := k)) g :=
  hasAdditiveAdicOrder_centerIdeal f g hf hg

end KltDP.Examples.PlaneAssociatedGradedDomain

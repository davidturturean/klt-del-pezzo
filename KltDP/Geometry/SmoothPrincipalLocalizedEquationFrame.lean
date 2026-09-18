import KltDP.Geometry.SmoothPrincipalEquationFrame
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# An actual principal neighborhood with a branch-normalized base basis

At every prime containing the original regular branch equation, the
determinant supplied by the original smooth quotient avoids that prime.
Localizing the original ring at that exact determinant produces an
actual absolute differential basis beginning with the differential of
the original restricted branch coefficient. The differential comparison
is the pinned original localization map, not an assumed isomorphism.
-/

noncomputable section

open scoped TensorProduct

universe u

namespace KltDP.Geometry.SmoothPrincipalEquationFrame

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]

private theorem not_mem_of_quotient_unit (s r : R) (p : PrimeSpectrum R)
    (hs : s ∈ p.asIdeal) (hr : IsUnit (algebraMap R (R ⧸ Ideal.span {s}) r)) :
    r ∉ p.asIdeal := by
  letI : p.asIdeal.IsPrime := p.isPrime
  have hle : Ideal.span {s} ≤ p.asIdeal := (Ideal.span_singleton_le_iff_mem p.asIdeal).mpr hs
  have hu : IsUnit (Ideal.Quotient.mk p.asIdeal r) := by
    simpa only [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.factor_mk] using
      hr.map (Ideal.Quotient.factor hle)
  intro hmem
  exact hu.ne_zero (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)

/-- The original smooth principal branch gives a genuine principal
neighborhood and an actual ds-first differential basis on that ring. -/
theorem exists_localized_equation_basis (s : R)
    (hs : s ∈ nonZeroDivisors R)
    [Algebra.FormallySmooth k R]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k (R ⧸ Ideal.span {s})]
    (b : Basis (Fin 2) R (KaehlerDifferential k R))
    (p : PrimeSpectrum R) (hps : s ∈ p.asIdeal) :
    ∃ r : R, r ∉ p.asIdeal ∧
      ∃ c : Basis (Fin 2) (Localization.Away r)
          (KaehlerDifferential k (Localization.Away r)),
        c 0 = KaehlerDifferential.D k (Localization.Away r)
          (algebraMap R (Localization.Away r) s) := by
  obtain ⟨eta, heta⟩ := exists_form_with_unit_quotient_determinant k R s hs b
  let v : Fin 2 → KaehlerDifferential k R := ![KaehlerDifferential.D k R s, eta]
  let r : R := b.det v
  have hr : r ∉ p.asIdeal := not_mem_of_quotient_unit R s r p hps heta
  refine ⟨r, hr, ?_⟩
  let Q := Localization.Away r
  letI : Algebra.FormallyEtale R Q :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers r)
  have hunit : IsUnit ((b.baseChange Q).det (fun i => (1 : Q) ⊗ₜ[R] v i)) := by
    rw [← determinant_baseChange k R Q b v]
    exact IsLocalization.Away.algebraMap_isUnit r
  obtain ⟨hli, hspan⟩ := (is_basis_iff_det (b.baseChange Q)).mpr hunit
  let c : Basis (Fin 2) Q (Q ⊗[R] KaehlerDifferential k R) := Basis.mk hli hspan.ge
  have hc0 : c 0 = (1 : Q) ⊗ₜ[R] KaehlerDifferential.D k R s :=
    congr_fun (Basis.coe_mk hli hspan.ge) 0
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R Q
  refine ⟨c.map e, ?_⟩
  rw [Basis.map_apply, hc0]
  change KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R Q
      ((1 : Q) ⊗ₜ[R] KaehlerDifferential.D k R s) = _
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]

end KltDP.Geometry.SmoothPrincipalEquationFrame

#check @KltDP.Geometry.SmoothPrincipalEquationFrame.exists_localized_equation_basis
#print axioms KltDP.Geometry.SmoothPrincipalEquationFrame.exists_localized_equation_basis

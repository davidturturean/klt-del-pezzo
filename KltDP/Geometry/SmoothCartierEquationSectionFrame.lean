import KltDP.Geometry.GluedAdjunctionChartBasis
import KltDP.Geometry.SmoothPrincipalEquationFrame
import KltDP.Geometry.StandardSmoothNativeTopDifferential
import Mathlib.RingTheory.Etale.Kaehler

/-!
# A branch-adapted basis in the original smaller affine section ring

The existing simultaneous ambient/quotient chart supplies both smooth
dimensions. Its original principal equation produces a determinant that
does not vanish at the chosen branch prime. On the corresponding actual
basic open of the same scheme, the original restriction algebra and the
canonical Kähler localization map give a basis beginning with the
differential of the original restricted equation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

namespace KltDP.Geometry.SmoothCartierEquationSectionFrame

open GluedAdjunctionChartBasis GluedAdjunctionBasicOpenAlgebra
open GluedConormalBasicOpenLocalization SmoothPrincipalEquationFrame

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
variable (c : Chart f I) (s : Γ(X, c.U.1))

/-- A supplied original generator of the branch ideal, rather than a newly
chosen generator, becomes the first differential on an actual smaller chart. -/
theorem exists_basicOpen_basis (heq : I.ideal c.U = Ideal.span {s})
    (hs : s ∈ nonZeroDivisors Γ(X, c.U.1))
    (p : PrimeSpectrum Γ(X, c.U.1)) (hps : s ∈ p.asIdeal) :
    ∃ r : Γ(X, c.U.1), r ∉ p.asIdeal ∧
      letI : Algebra k Γ(X, (X.affineBasicOpen r).1) :=
        GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
      ∃ b : Basis (Fin 2) Γ(X, (X.affineBasicOpen r).1)
          (KaehlerDifferential k Γ(X, (X.affineBasicOpen r).1)),
        b 0 = KaehlerDifferential.D k Γ(X, (X.affineBasicOpen r).1)
          (sectionMap c.U r s) := by
  letI : Algebra k Γ(X, c.U.1) := GluedChartKaehlerPullback.chartAlgebra f c.U
  letI : Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, c.U.1) := c.ambient
  letI : Algebra.IsStandardSmooth k Γ(X, c.U.1) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth
      (R := k) (S := Γ(X, c.U.1)) 2
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1 k (Γ(X, c.U.1) ⧸ Ideal.span {s}) := by
    rw [← heq]
    exact c.curve
  obtain ⟨beta, _, _⟩ := AffineNativeTopDifferential.exists_coordinate_basis k Γ(X, c.U.1) 2
  obtain ⟨eta, heta⟩ := exists_form_with_unit_quotient_determinant k Γ(X, c.U.1) s hs beta
  let v : Fin 2 → KaehlerDifferential k Γ(X, c.U.1) :=
    ![KaehlerDifferential.D k Γ(X, c.U.1) s, eta]
  let r : Γ(X, c.U.1) := beta.det v
  have hr : r ∉ p.asIdeal := by
    letI : p.asIdeal.IsPrime := p.isPrime
    have hle : Ideal.span {s} ≤ p.asIdeal := (Ideal.span_singleton_le_iff_mem p.asIdeal).mpr hps
    have hu : IsUnit (Ideal.Quotient.mk p.asIdeal r) := by
      simpa only [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.factor_mk] using
        heta.map (Ideal.Quotient.factor hle)
    intro hmem
    exact hu.ne_zero (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  refine ⟨r, hr, ?_⟩
  let Q := Γ(X, (X.affineBasicOpen r).1)
  letI : Algebra k Q := GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
  letI := restrictionAlgebra c.U r
  letI := restrictionTower f c.U r
  letI : IsLocalization.Away r Q := c.U.2.isLocalization_basicOpen r
  letI : Algebra.FormallyEtale Γ(X, c.U.1) Q :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers r)
  have hunit : IsUnit ((beta.baseChange Q).det (fun i => (1 : Q) ⊗ₜ[Γ(X, c.U.1)] v i)) := by
    rw [← determinant_baseChange k Γ(X, c.U.1) Q beta v]
    exact IsLocalization.Away.algebraMap_isUnit r
  obtain ⟨hli, hspan⟩ := (is_basis_iff_det (beta.baseChange Q)).mpr hunit
  let b : Basis (Fin 2) Q (Q ⊗[Γ(X, c.U.1)] KaehlerDifferential k Γ(X, c.U.1)) :=
    Basis.mk hli hspan.ge
  have hb0 : b 0 = (1 : Q) ⊗ₜ[Γ(X, c.U.1)] KaehlerDifferential.D k Γ(X, c.U.1) s :=
    congr_fun (Basis.coe_mk hli hspan.ge) 0
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k Γ(X, c.U.1) Q
  refine ⟨b.map e, ?_⟩
  rw [Basis.map_apply, hb0]
  change KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k Γ(X, c.U.1) Q
    ((1 : Q) ⊗ₜ[Γ(X, c.U.1)] KaehlerDifferential.D k Γ(X, c.U.1) s) = _
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  rfl

end KltDP.Geometry.SmoothCartierEquationSectionFrame

#print axioms KltDP.Geometry.SmoothCartierEquationSectionFrame.exists_basicOpen_basis

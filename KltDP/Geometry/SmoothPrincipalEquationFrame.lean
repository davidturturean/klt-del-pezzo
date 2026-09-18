import KltDP.RingTheory.SmoothPrincipalConormalDeterminant
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# A branch-normalized base frame modulo the original smooth branch

The proved split conormal sequence gives a basis of the actual pulled
base differentials on the original principal quotient, with first vector
the actual d(s). Its second vector lifts through the original quotient
tensor map. Thus the determinant of (d(s), eta) is a unit modulo the
original branch ideal. A subsequent original principal localization
makes it a basis upstairs; no normalized-base-frame premise is introduced.
-/

noncomputable section

open scoped TensorProduct

universe u

namespace KltDP.Geometry.SmoothPrincipalEquationFrame

open KltDP.LinearAlgebra.SplitConormalDeterminant
open KltDP.RingTheory.SmoothPrincipalConormalDeterminant

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]

/-- Determinants of actual base-changed vectors use the original scalar map. -/
theorem determinant_baseChange (Q : Type u) [CommRing Q] [Algebra R Q]
    (b : Basis (Fin 2) R (KaehlerDifferential k R))
    (v : Fin 2 → KaehlerDifferential k R) :
    algebraMap R Q (b.det v) =
      (b.baseChange Q).det (fun i => (1 : Q) ⊗ₜ[R] v i) := by
  simp only [Basis.det_apply]
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Basis.toMatrix_apply, Basis.baseChange_repr_tmul, Algebra.smul_def]

/-- The original smooth principal branch supplies a second actual form
whose determinant with d(s) is invertible on the branch quotient. -/
theorem exists_form_with_unit_quotient_determinant (s : R)
    (hs : s ∈ nonZeroDivisors R)
    [Algebra.FormallySmooth k R]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k (R ⧸ Ideal.span {s})]
    (b : Basis (Fin 2) R (KaehlerDifferential k R)) :
    ∃ eta : KaehlerDifferential k R,
      IsUnit (algebraMap R (R ⧸ Ideal.span {s})
        (b.det ![KaehlerDifferential.D k R s, eta])) := by
  let J : Ideal R := Ideal.span {s}
  let ds : J := ⟨s, Ideal.subset_span (Set.mem_singleton s)⟩
  letI : Algebra.IsStandardSmooth k (R ⧸ J) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth
      (R := k) (S := R ⧸ J) 1
  let c : Basis (Fin 2) (R ⧸ J) ((R ⧸ J) ⊗[R] KaehlerDifferential k R) :=
    basis (equationDifferential k R J ds)
      (KaehlerDifferential.mapBaseChange k R (R ⧸ J))
      (equationDifferential_exact k R J ds rfl)
      (equationDifferential_injective k R J ds rfl hs)
      (quotientSection k R J) (quotientSection_property k R J)
      (standardSmoothQuotientFrame k R J)
  have hc0 : c 0 = (1 : R ⧸ J) ⊗ₜ[R] KaehlerDifferential.D k R s := by
    dsimp only [c]
    rw [basis_zero, equationDifferential_one]
  obtain ⟨eta, heta⟩ := TensorProduct.mk_surjective (R := R) (S := R ⧸ J) (M := KaehlerDifferential k R)
    (show Function.Surjective (algebraMap R (R ⧸ J)) from Ideal.Quotient.mk_surjective) (c 1)
  have hc : (fun i : Fin 2 =>
      (1 : R ⧸ J) ⊗ₜ[R] (![KaehlerDifferential.D k R s, eta] i)) = c := by
    funext i
    fin_cases i
    · exact hc0.symm
    · exact heta
  refine ⟨eta, ?_⟩
  change IsUnit (algebraMap R (R ⧸ J) (b.det ![KaehlerDifferential.D k R s, eta]))
  rw [determinant_baseChange k R (R ⧸ J), hc]
  exact (b.baseChange (R ⧸ J)).isUnit_det c

end KltDP.Geometry.SmoothPrincipalEquationFrame

#check @KltDP.Geometry.SmoothPrincipalEquationFrame.exists_form_with_unit_quotient_determinant
#print axioms KltDP.Geometry.SmoothPrincipalEquationFrame.exists_form_with_unit_quotient_determinant

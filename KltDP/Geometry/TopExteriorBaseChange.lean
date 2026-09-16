import KltDP.Compatibility.ExteriorPowerBaseChange
import KltDP.Geometry.AffineTopDifferentialFrame
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Canonical scalar extension of the top exterior power

For an actual basis `b : Basis (Fin n) A M`, the canonical comparison
`B ⊗[A] (⋀[A]^n M) →ₗ[B] ⋀[B]^n (B ⊗[A] M)` is an equivalence.

The determinant frames and the scalar-extended basis provide an auxiliary
equivalence. It agrees with the canonical comparison on every tensor of
the original basis wedge. The original determinant frame and tensor
balancing extend that equality to the entire source. The final equivalence
therefore stores the canonical comparison as its forward map.

All scalar actions come from the supplied `Algebra A B`. No flatness,
invertibility of two, or separate exterior-frame premise is required.
-/

noncomputable section

open scoped TensorProduct

universe u v w

namespace KltDP.Geometry.TopExteriorBaseChange

open AffineTopDifferentialFrame

variable {A : Type u} [CommRing A] {M : Type w} [AddCommGroup M] [Module A M]
variable (B : Type v) [CommRing B] [Algebra A B] {n : ℕ} (b : Basis (Fin n) A M)

/-- The two actual determinant frames give an auxiliary equivalence. -/
private def frameEquiv : B ⊗[A] (⋀[A]^n M) ≃ₗ[B] (⋀[B]^n (B ⊗[A] M)) :=
  (LinearEquiv.baseChange A B (⋀[A]^n M) A (determinantEquiv b)).trans
    ((TensorProduct.AlgebraTensorModule.rid A B B).trans
      (determinantEquiv (b.baseChange B)).symm)

/-- Both maps send the original basis wedge to the wedge of the actual
scalar-extended basis, with the same arbitrary coefficient. -/
private theorem frameEquiv_basis_tmul (r : B) :
    frameEquiv B b (r ⊗ₜ[A] exteriorPower.ιMulti A n b) =
      KltDP.Compatibility.ExteriorPowerBaseChange.map A B n M
        (r ⊗ₜ[A] exteriorPower.ιMulti A n b) := by
  change (determinantEquiv (b.baseChange B)).symm
      (determinantEquiv b (exteriorPower.ιMulti A n b) • r) = _
  rw [determinantEquiv_basis_wedge, one_smul, determinantEquiv_symm_apply,
    KltDP.Compatibility.ExteriorPowerBaseChange.map_tmul_ιMulti]
  exact congrArg
    (fun v : Fin n → B ⊗[A] M => r • exteriorPower.ιMulti B n v)
    (funext fun i => Basis.baseChange_apply B b i)

/-- The original determinant frame expresses every source exterior
element as a scalar times its basis wedge. Tensor balancing therefore
extends agreement on the basis wedge to equality of the entire maps. -/
private theorem frameEquiv_toLinearMap :
    (frameEquiv B b).toLinearMap =
      KltDP.Compatibility.ExteriorPowerBaseChange.map A B n M := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro r x
  obtain ⟨a, rfl⟩ := (determinantEquiv b).symm.surjective x
  simpa only [determinantEquiv_symm_apply, TensorProduct.tmul_smul] using
    frameEquiv_basis_tmul B b (a • r)

/-- The canonical comparison is an equivalence in the degree equal to
the size of the given actual basis. Its forward map is the original
comparison, whose bijectivity follows from the proved equality above. -/
def equiv : B ⊗[A] (⋀[A]^n M) ≃ₗ[B] (⋀[B]^n (B ⊗[A] M)) :=
  LinearEquiv.ofBijective
    (KltDP.Compatibility.ExteriorPowerBaseChange.map A B n M) (by
      rw [← frameEquiv_toLinearMap B b]
      exact (frameEquiv B b).bijective)

/-- The stored linear map is exactly the original canonical comparison. -/
theorem equiv_toLinearMap :
    (equiv B b).toLinearMap =
      KltDP.Compatibility.ExteriorPowerBaseChange.map A B n M := rfl

/-- The equivalence retains the canonical formula on every original pure wedge. -/
theorem equiv_tmul_ιMulti (r : B) (v : Fin n → M) :
    equiv B b (r ⊗ₜ[A] exteriorPower.ιMulti A n v) =
      r • exteriorPower.ιMulti B n (fun i => 1 ⊗ₜ[A] v i) :=
  KltDP.Compatibility.ExteriorPowerBaseChange.map_tmul_ιMulti A B n M r v

/-- In particular, a canonically extended pure wedge is the wedge of
the canonically extended vectors. -/
theorem equiv_one_tmul_ιMulti (v : Fin n → M) :
    equiv B b (1 ⊗ₜ[A] exteriorPower.ιMulti A n v) =
      exteriorPower.ιMulti B n (fun i => 1 ⊗ₜ[A] v i) :=
  KltDP.Compatibility.ExteriorPowerBaseChange.map_one_tmul_ιMulti A B n M v

end KltDP.Geometry.TopExteriorBaseChange

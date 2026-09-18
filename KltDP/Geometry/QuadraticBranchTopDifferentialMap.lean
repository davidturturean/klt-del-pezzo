import KltDP.Geometry.QuadraticBranchDifferentialBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The actual determinant map in the produced quadratic branch frames

The source frame is the base change of the given original base basis.
The target frame is the proved original quadratic differential basis.
In these frames the actual exterior-square differential is multiplication
by 2t. This is an equality on the whole actual exterior module, not just
on a chosen pure wedge and not an assumed determinant factorization.
-/

noncomputable section

open scoped TensorProduct
open KltDP.Geometry.AffineTopDifferentialFrame

universe u

namespace KltDP.Geometry.QuadraticCover

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] [Nontrivial R]

/-- The original map takes the actual pulled-back basis wedge to twice
the original root times the constructed cover basis wedge. -/
theorem exteriorDifferential_basis_wedge (s : R)
    (b : Basis (Fin 2) R (KaehlerDifferential k R))
    (hb : b 0 = KaehlerDifferential.D k R s) :
    exteriorPower.map 2 (KaehlerDifferential.mapBaseChange k R (CoverAlgebra s))
        (exteriorPower.ιMulti (CoverAlgebra s) 2 (b.baseChange (CoverAlgebra s))) =
      (2 * root s) • exteriorPower.ιMulti (CoverAlgebra s) 2
        (branchDifferentialBasis k R s b hb) := by
  have hsource : (b.baseChange (CoverAlgebra s) :
      Fin 2 → CoverAlgebra s ⊗[R] KaehlerDifferential k R) =
      ![1 ⊗ₜ[R] KaehlerDifferential.D k R s, 1 ⊗ₜ[R] b 1] := by
    funext i
    fin_cases i <;> simp [Basis.baseChange_apply, hb]
  have htarget : (branchDifferentialBasis k R s b hb :
      Fin 2 → KaehlerDifferential k (CoverAlgebra s)) =
      ![KaehlerDifferential.D k (CoverAlgebra s) (root s),
        KaehlerDifferential.mapBaseChange k R (CoverAlgebra s) (1 ⊗ₜ[R] b 1)] := by
    funext i
    fin_cases i <;> simp
  rw [hsource, htarget]
  exact exteriorDifferential_branch k R s (1 ⊗ₜ[R] b 1)

/-- The actual determinant coordinate map is exactly multiplication by
twice the original quadratic root, on every original top differential. -/
theorem exteriorDifferential_frame_map (s : R)
    (b : Basis (Fin 2) R (KaehlerDifferential k R))
    (hb : b 0 = KaehlerDifferential.D k R s) :
    (determinantEquiv (branchDifferentialBasis k R s b hb)).toLinearMap.comp
        (exteriorPower.map 2 (KaehlerDifferential.mapBaseChange k R (CoverAlgebra s))) =
      (2 * root s) • (determinantEquiv (b.baseChange (CoverAlgebra s))).toLinearMap := by
  apply LinearMap.ext
  intro omega
  obtain ⟨a, rfl⟩ := (determinantEquiv (b.baseChange (CoverAlgebra s))).symm.surjective omega
  change determinantEquiv (branchDifferentialBasis k R s b hb)
      (exteriorPower.map 2 (KaehlerDifferential.mapBaseChange k R (CoverAlgebra s))
        ((determinantEquiv (b.baseChange (CoverAlgebra s))).symm a)) =
    (2 * root s) • determinantEquiv (b.baseChange (CoverAlgebra s))
      ((determinantEquiv (b.baseChange (CoverAlgebra s))).symm a)
  rw [LinearEquiv.apply_symm_apply, determinantEquiv_symm_apply, map_smul,
    exteriorDifferential_basis_wedge, map_smul, map_smul, determinantEquiv_basis_wedge]
  simp only [smul_eq_mul, mul_one, one_mul, mul_comm]

end KltDP.Geometry.QuadraticCover

#check @KltDP.Geometry.QuadraticCover.exteriorDifferential_frame_map
#print axioms KltDP.Geometry.QuadraticCover.exteriorDifferential_frame_map

import KltDP.Geometry.QuadraticCanonicalRootTensor
import KltDP.Geometry.QuadraticBranchTopDifferentialMap

/-!
# The normalized actual canonical factor on a quadratic branch chart

The original root ideal and the proved actual differential bases give an
isomorphism from the pulled base top forms to the root ideal tensored
with the original cover top forms. Its composite with the original
ideal inclusion is exactly the original exterior differential map.
The base frame begins with the original d(s); its geometric producer
and the original chart transport/gluing remain separate obligations.
-/

noncomputable section

open scoped TensorProduct
open KltDP.Geometry.AffineTopDifferentialFrame

universe u

namespace KltDP.Geometry.QuadraticCover

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] [Nontrivial R]

/-- The image of two is a unit in the same original quadratic quotient. -/
def coverTwoUnit (s : R) (h2 : IsUnit (2 : R)) : (CoverAlgebra s)ˣ :=
  (show IsUnit (2 : CoverAlgebra s) by
    simpa only [map_ofNat] using h2.map (algebraMap R (CoverAlgebra s))).unit

@[simp]
theorem coverTwoUnit_val (s : R) (h2 : IsUnit (2 : R)) :
    (coverTwoUnit R s h2 : CoverAlgebra s) = 2 :=
  IsUnit.unit_spec _

/-- The original differential factor through the actual root-ideal tensor. -/
def branchCanonicalFactorEquiv (s : R) (hs : s ∈ nonZeroDivisors R)
    (h2 : IsUnit (2 : R)) (b : Basis (Fin 2) R (KaehlerDifferential k R))
    (hb : b 0 = KaehlerDifferential.D k R s) :
    (⋀[CoverAlgebra s]^2 (CoverAlgebra s ⊗[R] KaehlerDifferential k R)) ≃ₗ[CoverAlgebra s]
      rootIdeal s ⊗[CoverAlgebra s] coverTopDifferentials k R s :=
  (determinantEquiv (b.baseChange (CoverAlgebra s))).trans
    ((determinantEquiv (branchDifferentialBasis k R s b hb)).symm.trans
      ((LinearEquiv.smulOfUnit (M := coverTopDifferentials k R s) (coverTwoUnit R s h2)).trans
        (rootTopTensorFrame k R s hs)))

/-- The produced isomorphism factors exactly the original absolute
exterior map; it is not merely an isomorphism between abstract free lines. -/
theorem branchCanonicalFactorEquiv_inclusion (s : R) (hs : s ∈ nonZeroDivisors R)
    (h2 : IsUnit (2 : R)) (b : Basis (Fin 2) R (KaehlerDifferential k R))
    (hb : b 0 = KaehlerDifferential.D k R s) :
    (rootTopTensorInclusion k R s).comp (branchCanonicalFactorEquiv k R s hs h2 b hb).toLinearMap =
      exteriorPower.map 2 (KaehlerDifferential.mapBaseChange k R (CoverAlgebra s)) := by
  apply LinearMap.ext
  intro omega
  have hfactor : rootTopTensorInclusion k R s
        (branchCanonicalFactorEquiv k R s hs h2 b hb omega) =
      (2 * root s) • (determinantEquiv (branchDifferentialBasis k R s b hb)).symm
        (determinantEquiv (b.baseChange (CoverAlgebra s)) omega) := by
    change rootTopTensorInclusion k R s
        (rootTopTensorFrame k R s hs ((coverTwoUnit R s h2 : CoverAlgebra s) •
          (determinantEquiv (branchDifferentialBasis k R s b hb)).symm
            (determinantEquiv (b.baseChange (CoverAlgebra s)) omega))) = _
    rw [rootTopTensorFrame_inclusion, coverTwoUnit_val, smul_smul, mul_comm (root s) 2]
  change rootTopTensorInclusion k R s
      (branchCanonicalFactorEquiv k R s hs h2 b hb omega) = _
  rw [hfactor]
  apply (determinantEquiv (branchDifferentialBasis k R s b hb)).injective
  rw [map_smul, LinearEquiv.apply_symm_apply]
  exact (LinearMap.congr_fun (exteriorDifferential_frame_map k R s b hb) omega).symm

end KltDP.Geometry.QuadraticCover

#check @KltDP.Geometry.QuadraticCover.branchCanonicalFactorEquiv_inclusion
#print axioms KltDP.Geometry.QuadraticCover.branchCanonicalFactorEquiv_inclusion

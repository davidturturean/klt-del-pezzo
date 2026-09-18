import KltDP.Geometry.QuadraticRootConormalCoordinates
import KltDP.Geometry.AffinePrincipalIdealTildeFrame
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.RingTheory.Kaehler.Basic

/-!
# The original ramification ideal tensored with actual top differentials

The original regular root supplies the existing principal-ideal frame.
Tensoring it with the actual absolute top differentials produces the
normalized root-ideal tensor frame. Its composition with the original
ideal inclusion is proved to multiply by that same original root.
-/

noncomputable section

open scoped TensorProduct

universe u

namespace KltDP.Geometry.QuadraticCover

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]

abbrev coverTopDifferentials (s : R) :=
  ⋀[CoverAlgebra s]^2 (KaehlerDifferential k (CoverAlgebra s))

/-- The actual root-ideal inclusion tensored with the actual exterior module. -/
def rootTopTensorInclusion (s : R) :
    rootIdeal s ⊗[CoverAlgebra s] coverTopDifferentials k R s →ₗ[CoverAlgebra s]
      coverTopDifferentials k R s :=
  (TensorProduct.lid (CoverAlgebra s) (coverTopDifferentials k R s)).toLinearMap.comp
    (TensorProduct.map (rootIdeal s).subtype LinearMap.id)

theorem rootTopTensorInclusion_tmul (s : R) (r : rootIdeal s)
    (omega : coverTopDifferentials k R s) :
    rootTopTensorInclusion k R s (r ⊗ₜ[CoverAlgebra s] omega) =
      (r : CoverAlgebra s) • omega := by
  simp only [rootTopTensorInclusion, LinearMap.comp_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul]
  rfl

/-- The original regular root gives an actual tensor equivalence. -/
def rootTopTensorFrame (s : R) (hs : s ∈ nonZeroDivisors R) :
    coverTopDifferentials k R s ≃ₗ[CoverAlgebra s]
      rootIdeal s ⊗[CoverAlgebra s] coverTopDifferentials k R s :=
  (TensorProduct.lid (CoverAlgebra s) (coverTopDifferentials k R s)).symm.trans
    (TensorProduct.congr
      (AffinePrincipalIdealTildeFrame.equationEquiv (rootIdeal s) (rootIdealGenerator s)
        rfl (root_mem_nonZeroDivisors s hs))
      (LinearEquiv.refl (CoverAlgebra s) (coverTopDifferentials k R s)))

theorem rootTopTensorFrame_apply (s : R) (hs : s ∈ nonZeroDivisors R)
    (omega : coverTopDifferentials k R s) :
    rootTopTensorFrame k R s hs omega = rootIdealGenerator s ⊗ₜ[CoverAlgebra s] omega := by
  rw [rootTopTensorFrame, LinearEquiv.trans_apply, TensorProduct.lid_symm_apply,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  congr 1
  apply Subtype.ext
  exact one_mul (root s)

/-- The original inclusion retains the root multiplier under the produced frame. -/
theorem rootTopTensorFrame_inclusion (s : R) (hs : s ∈ nonZeroDivisors R)
    (omega : coverTopDifferentials k R s) :
    rootTopTensorInclusion k R s (rootTopTensorFrame k R s hs omega) = root s • omega := by
  simp only [rootTopTensorFrame_apply, rootTopTensorInclusion_tmul, rootIdealGenerator]

end KltDP.Geometry.QuadraticCover

#print axioms KltDP.Geometry.QuadraticCover.rootTopTensorFrame_inclusion

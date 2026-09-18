import KltDP.Geometry.UnimodularPicardFiniteFree
import KltDP.Lattices.PerfectIntegralGram
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# An actual finite Picard basis from the original unimodularity theorem

The existing original Picard-to-numerical equivalence transfers finite
freeness. Mathlib's finite basis and the original dual equivalence then
give determinant of absolute value one for the same intersection form.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry
open LinearMap
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)
  (hS : ∀ s : S.Point, RegularPoint S.toScheme s)

/-- The supplied original Picard unimodularity constructs an actual finite
basis with the exact original Gram determinant of absolute value one. -/
theorem exists_picard_basis_det_natAbs_one_of_picardUnimodular
    (hU : S.PicardUnimodular hS) :
    ∃ n : ℕ, ∃ b : Basis (Fin n) ℤ (Additive S.toScheme.Pic),
      (BilinForm.toMatrix b (S.integralPicardIntersectionBilinForm hS)).det.natAbs = 1 := by
  obtain ⟨hfree, hfinite⟩ := S.picard_free_and_finite_of_picardUnimodular hS hU
  letI : Module.Free ℤ (Additive S.toScheme.Pic) := hfree
  letI : Module.Finite ℤ (Additive S.toScheme.Pic) := hfinite
  let b := Module.finBasis ℤ (Additive S.toScheme.Pic)
  refine ⟨_, b, ?_⟩
  exact KltDP.Lattices.PerfectIntegralGram.toMatrix_det_natAbs_eq_one b
    (S.integralPicardIntersectionBilinForm hS)
    (S.integralPicardIntersectionBilinForm_bijective_of_picardUnimodular hS hU)

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.exists_picard_basis_det_natAbs_one_of_picardUnimodular
#print axioms KltDP.Geometry.NormalProjectiveSurface.exists_picard_basis_det_natAbs_one_of_picardUnimodular

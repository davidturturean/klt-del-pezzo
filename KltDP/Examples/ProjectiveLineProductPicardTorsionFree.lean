import KltDP.Examples.ProjectiveLineProductPicardCoordinates
import KltDP.Geometry.NumericalSpaceRank
import Mathlib.Algebra.Order.Group.Basic

/-! The original integral ruling equivalence detects torsion in the original Picard group. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry
universe u

namespace KltDP.Examples.ProjectiveLineProductPicardTorsionFree

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusStageZeroProjective
open ProjectiveLineProductPicardGeneration

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem picardTorsionFree : (projectiveProductSurface (k := k)).PicardTorsionFree := by
  intro p n hn hp
  apply (rulingPicardEquiv (k := k)).symm.injective
  rw [map_zero]
  have h : n • (rulingPicardEquiv (k := k)).symm p = 0 := by
    rw [← map_nsmul, hp, map_zero]
  apply Prod.ext
  · apply nsmul_right_injective (Nat.ne_of_gt hn)
    have hx := congrArg (fun z : ℤ × ℤ => z.1) h
    simpa only [nsmul_zero] using hx
  · apply nsmul_right_injective (Nat.ne_of_gt hn)
    have hy := congrArg (fun z : ℤ × ℤ => z.2) h
    simpa only [nsmul_zero] using hy

end KltDP.Examples.ProjectiveLineProductPicardTorsionFree

#check @KltDP.Examples.ProjectiveLineProductPicardTorsionFree.picardTorsionFree
#print axioms KltDP.Examples.ProjectiveLineProductPicardTorsionFree.picardTorsionFree

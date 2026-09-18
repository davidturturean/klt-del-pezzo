import KltDP.Geometry.ActualExceptionalNumericalComplement
import Mathlib.LinearAlgebra.Projection

/-!
# The original numerical projection away from exceptional curves

The complement is proved from the actual surface and morphism. The original
numerical space therefore has a linear projection whose kernel is precisely
the span of the original exceptional classes and whose range is precisely
their original degree-zero subspace. An actual Cartier correction is identified
with this projection by its original class difference and degree equations.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.ActualExceptionalNumerical

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π]
  (hπ : π ≫ X.structureMorphism = S.structureMorphism) (hbir : IsBirationalScheme π)
  (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)

include hπ hbir

/-- The actual numerical projection onto the original exceptional orthogonal subspace. -/
def projection : S.NumericalClassGroup →ₗ[ℚ] S.NumericalClassGroup :=
  (exceptionalOrthogonal π).subtype.comp
    ((exceptionalOrthogonal π).linearProjOfIsCompl (exceptionalSpan π hregular)
      (isCompl_exceptionalSpan_orthogonal π hπ hbir hregular).symm)

theorem projection_mem (c : S.NumericalClassGroup) :
    projection π hπ hbir hregular c ∈ exceptionalOrthogonal π :=
  ((exceptionalOrthogonal π).linearProjOfIsCompl (exceptionalSpan π hregular)
    (isCompl_exceptionalSpan_orthogonal π hπ hbir hregular).symm c).property

theorem projection_eq_self (c : S.NumericalClassGroup)
    (hc : c ∈ exceptionalOrthogonal π) : projection π hπ hbir hregular c = c := by
  exact congrArg (fun x : exceptionalOrthogonal π => (x : S.NumericalClassGroup))
    (Submodule.linearProjOfIsCompl_apply_left
      (isCompl_exceptionalSpan_orthogonal π hπ hbir hregular).symm ⟨c, hc⟩)

theorem projection_eq_zero_of_mem (c : S.NumericalClassGroup)
    (hc : c ∈ exceptionalSpan π hregular) : projection π hπ hbir hregular c = 0 := by
  exact congrArg (fun x : exceptionalOrthogonal π => (x : S.NumericalClassGroup))
    (Submodule.linearProjOfIsCompl_apply_right'
      (isCompl_exceptionalSpan_orthogonal π hπ hbir hregular).symm c hc)

/-- The correction is an actual class in the original exceptional span. -/
theorem sub_projection_mem (c : S.NumericalClassGroup) :
    c - projection π hπ hbir hregular c ∈ exceptionalSpan π hregular := by
  let d : exceptionalSpan π hregular :=
    (exceptionalSpan π hregular).linearProjOfIsCompl (exceptionalOrthogonal π)
      (isCompl_exceptionalSpan_orthogonal π hπ hbir hregular) c
  have hsum : projection π hπ hbir hregular c + (d : S.NumericalClassGroup) = c :=
    Submodule.linear_proj_add_linearProjOfIsCompl_eq_self
      (isCompl_exceptionalSpan_orthogonal π hπ hbir hregular).symm c
  have heq : c - projection π hπ hbir hregular c = (d : S.NumericalClassGroup) := by
    apply sub_eq_iff_eq_add.mpr
    exact hsum.symm.trans (add_comm _ _)
  rw [heq]
  exact d.property

/-- Original degree zero and an actual exceptional difference identify the correction. -/
theorem projection_eq_of_sub_mem (c d : S.NumericalClassGroup)
    (hd : d ∈ exceptionalOrthogonal π) (hcd : c - d ∈ exceptionalSpan π hregular) :
    projection π hπ hbir hregular c = d := by
  have h := projection_eq_zero_of_mem π hπ hbir hregular (c - d) hcd
  rw [map_sub, projection_eq_self π hπ hbir hregular d hd] at h
  exact sub_eq_zero.mp h

theorem range_projection : LinearMap.range (projection π hπ hbir hregular) =
    exceptionalOrthogonal π := by
  ext c
  constructor
  · rintro ⟨d, rfl⟩
    exact projection_mem π hπ hbir hregular d
  · intro hc
    exact ⟨c, projection_eq_self π hπ hbir hregular c hc⟩

theorem ker_projection : LinearMap.ker (projection π hπ hbir hregular) =
    exceptionalSpan π hregular := by
  ext c
  change projection π hπ hbir hregular c = 0 ↔ c ∈ exceptionalSpan π hregular
  constructor
  · intro hc
    have h := sub_projection_mem π hπ hbir hregular c
    simpa only [hc, sub_zero] using h
  · exact projection_eq_zero_of_mem π hπ hbir hregular c

end KltDP.Geometry.ActualExceptionalNumerical

#check @KltDP.Geometry.ActualExceptionalNumerical.projection
#check @KltDP.Geometry.ActualExceptionalNumerical.projection_eq_of_sub_mem
#print axioms KltDP.Geometry.ActualExceptionalNumerical.range_projection
#print axioms KltDP.Geometry.ActualExceptionalNumerical.ker_projection

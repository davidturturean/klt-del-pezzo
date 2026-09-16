import KltDP.Geometry.TensorInvertibleSheaf
import KltDP.Geometry.InvertibleSheaf

/-!
# The tensor product of two invertible sheaves is invertible

For invertible sheaves `L`, `M` on a scheme `X`, the skeleton class of `L ⊗ M` is the product of
two units of the monoidal skeleton (pinned `Skeleton.toSkeleton_tensorObj`), so `L ⊗ M` is
invertible by the accepted criterion `SchemeTensorPairing.isInvertible_of_isUnit_toSkeleton`;
`tensorInvertibleSheaf L M : InvertibleSheaf X` packages it with `obj = L.obj ⊗ M.obj` (`rfl`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace KltDP.Geometry.InvertibleSheafTensor

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance invertibleSheafTensorMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {X : Scheme.{u}}

/-- The skeleton class of `L ⊗ M` is a unit. -/
theorem isUnit_toSkeleton_tensor (L M : InvertibleSheaf X) :
    IsUnit (toSkeleton (L.obj ⊗ M.obj)) := by
  rw [Skeleton.toSkeleton_tensorObj]
  exact ((SchemeTensorPairing.isInvertible_iff_isUnit_toSkeleton L.obj).mp L.property).mul
    ((SchemeTensorPairing.isInvertible_iff_isUnit_toSkeleton M.obj).mp M.property)

/-- `L ⊗ M` is invertible. -/
theorem isInvertible_tensor (L M : InvertibleSheaf X) :
    KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) (L.obj ⊗ M.obj) :=
  SchemeTensorPairing.isInvertible_of_isUnit_toSkeleton _ (isUnit_toSkeleton_tensor L M)

/-- The tensor product of two invertible sheaves, as an invertible sheaf. -/
def tensorInvertibleSheaf (L M : InvertibleSheaf X) : InvertibleSheaf X :=
  ⟨L.obj ⊗ M.obj, isInvertible_tensor L M⟩

@[simp]
theorem tensorInvertibleSheaf_obj (L M : InvertibleSheaf X) :
    (tensorInvertibleSheaf L M).obj = L.obj ⊗ M.obj := rfl

end KltDP.Geometry.InvertibleSheafTensor

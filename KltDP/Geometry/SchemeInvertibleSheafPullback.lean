import KltDP.Geometry.SchemePicardPullback
import KltDP.Geometry.TensorInvertibleSheaf

/-!
# Pullback of actual locally free rank-one sheaves

Actual pullback preserves tensor-invertible classes by its proved tensor
and unit comparisons. The established equivalence between those classes
and the original local rank-one predicate then supplies local freeness
of the actual pulled-back sheaf. No local freeness result is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- Pullback along any actual scheme morphism preserves the original
locally free rank-one predicate. -/
theorem schemeModulePullback_isInvertible (M : X.Modules)
    (hM : KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) M) :
    KltDP.SheafOfModules.IsInvertible (R := Y.ringCatSheaf)
      ((schemeModulePullback f).obj M) := by
  letI := Scheme.Modules.monoidalCategory X
  letI := Scheme.Modules.monoidalCategory Y
  apply SchemeTensorPairing.isInvertible_of_isUnit_toSkeleton
  change IsUnit (schemeModulePullbackClassHom f (toSkeleton M))
  exact ((SchemeTensorPairing.isInvertible_iff_isUnit_toSkeleton M).mp hM).map
    (schemeModulePullbackClassHom f)

/-- The actual pulled-back module sheaf with its proved local rank-one property. -/
def pullbackInvertibleSheaf (L : InvertibleSheaf X) : InvertibleSheaf Y :=
  ⟨(schemeModulePullback f).obj L.obj,
    schemeModulePullback_isInvertible f L.obj L.property⟩

/-- The class of the actual pulled-back line bundle is the pullback of
its original class in the existing Picard group. -/
theorem schemePicardPullbackHom_toPic (L : InvertibleSheaf X) :
    schemePicardPullbackHom f L.toPic = (pullbackInvertibleSheaf f L).toPic := by
  letI := Scheme.Modules.monoidalCategory X
  letI := Scheme.Modules.monoidalCategory Y
  apply Units.ext
  change schemeModulePullbackClassMap f (L.toPic : Skeleton X.Modules) =
    ((pullbackInvertibleSheaf f L).toPic : Skeleton Y.Modules)
  rw [InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val]
  rfl

end KltDP.Geometry

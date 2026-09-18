import KltDP.Geometry.SchemePullbackRestrictIso
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! Abstract composition of the two existing pullback-projection laws. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.EqualityAppendixPullbackProjection

variable {S T X : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ X)

theorem proper [IsProper f] [IsProper g] : IsProper (pullback.fst f g ≫ f) := by
  letI : IsProper (pullback.fst f g) :=
    MorphismProperty.pullback_fst (P := @IsProper) _ _ inferInstance
  infer_instance

theorem restrict_isIso (V : X.Opens) [IsIso (f ∣_ V)] [IsIso (g ∣_ V)] :
    IsIso ((pullback.fst f g ≫ f) ∣_ V) := by
  letI := KltDP.Geometry.isIso_pullback_fst_restrict f g V
  rw [morphismRestrict_comp]
  infer_instance

end KltDP.Examples.EqualityAppendixPullbackProjection

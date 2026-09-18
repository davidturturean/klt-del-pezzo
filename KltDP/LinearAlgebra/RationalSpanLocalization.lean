import KltDP.Geometry.CartierPicardEndpointRational
import Mathlib.RingTheory.Localization.Module

/-!
An injective additive map into a rational vector space identifies its
rational span as localization of the original group at the nonzero
integers. The existing positive-multiple criterion proves surjectivity;
the other two localization axioms use scalar inverses and injectivity.
This is an adapter to Mathlib's existing localization universal property.
-/

noncomputable section

universe u v

namespace KltDP.LinearAlgebra.RationalSpanLocalization

variable {A : Type u} [AddCommGroup A]
variable {V : Type v} [AddCommGroup V] [Module ℚ V] (f : A →+ V)

/-- The original additive map into its actual rational span. -/
def spanMap : A →ₗ[ℤ] Submodule.span ℚ (Set.range f) where
  toFun a := ⟨f a, Submodule.subset_span ⟨a, rfl⟩⟩
  map_add' a b := Subtype.ext (f.map_add a b)
  map_smul' z a := Subtype.ext (f.map_zsmul a z)

/-- The rational span is the localization of the original group when
the original additive map is injective. -/
theorem spanMap_isLocalizedModule (hf : Function.Injective f) :
    IsLocalizedModule (nonZeroDivisors ℤ) (spanMap f) where
  map_units s := by
    rw [← (Algebra.lsmul ℤ (A := ℚ) ℤ (Submodule.span ℚ (Set.range f))).commutes]
    exact (IsLocalization.map_units ℚ s).map _
  surj' x := by
    obtain ⟨n, hn, a, ha⟩ :=
      (KltDP.Geometry.mem_ratSpan_range_iff f x.val).mp x.property
    let s : nonZeroDivisors ℤ :=
      ⟨(n : ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr
        (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hn))⟩
    refine ⟨(a, s), ?_⟩
    apply Subtype.ext
    change (n : ℤ) • x.val = f a
    simpa only [natCast_zsmul] using ha.symm
  exists_of_eq {a b} h := by
    have hab : a = b := hf (congrArg Subtype.val h)
    subst b
    exact ⟨1, rfl⟩

end KltDP.LinearAlgebra.RationalSpanLocalization

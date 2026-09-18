import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.Algebra.Module.End

/-!
# Finite index from an injective rational spanning map

For the supplied integer submodule, full rational span under the supplied
injective map makes the actual additive quotient torsion. Finite generation
then makes that quotient finite. The supplied integer-module structure is
compared explicitly with the canonical integer action before passing to
the additive finite-generation and torsion APIs.
-/

set_option autoImplicit false

namespace KltDP.Lattices.RationalSpanFiniteIndex

variable {M V : Type*} [AddCommGroup M] [mM : Module ℤ M]
  [AddCommGroup V] [Module ℚ V] [Module.Finite ℤ M]

/-- A submodule whose image spans the rational target of an injective
integer-linear map has finite index in the original integer module. -/
theorem finiteIndex_of_span_eq_top
    (f : M →ₗ[ℤ] V) (hf : Function.Injective f) (Γ : Submodule ℤ M)
    (hspan : Submodule.span ℚ (f '' (Γ : Set M)) = ⊤) :
    Γ.toAddSubgroup.FiniteIndex := by
  letI : AddGroup.FG M := Module.Finite.iff_addGroup_fg.mp <| by
    have hfin : @Module.Finite ℤ M _ _ mM := inferInstance
    simpa only [(AddCommGroup.uniqueIntModule (M := M)).uniq mM] using hfin
  have htors : AddMonoid.IsTorsion (M ⧸ Γ.toAddSubgroup) := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientAddGroup.mk'_surjective Γ.toAddSubgroup q
    have hm : f m ∈ Submodule.span ℚ (f '' (Γ : Set M)) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨y, hy, a, ha⟩ :=
      (IsLocalization.mem_span_iff (nonZeroDivisors ℤ)).mp hm
    rw [← Submodule.map_span, Submodule.span_eq] at hy
    obtain ⟨n, hn, rfl⟩ := Submodule.mem_map.mp hy
    have hmul : f ((a : ℤ) • m) = f n := by
      calc
        f ((a : ℤ) • m) = (a : ℤ) • f m :=
          map_zsmul f.toAddMonoidHom (a : ℤ) m
        _ = (algebraMap ℤ ℚ (a : ℤ)) • f m :=
          (IsScalarTower.algebraMap_smul ℚ (a : ℤ) (f m)).symm
        _ = f n := by
          rw [ha, smul_smul, IsLocalization.mk'_spec', map_one, one_smul]
    refine isOfFinAddOrder_iff_zsmul_eq_zero.mpr
      ⟨(a : ℤ), nonZeroDivisors.coe_ne_zero a, ?_⟩
    calc
      (a : ℤ) • (QuotientAddGroup.mk' Γ.toAddSubgroup) m =
          (QuotientAddGroup.mk' Γ.toAddSubgroup) ((a : ℤ) • m) :=
        (map_zsmul (QuotientAddGroup.mk' Γ.toAddSubgroup) (a : ℤ) m).symm
      _ = 0 := (QuotientAddGroup.eq_zero_iff (N := Γ.toAddSubgroup)
        ((a : ℤ) • m)).2 ((hf hmul).symm ▸ hn)
  letI : Finite (M ⧸ Γ.toAddSubgroup) :=
    AddCommGroup.finite_of_fg_torsion (M ⧸ Γ.toAddSubgroup) htors
  exact AddSubgroup.finiteIndex_of_finite_quotient

end KltDP.Lattices.RationalSpanFiniteIndex

#check @KltDP.Lattices.RationalSpanFiniteIndex.finiteIndex_of_span_eq_top
#print axioms KltDP.Lattices.RationalSpanFiniteIndex.finiteIndex_of_span_eq_top

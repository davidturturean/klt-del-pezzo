import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# A spanning family of the full rank over a domain

This algebraic step retains the given vectors.  Rank-nullity makes the
kernel of their presentation have rank zero; as a submodule of a free
module over a domain, that kernel is torsion-free and hence zero.
-/

noncomputable section

universe u

namespace KltDP.Geometry.DomainBasisOfSpanningRank

variable {A M : Type u} [CommRing A] [IsDomain A]
  [AddCommGroup M] [Module A M]

/-- A finite spanning family whose size equals the module rank is independent
over a domain. No torsion-freeness hypothesis on the target module is needed. -/
theorem linearIndependent {n : ℕ} (v : Fin n → M)
    (hspan : Submodule.span A (Set.range v) = ⊤)
    (hrank : Module.rank A M = n) : LinearIndependent A v := by
  let f := Finsupp.linearCombination A v
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact hspan
  have hrel := LinearMap.rank_eq_of_surjective hsurj
  have hfree : Module.rank A (Fin n →₀ A) = n := by
    simpa only [Cardinal.mk_fin, Cardinal.lift_natCast] using rank_finsupp_self A (Fin n)
  rw [hfree, hrank] at hrel
  have hker : Module.rank A (LinearMap.ker f) = 0 := by
    apply (Cardinal.add_nat_inj n).mp
    simpa only [zero_add, add_zero, add_comm] using hrel.symm
  have hzero : Subsingleton (LinearMap.ker f) := rank_zero_iff.mp hker
  exact linearIndependent_iff_ker.mpr (Submodule.subsingleton_iff_eq_bot.mp hzero)

/-- The resulting basis has exactly the original spanning vectors. -/
def basis {n : ℕ} (v : Fin n → M)
    (hspan : Submodule.span A (Set.range v) = ⊤)
    (hrank : Module.rank A M = n) : Basis (Fin n) A M :=
  Basis.mk (linearIndependent v hspan hrank) (by rw [hspan])

@[simp] theorem basis_apply {n : ℕ} (v : Fin n → M)
    (hspan : Submodule.span A (Set.range v) = ⊤)
    (hrank : Module.rank A M = n) (i : Fin n) :
    basis v hspan hrank i = v i :=
  Basis.mk_apply _ _ i

end KltDP.Geometry.DomainBasisOfSpanningRank

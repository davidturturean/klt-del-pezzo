import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Dimension bounds for actual orthogonal subspaces and node images

An actual nondegenerate bilinear form on a finite-dimensional vector space
identifies the space with its dual. Restriction to a subspace is injective,
so its dual coannihilator has the expected complementary dimension. This
proves the dimension bound for orthogonal subspaces and for the range of
the actual linear-combination map of a supplied finite family of vectors.

Only left nondegeneracy of the bilinear form is required. Neither symmetry
nor reflexivity is assumed, and the field may have characteristic two.
Mathlib's `B.orthogonal W` consists of the vectors `u` satisfying
`B w u = 0` for every `w` in `W`; the orientation is explicit below.

This supplies a linear-algebra adapter for the Picard-code image bound in
manuscript `lem:picard-parity`. It does not construct the intersection form
modulo two, prove that form nondegenerate, or infer the codimension of the
reduced sublattice from its integral index. Those are separate obligations.
-/

namespace KltDP.Lattices.OrthogonalRank

open Module
open scoped BigOperators

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V]

/-- The orthogonal dimension formula without a symmetry or reflexivity
hypothesis: nondegeneracy makes the map into the dual injective. -/
theorem finrank_orthogonal (B : LinearMap.BilinForm k V)
    (hB : B.Nondegenerate) (W : Submodule k V) :
    finrank k (B.orthogonal W) = finrank k V - finrank k W := by
  have hinj : Function.Injective B := LinearMap.ker_eq_bot.mp hB.ker_eq_bot
  have hrestrict : Function.Injective (B.domRestrict W) := by
    intro x y hxy
    apply Subtype.ext
    exact hinj hxy
  have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (LinearMap.range (B.domRestrict W))
  rw [B.toLin_restrict_range_dualCoannihilator_eq_orthogonal W,
    LinearMap.finrank_range_of_inj hrestrict] at hdim
  exact Nat.eq_sub_of_add_eq' hdim

/-- An actual inclusion into the orthogonal subspace gives the codimension
bound; the bound is a conclusion, not an input. -/
theorem finrank_le_codim_of_le_orthogonal (B : LinearMap.BilinForm k V)
    (hB : B.Nondegenerate) {U W : Submodule k V}
    (hUW : U ≤ B.orthogonal W) :
    finrank k U ≤ finrank k V - finrank k W := by
  calc
    finrank k U ≤ finrank k (B.orthogonal W) := Submodule.finrank_mono hUW
    _ = finrank k V - finrank k W := finrank_orthogonal B hB W

/-- The same bound stated using the actual quotient by the subspace. -/
theorem finrank_le_finrank_quotient_of_le_orthogonal
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate)
    {U W : Submodule k V} (hUW : U ≤ B.orthogonal W) :
    finrank k U ≤ finrank k (V ⧸ W) := by
  rw [Submodule.finrank_quotient]
  exact finrank_le_codim_of_le_orthogonal B hB hUW

/-- Pairing zero in the orientation used by Mathlib's orthogonal subspace. -/
theorem finrank_le_codim_of_right_pairing_zero (B : LinearMap.BilinForm k V)
    (hB : B.Nondegenerate) (U W : Submodule k V)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, B w u = 0) :
    finrank k U ≤ finrank k V - finrank k W := by
  apply finrank_le_codim_of_le_orthogonal B hB
  intro u hu w hw
  exact hUW u hu w hw

/-- The other pairing orientation gives the same dimension bound by
flipping the form; finite-dimensional nondegeneracy survives this flip. -/
theorem finrank_le_codim_of_pairing_zero (B : LinearMap.BilinForm k V)
    (hB : B.Nondegenerate) (U W : Submodule k V)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, B u w = 0) :
    finrank k U ≤ finrank k V - finrank k W := by
  apply finrank_le_codim_of_right_pairing_zero B.flip hB.flip U W
  intro u hu w hw
  exact hUW u hu w hw

section Ranges

variable {X Y : Type*} [AddCommGroup X] [Module k X]
variable [AddCommGroup Y] [Module k Y]

/-- Perpendicular actual images of linear maps have complementary rank
bounds, without any injectivity or finite-dimensional domain premise. -/
theorem finrank_range_le_codim_range (B : LinearMap.BilinForm k V)
    (hB : B.Nondegenerate) (f : X →ₗ[k] V) (g : Y →ₗ[k] V)
    (hfg : ∀ x y, B (f x) (g y) = 0) :
    finrank k (LinearMap.range f) ≤
      finrank k V - finrank k (LinearMap.range g) := by
  apply finrank_le_codim_of_pairing_zero B hB
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  exact hfg x y

end Ranges

section NodeImages

variable {ι : Type*} [Fintype ι]

omit [FiniteDimensional k V] in
/-- If each supplied vector is perpendicular to an actual subspace, the
range of its actual finite linear-combination map lies in the orthogonal. -/
theorem range_linearCombination_le_orthogonal (B : LinearMap.BilinForm k V)
    (w : ι → V) (W : Submodule k V)
    (hW : ∀ i v, v ∈ W → B v (w i) = 0) :
    LinearMap.range (Fintype.linearCombination k w) ≤ B.orthogonal W := by
  rintro _ ⟨x, rfl⟩ v hv
  change B v (Fintype.linearCombination k w x) = 0
  rw [Fintype.linearCombination_apply, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [B.smul_right, hW i v hv, mul_zero]

/-- The node-image rank is bounded by the codimension of an actual
subspace to which all the supplied vectors are perpendicular. -/
theorem finrank_range_linearCombination_le_codim
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate)
    (w : ι → V) (W : Submodule k V)
    (hW : ∀ i v, v ∈ W → B v (w i) = 0) :
    finrank k (LinearMap.range (Fintype.linearCombination k w)) ≤
      finrank k V - finrank k W :=
  finrank_le_codim_of_le_orthogonal B hB
    (range_linearCombination_le_orthogonal B w W hW)

/-- A quotient formulation for combining with a bound proved from an
actual lattice index. No such index bound is assumed in this theorem. -/
theorem finrank_range_linearCombination_le_finrank_quotient
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate)
    (w : ι → V) (W : Submodule k V)
    (hW : ∀ i v, v ∈ W → B v (w i) = 0) :
    finrank k (LinearMap.range (Fintype.linearCombination k w)) ≤
      finrank k (V ⧸ W) :=
  finrank_le_finrank_quotient_of_le_orthogonal B hB
    (range_linearCombination_le_orthogonal B w W hW)

variable {Y : Type*} [AddCommGroup Y] [Module k Y]

omit [FiniteDimensional k V] in
/-- Generator pairings against an actual spanning or inclusion map prove
the orthogonality of the entire node image to that map's actual range. -/
theorem range_linearCombination_le_orthogonal_range
    (B : LinearMap.BilinForm k V) (w : ι → V) (g : Y →ₗ[k] V)
    (hg : ∀ i y, B (g y) (w i) = 0) :
    LinearMap.range (Fintype.linearCombination k w) ≤
      B.orthogonal (LinearMap.range g) := by
  apply range_linearCombination_le_orthogonal B w (LinearMap.range g)
  rintro i _ ⟨y, rfl⟩
  exact hg i y

/-- The node-image bound against the actual range of a supplied map. -/
theorem finrank_range_linearCombination_le_codim_range
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate)
    (w : ι → V) (g : Y →ₗ[k] V)
    (hg : ∀ i y, B (g y) (w i) = 0) :
    finrank k (LinearMap.range (Fintype.linearCombination k w)) ≤
      finrank k V - finrank k (LinearMap.range g) :=
  finrank_le_codim_of_le_orthogonal B hB
    (range_linearCombination_le_orthogonal_range B w g hg)

end NodeImages

end KltDP.Lattices.OrthogonalRank

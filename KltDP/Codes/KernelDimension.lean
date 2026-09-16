import KltDP.Codes.DoublyEven
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Dimensions and relations in binary kernels

This module supplies finite-dimensional linear algebra for manuscript
`lem:picard-index` and `lem:picard-parity` (`source/manuscript.tex`,
lines 1342–1428). The spaces, linear maps, kernels, vectors and finite subsets
below are actual mathematical objects, independent of any geometric model.

For a map from `ι → ZMod 2` whose image has dimension at most `s`, rank-nullity
gives kernel dimension at least `Fintype.card ι - s`. A strict inequality
`s < Fintype.card ι` gives a nonzero kernel vector, hence a nonempty subset
relation among a supplied family of vectors. The short doubly-even-code
results then give the dimension contradictions and all-ones relation used in
the manuscript's three- and four-node cases.

Remaining lattice adapter: construct the map using actual isolated-node
classes in the integral Picard group modulo twice that group; prove the bound
on its image rank from the full lattice index; identify its kernel with
integral half-sums; and prove the Riemann--Roch weight divisibility property.
None of those statements is assumed as a geometric structure field or claimed
as a consequence of this module. In particular the finite 2-primary group
`Pic(S)/Γ` need not itself be an `F₂` vector space.
-/

namespace KltDP.Codes

section RankNullity

variable {ι 𝕜 V : Type*} [Fintype ι] [DivisionRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-- Rank-nullity for a map whose source is a finite coordinate space. The
codomain need not be finite dimensional. -/
theorem finrank_kernel_eq_card_sub_finrank_range (f : (ι → 𝕜) →ₗ[𝕜] V) :
    Module.finrank 𝕜 (LinearMap.ker f) = Fintype.card ι - Module.finrank 𝕜 (LinearMap.range f) := by
  have h := f.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at h
  omega

/-- An upper bound on the image dimension gives a lower bound on the actual
kernel dimension, including the case of an empty coordinate type. -/
theorem card_sub_le_finrank_kernel_of_finrank_range_le
    (f : (ι → 𝕜) →ₗ[𝕜] V) {s : ℕ} (h : Module.finrank 𝕜 (LinearMap.range f) ≤ s) :
    Fintype.card ι - s ≤ Module.finrank 𝕜 (LinearMap.ker f) := by
  rw [finrank_kernel_eq_card_sub_finrank_range]
  omega

/-- A finite-dimensional target is a sufficient image-rank bound. -/
theorem card_sub_finrank_le_finrank_kernel [FiniteDimensional 𝕜 V]
    (f : (ι → 𝕜) →ₗ[𝕜] V) :
    Fintype.card ι - Module.finrank 𝕜 V ≤ Module.finrank 𝕜 (LinearMap.ker f) :=
  card_sub_le_finrank_kernel_of_finrank_range_le f (LinearMap.range f).finrank_le

/-- A strict rank deficit yields a nonzero vector annihilated by the map. -/
theorem exists_ne_zero_map_eq_zero_of_finrank_range_lt_card
    (f : (ι → 𝕜) →ₗ[𝕜] V) (h : Module.finrank 𝕜 (LinearMap.range f) < Fintype.card ι) :
    ∃ x : ι → 𝕜, x ≠ 0 ∧ f x = 0 := by
  have hpos : 0 < Module.finrank 𝕜 (LinearMap.ker f) := by
    rw [finrank_kernel_eq_card_sub_finrank_range]
    omega
  have hker : (LinearMap.ker f) ≠ ⊥ := by
    intro hz
    rw [hz, finrank_bot] at hpos
    exact (lt_irrefl 0) hpos
  obtain ⟨x, hx, hx0⟩ := (LinearMap.ker f).ne_bot_iff.mp hker
  exact ⟨x, hx0, LinearMap.mem_ker.mp hx⟩

end RankNullity

section BinaryRelations

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module (ZMod 2) V]

/-- The binary relations among a family of actual vectors. -/
def binaryRelationCode (v : ι → V) : Submodule (ZMod 2) (BinaryWord ι) :=
  (LinearMap.ker (Fintype.linearCombination (ZMod 2) v))

/-- Membership says precisely that the indicated binary linear combination
of the supplied vectors is zero. -/
theorem mem_binaryRelationCode_iff (v : ι → V) (x : BinaryWord ι) :
    x ∈ binaryRelationCode v ↔ ∑ i, x i • v i = 0 := by
  rfl

theorem binaryRelationCode_finrank_ge_card_sub
    (v : ι → V) {s : ℕ}
    (h : Module.finrank (ZMod 2) (LinearMap.range (Fintype.linearCombination (ZMod 2) v)) ≤ s) :
    Fintype.card ι - s ≤ Module.finrank (ZMod 2) (binaryRelationCode v) :=
  card_sub_le_finrank_kernel_of_finrank_range_le _ h

/-- A nonzero binary relation has an actual nonempty set of indices whose
vectors sum to zero. No support or half-sum witness is stored in the input. -/
theorem exists_nonempty_sum_eq_zero_of_binary_relation
    (v : ι → V) {x : BinaryWord ι} (hx0 : x ≠ 0)
    (hx : x ∈ binaryRelationCode v) :
    ∃ J : Finset ι, J.Nonempty ∧ ∑ i ∈ J, v i = 0 := by
  classical
  have hsupport : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (funext h)
  obtain ⟨i, hi⟩ := hsupport
  refine ⟨Finset.univ.filter (fun j => x j ≠ 0),
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩, ?_⟩
  have hsum : ∑ j, x j • v j = 0 := (mem_binaryRelationCode_iff v x).mp hx
  calc
    ∑ j ∈ Finset.univ.filter (fun j => x j ≠ 0), v j = ∑ j, x j • v j := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : x j = 0
      · simp [hj]
      · simp [hj, binary_eq_one_of_ne_zero hj]
    _ = 0 := hsum

/-- Too many binary generators for the dimension of their span force a
nonempty vanishing subset. The conclusion concerns the supplied vectors. -/
theorem exists_nonempty_sum_eq_zero_of_binary_rank_lt
    (v : ι → V)
    (h : Module.finrank (ZMod 2) (LinearMap.range (Fintype.linearCombination (ZMod 2) v)) <
      Fintype.card ι) :
    ∃ J : Finset ι, J.Nonempty ∧ ∑ i ∈ J, v i = 0 := by
  obtain ⟨x, hx0, hx⟩ :=
    exists_ne_zero_map_eq_zero_of_finrank_range_lt_card
      (Fintype.linearCombination (ZMod 2) v) h
  exact exists_nonempty_sum_eq_zero_of_binary_relation v hx0 hx

/-- If the codomain is finite dimensional, its dimension alone gives a
sufficient criterion for a nonempty vanishing subset. -/
theorem exists_nonempty_sum_eq_zero_of_card_gt_finrank [FiniteDimensional (ZMod 2) V]
    (v : ι → V) (h : Module.finrank (ZMod 2) V < Fintype.card ι) :
    ∃ J : Finset ι, J.Nonempty ∧ ∑ i ∈ J, v i = 0 :=
  exists_nonempty_sum_eq_zero_of_binary_rank_lt v
    (lt_of_le_of_lt (LinearMap.range (Fintype.linearCombination (ZMod 2) v)).finrank_le h)

end BinaryRelations

section ShortKernels

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module (ZMod 2) V]

/-- At length three, an image rank at most two cannot have a doubly-even
kernel. This is the purely linear-algebraic contradiction in the `(36,3)` case. -/
theorem not_doublyEven_kernel_of_card_eq_three_of_range_le_two
    (f : BinaryWord ι →ₗ[ZMod 2] V) (hι : Fintype.card ι = 3)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range f) ≤ 2) : ¬ DoublyEvenCode (LinearMap.ker f) := by
  intro hC
  have hzero : Module.finrank (ZMod 2) (LinearMap.ker f) = 0 :=
    doublyEvenCode_finrank_eq_zero_of_card_lt_four (LinearMap.ker f) hC (by omega)
  have hlower : Fintype.card ι - 2 ≤ Module.finrank (ZMod 2) (LinearMap.ker f) :=
    card_sub_le_finrank_kernel_of_finrank_range_le f hrank
  omega

/-- At length four, image rank at most two forces a kernel too large to be
doubly even. This is the algebraic contradiction in the `(36,4)` case. -/
theorem not_doublyEven_kernel_of_card_eq_four_of_range_le_two
    (f : BinaryWord ι →ₗ[ZMod 2] V) (hι : Fintype.card ι = 4)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range f) ≤ 2) : ¬ DoublyEvenCode (LinearMap.ker f) := by
  intro hC
  have hupper : Module.finrank (ZMod 2) (LinearMap.ker f) ≤ 1 :=
    doublyEvenCode_finrank_le_one_of_card_eq_four (LinearMap.ker f) hC hι
  have hlower : Fintype.card ι - 2 ≤ Module.finrank (ZMod 2) (LinearMap.ker f) :=
    card_sub_le_finrank_kernel_of_finrank_range_le f hrank
  omega

/-- At length four, a doubly-even kernel with image rank at most three
contains the all-ones vector. This is the algebraic part of the `(24,4)` case. -/
theorem ones_mem_kernel_of_doublyEven_of_card_eq_four_of_range_le_three
    (f : BinaryWord ι →ₗ[ZMod 2] V) (hC : DoublyEvenCode (LinearMap.ker f))
    (hι : Fintype.card ι = 4) (hrank : Module.finrank (ZMod 2) (LinearMap.range f) ≤ 3) :
    ones ι ∈ (LinearMap.ker f) := by
  have hlower : Fintype.card ι - 3 ≤ Module.finrank (ZMod 2) (LinearMap.ker f) :=
    card_sub_le_finrank_kernel_of_finrank_range_le f hrank
  have hpos : 0 < Module.finrank (ZMod 2) (LinearMap.ker f) := by omega
  exact ones_mem_of_doublyEvenCode_of_card_eq_four_of_finrank_pos (LinearMap.ker f) hC hι hpos

/-- In a family of four vectors with doubly-even relations and image rank at
most three, the sum of all four supplied vectors is zero. -/
theorem sum_eq_zero_of_doublyEven_relations_of_card_eq_four_of_range_le_three
    (v : ι → V) (hC : DoublyEvenCode (binaryRelationCode v))
    (hι : Fintype.card ι = 4)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (Fintype.linearCombination (ZMod 2) v)) ≤ 3) :
    ∑ i, v i = 0 := by
  have h := ones_mem_kernel_of_doublyEven_of_card_eq_four_of_range_le_three
    (Fintype.linearCombination (ZMod 2) v) hC hι hrank
  have hsum := (mem_binaryRelationCode_iff v (ones ι)).mp h
  simpa only [ones, one_smul] using hsum

end ShortKernels

end KltDP.Codes

import KltDP.Codes.KernelDimension
import KltDP.Codes.NodeParity
import Mathlib.Algebra.Module.ZMod

/-!
# The binary code of integral node half-sums

Given actual vectors `w i` in an additive group `M`, this module constructs
the quotient `M / (2 M)` as an actual quotient group, equips it with its
`ZMod 2` module structure, and defines a linear map from binary words by
sending the standard basis vectors to the classes of `w i`. Its kernel is
the code of integral node half-sums. Membership is proved equivalent to
the existence of a vector whose double is the sum over the word's support.
The linear-code closure is therefore proved by the quotient and kernel
constructions, rather than assumed.

For an integer-valued bilinear form, pairwise orthogonal vectors of square
`-2`, and a characteristic vector perpendicular to those vectors, the code
is proved doubly even using `NodeParity`. This supplies the algebraic code
construction in manuscript `lem:picard-parity`, lines 1388–1428.

No freeness, torsion-freeness, finite generation or geometric interpretation
of `M` is needed here. Identifying `M` with the actual integral Picard group,
constructing its intersection form and canonical characteristic vector,
and proving the image-rank bound from a full sublattice index remain separate
obligations. No Riemann--Roch theorem about surfaces is assumed or claimed.
-/

namespace KltDP.Codes

section QuotientByTwo

variable (M : Type*) [AddCommGroup M]

/-- The subgroup consisting exactly of doubles of elements of the group. -/
def twiceSubgroup : AddSubgroup M where
  carrier := {x | ∃ m : M, m + m = x}
  zero_mem' := ⟨0, zero_add 0⟩
  add_mem' := by
    rintro a b ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨x + y, ?_⟩
    calc
      (x + y) + (x + y) = (x + x) + (y + y) := by abel
      _ = a + b := by rw [hx, hy]
  neg_mem' := by
    rintro a ⟨x, hx⟩
    refine ⟨-x, ?_⟩
    simpa only [neg_add] using congrArg Neg.neg hx

/-- Reduction of the actual additive group modulo its subgroup of doubles. -/
abbrev ModTwo := M ⧸ twiceSubgroup M

/-- Every quotient class is killed by two, giving the quotient its binary
vector-space structure without a freeness or finite-generation assumption. -/
instance modTwoModule : Module (ZMod 2) (ModTwo M) :=
  QuotientAddGroup.zmodModule (n := 2) (H := twiceSubgroup M) (fun x => by
    exact ⟨x, by simp only [two_nsmul]⟩)

/-- The canonical additive quotient map. -/
def modTwoMk : M →+ ModTwo M := QuotientAddGroup.mk' (twiceSubgroup M)

variable {M}

/-- A quotient class vanishes exactly when it has an integral half. -/
theorem modTwoMk_eq_zero_iff (x : M) :
    modTwoMk M x = 0 ↔ ∃ m : M, m + m = x := by
  exact QuotientAddGroup.eq_zero_iff x

end QuotientByTwo

section IntegralCode

variable {M ι : Type*} [AddCommGroup M] [Fintype ι]

/-- The actual binary linear map sending each node label to its class modulo
twice the ambient group. -/
def integralNodeMap (w : ι → M) : BinaryWord ι →ₗ[ZMod 2] ModTwo M :=
  Fintype.linearCombination (ZMod 2) (fun i => modTwoMk M (w i))

/-- The code is the kernel of reduction modulo twice the group. -/
def integralNodeCode (w : ι → M) : Submodule (ZMod 2) (BinaryWord ι) :=
  (LinearMap.ker (integralNodeMap w))

@[simp]
theorem integralNodeMap_single [DecidableEq ι] (w : ι → M) (i : ι) :
    integralNodeMap w (Pi.single i 1) = modTwoMk M (w i) := by
  simp [integralNodeMap]

/-- Binary coefficients are exactly the support indicators, so the linear
map is the quotient class of the actual unweighted support sum. -/
theorem integralNodeMap_apply (w : ι → M) (x : BinaryWord ι) :
    integralNodeMap w x = modTwoMk M
      (∑ i ∈ Finset.univ.filter (fun j => x j ≠ 0), w i) := by
  classical
  simp only [integralNodeMap, Fintype.linearCombination_apply, map_sum,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x i = 0
  · simp [hi]
  · simp [hi, binary_eq_one_of_ne_zero hi]

/-- Membership is precisely two-divisibility of the actual support sum in
the ambient integer module; no rational class is substituted for it. -/
theorem mem_integralNodeCode_iff [Module ℤ M] (w : ι → M) (x : BinaryWord ι) :
    x ∈ integralNodeCode w ↔ ∃ m : M, (2 : ℤ) • m =
      ∑ i ∈ Finset.univ.filter (fun j => x j ≠ 0), w i := by
  change integralNodeMap w x = 0 ↔ _
  rw [integralNodeMap_apply, modTwoMk_eq_zero_iff]
  simp only [two_zsmul]

/-- The all-ones codeword is equivalent to divisibility of the sum of all
the supplied node vectors. -/
theorem ones_mem_integralNodeCode_iff [Module ℤ M] (w : ι → M) :
    ones ι ∈ integralNodeCode w ↔ ∃ m : M, (2 : ℤ) • m = ∑ i, w i := by
  simpa [ones] using mem_integralNodeCode_iff w (ones ι)

/-- Rank-nullity now applies to this constructed integral code. The bound on
the quotient image is a stated linear-algebra premise, not a claimed lattice
index consequence. -/
theorem integralNodeCode_finrank_ge_card_sub (w : ι → M) {s : ℕ}
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (integralNodeMap w)) ≤ s) :
    Fintype.card ι - s ≤ Module.finrank (ZMod 2) (integralNodeCode w) :=
  card_sub_le_finrank_kernel_of_finrank_range_le _ hrank

/-- An actual rank deficit forces a nonempty integral node half-sum. -/
theorem exists_nonempty_integral_half_sum_of_rank_lt [Module ℤ M]
    (w : ι → M)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (integralNodeMap w)) < Fintype.card ι) :
    ∃ J : Finset ι, J.Nonempty ∧ ∃ m : M, (2 : ℤ) • m = ∑ i ∈ J, w i := by
  classical
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_map_eq_zero_of_finrank_range_lt_card
    (integralNodeMap w) hrank
  have hsupport : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (funext h)
  obtain ⟨i, hi⟩ := hsupport
  refine ⟨Finset.univ.filter (fun j => x j ≠ 0),
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩, ?_⟩
  exact (mem_integralNodeCode_iff w x).mp hx

end IntegralCode

section Parity

variable {M ι : Type*} [AddCommGroup M] [Module ℤ M] [Fintype ι]

/-- The constructed code is doubly even under the explicit algebraic parity
and intersection hypotheses. No linear-code closure is an input. -/
theorem integralNodeCode_doublyEven
    (B : LinearMap.BilinForm ℤ M) (K : M) (hchar : IsCharacteristic B K)
    (w : ι → M) (hsq : ∀ i, B (w i) (w i) = -2)
    (horth : ∀ i j, i ≠ j → B (w i) (w j) = 0)
    (hK : ∀ i, B K (w i) = 0) : DoublyEvenCode (integralNodeCode w) := by
  intro x hx
  exact doublyEvenWord_of_nodeHalfSum B K hchar w x hsq horth hK
    ((mem_integralNodeCode_iff w x).mp hx)

/-- Four nodes with quotient image rank at most three have a divisible total
sum when the form satisfies characteristic parity. -/
theorem total_node_sum_divisible_of_card_eq_four_of_range_le_three
    (B : LinearMap.BilinForm ℤ M) (K : M) (hchar : IsCharacteristic B K)
    (w : ι → M) (hsq : ∀ i, B (w i) (w i) = -2)
    (horth : ∀ i j, i ≠ j → B (w i) (w j) = 0)
    (hK : ∀ i, B K (w i) = 0) (hι : Fintype.card ι = 4)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (integralNodeMap w)) ≤ 3) :
    ∃ m : M, (2 : ℤ) • m = ∑ i, w i := by
  apply (ones_mem_integralNodeCode_iff w).mp
  exact ones_mem_kernel_of_doublyEven_of_card_eq_four_of_range_le_three
    (integralNodeMap w) (integralNodeCode_doublyEven B K hchar w hsq horth hK)
    hι hrank

end Parity

end KltDP.Codes

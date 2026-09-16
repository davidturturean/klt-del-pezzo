import KltDP.Lattices.ModTwoForm
import KltDP.Lattices.ModTwoIndex
import KltDP.Lattices.OrthogonalRank

/-!
# Integral node codes and the actual sublattice index

An actual finite integral basis and a bilinear form with Gram determinant
of absolute value one give a nondegenerate form on the actual quotient
`M / (2 M)`. If every node vector pairs evenly with the actual submodule
`Γ`, the node image lies in the orthogonal complement of the reduced image
of `Γ`. Its rank is therefore at most the dimension of the quotient by that
image, which is bounded by the exponent of two in the actual finite index.

The previously constructed integral node code consequently has dimension
at least the number of nodes minus this index exponent. A strict deficit
forces a nonempty integral half-sum. Characteristic parity and orthogonal
squares of minus two give the short doubly-even-code obstructions and the
forced total half-sum for four nodes.

The rank bound is proved here, rather than assumed. Finite dimensionality
comes from the actual basis, and the index bound uses a finite-index
instance on the actual subgroup. Neither symmetry of the form nor a
geometric Picard interpretation is assumed. No literature axiom is used.
-/

namespace KltDP.Lattices.IntegralNodeObstruction

open KltDP.Codes
open ModTwoForm
open scoped BigOperators

variable {M κ ι : Type*} [AddCommGroup M]
variable [Fintype κ] [DecidableEq κ] [Fintype ι]

/-- Even integral pairings put the actual node image in the orthogonal
complement of the actual reduced submodule. The flip accommodates the
stated pairing orientation without imposing symmetry. -/
theorem integralNodeImage_le_orthogonal_modTwoImage
    (b : Basis κ ℤ M) (B : LinearMap.BilinForm ℤ M)
    (Γ : Submodule ℤ M) (w : ι → M)
    (hpair : ∀ i y, y ∈ Γ → Even (B (w i) y)) :
    LinearMap.range (integralNodeMap w) ≤
      (quotientForm b B).flip.orthogonal (modTwoImage Γ.toAddSubgroup) := by
  apply OrthogonalRank.range_linearCombination_le_orthogonal
    (quotientForm b B).flip (fun i => modTwoMk M (w i))
  intro i q hq
  obtain ⟨y, hy, rfl⟩ := (mem_modTwoImage_iff Γ.toAddSubgroup q).mp hq
  change quotientForm b B (modTwoMk M (w i)) (modTwoMk M y) = 0
  rw [quotientForm_mk]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (B (w i) y) 2).mpr
    (hpair i y hy).two_dvd

/-- The image rank is bounded by the exponent of two in the actual
finite submodule index. No image-rank or codimension bound is a premise. -/
theorem integralNodeMap_finrank_le_index_factorization
    (b : Basis κ ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1)
    (Γ : Submodule ℤ M) [Γ.toAddSubgroup.FiniteIndex] (w : ι → M)
    (hpair : ∀ i y, y ∈ Γ → Even (B (w i) y)) :
    Module.finrank (ZMod 2) (LinearMap.range (integralNodeMap w)) ≤
      Γ.toAddSubgroup.index.factorization 2 := by
  letI := ModTwoCoordinates.modTwo_finiteDimensional b
  exact (OrthogonalRank.finrank_le_finrank_quotient_of_le_orthogonal
    (quotientForm b B).flip (quotientForm_nondegenerate b B hB).flip
    (integralNodeImage_le_orthogonal_modTwoImage b B Γ w hpair)).trans
      (submodule_modTwoImage_quotient_finrank_le_index_factorization Γ)

/-- Rank-nullity for the constructed code, with its rank bound now derived
from the actual integral index. -/
theorem integralNodeCode_finrank_ge_card_sub_index_factorization
    (b : Basis κ ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1)
    (Γ : Submodule ℤ M) [Γ.toAddSubgroup.FiniteIndex] (w : ι → M)
    (hpair : ∀ i y, y ∈ Γ → Even (B (w i) y)) :
    Fintype.card ι - Γ.toAddSubgroup.index.factorization 2 ≤
      Module.finrank (ZMod 2) (integralNodeCode w) :=
  integralNodeCode_finrank_ge_card_sub w
    (integralNodeMap_finrank_le_index_factorization b B hB Γ w hpair)

/-- An upper bound on the actual index exponent gives the usual `t - s`
lower bound on code dimension. The image-rank bound is still a conclusion. -/
theorem integralNodeCode_finrank_ge_card_sub_of_index_factorization_le
    (b : Basis κ ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1)
    (Γ : Submodule ℤ M) [Γ.toAddSubgroup.FiniteIndex] (w : ι → M)
    (hpair : ∀ i y, y ∈ Γ → Even (B (w i) y))
    {s : ℕ} (hs : Γ.toAddSubgroup.index.factorization 2 ≤ s) :
    Fintype.card ι - s ≤ Module.finrank (ZMod 2) (integralNodeCode w) :=
  integralNodeCode_finrank_ge_card_sub w
    ((integralNodeMap_finrank_le_index_factorization b B hB Γ w hpair).trans hs)

/-- More nodes than the actual index exponent force a nonempty sum which
has a half in the original integral module. -/
theorem exists_nonempty_integral_half_sum_of_index_factorization_lt_card
    (b : Basis κ ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1)
    (Γ : Submodule ℤ M) [Γ.toAddSubgroup.FiniteIndex] (w : ι → M)
    (hpair : ∀ i y, y ∈ Γ → Even (B (w i) y))
    (hcard : Γ.toAddSubgroup.index.factorization 2 < Fintype.card ι) :
    ∃ J : Finset ι, J.Nonempty ∧ ∃ m : M, (2 : ℤ) • m = ∑ i ∈ J, w i :=
  exists_nonempty_integral_half_sum_of_rank_lt w
    (lt_of_le_of_lt
      (integralNodeMap_finrank_le_index_factorization b B hB Γ w hpair) hcard)

/-- The same conclusion with an explicit bound `s` for the index exponent. -/
theorem exists_nonempty_integral_half_sum_of_index_factorization_le
    (b : Basis κ ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1)
    (Γ : Submodule ℤ M) [Γ.toAddSubgroup.FiniteIndex] (w : ι → M)
    (hpair : ∀ i y, y ∈ Γ → Even (B (w i) y))
    {s : ℕ} (hs : Γ.toAddSubgroup.index.factorization 2 ≤ s)
    (hcard : s < Fintype.card ι) :
    ∃ J : Finset ι, J.Nonempty ∧ ∃ m : M, (2 : ℤ) • m = ∑ i ∈ J, w i :=
  exists_nonempty_integral_half_sum_of_index_factorization_lt_card
    b B hB Γ w hpair (lt_of_le_of_lt hs hcard)

/-- Characteristic parity and the actual index bound hold for the same
constructed integral code. No linear-code closure is an input. -/
theorem integralNodeCode_doublyEven_and_finrank_ge
    (b : Basis κ ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1)
    (Γ : Submodule ℤ M) [Γ.toAddSubgroup.FiniteIndex] (w : ι → M)
    (hpair : ∀ i y, y ∈ Γ → Even (B (w i) y))
    (K : M) (hchar : IsCharacteristic B K)
    (hsq : ∀ i, B (w i) (w i) = -2)
    (horth : ∀ i j, i ≠ j → B (w i) (w j) = 0)
    (hK : ∀ i, B K (w i) = 0) :
    DoublyEvenCode (integralNodeCode w) ∧
      Fintype.card ι - Γ.toAddSubgroup.index.factorization 2 ≤
        Module.finrank (ZMod 2) (integralNodeCode w) :=
  ⟨integralNodeCode_doublyEven B K hchar w hsq horth hK,
    integralNodeCode_finrank_ge_card_sub_index_factorization b B hB Γ w hpair⟩

/-- For fewer than four orthogonal nodes, characteristic parity forces the
number of nodes to be at most the exponent of two in the actual index. -/
theorem card_le_index_factorization_of_card_lt_four
    (b : Basis κ ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1)
    (Γ : Submodule ℤ M) [Γ.toAddSubgroup.FiniteIndex] (w : ι → M)
    (hpair : ∀ i y, y ∈ Γ → Even (B (w i) y))
    (K : M) (hchar : IsCharacteristic B K)
    (hsq : ∀ i, B (w i) (w i) = -2)
    (horth : ∀ i j, i ≠ j → B (w i) (w j) = 0)
    (hK : ∀ i, B K (w i) = 0) (hcard : Fintype.card ι < 4) :
    Fintype.card ι ≤ Γ.toAddSubgroup.index.factorization 2 := by
  have hzero := doublyEvenCode_finrank_eq_zero_of_card_lt_four
    (integralNodeCode w) (integralNodeCode_doublyEven B K hchar w hsq horth hK) hcard
  have hlower :=
    integralNodeCode_finrank_ge_card_sub_index_factorization b B hB Γ w hpair
  omega

/-- Three orthogonal nodes require index exponent at least three. In
particular, an index exponent at most two is impossible. -/
theorem three_le_index_factorization_of_card_eq_three
    (b : Basis κ ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1)
    (Γ : Submodule ℤ M) [Γ.toAddSubgroup.FiniteIndex] (w : ι → M)
    (hpair : ∀ i y, y ∈ Γ → Even (B (w i) y))
    (K : M) (hchar : IsCharacteristic B K)
    (hsq : ∀ i, B (w i) (w i) = -2)
    (horth : ∀ i j, i ≠ j → B (w i) (w j) = 0)
    (hK : ∀ i, B K (w i) = 0) (hcard : Fintype.card ι = 3) :
    3 ≤ Γ.toAddSubgroup.index.factorization 2 := by
  have h := card_le_index_factorization_of_card_lt_four
    b B hB Γ w hpair K hchar hsq horth hK (by omega)
  simpa only [hcard] using h

/-- Four orthogonal nodes also require index exponent at least three,
because their doubly-even code has dimension at most one. -/
theorem three_le_index_factorization_of_card_eq_four
    (b : Basis κ ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1)
    (Γ : Submodule ℤ M) [Γ.toAddSubgroup.FiniteIndex] (w : ι → M)
    (hpair : ∀ i y, y ∈ Γ → Even (B (w i) y))
    (K : M) (hchar : IsCharacteristic B K)
    (hsq : ∀ i, B (w i) (w i) = -2)
    (horth : ∀ i j, i ≠ j → B (w i) (w j) = 0)
    (hK : ∀ i, B K (w i) = 0) (hcard : Fintype.card ι = 4) :
    3 ≤ Γ.toAddSubgroup.index.factorization 2 := by
  have hupper := doublyEvenCode_finrank_le_one_of_card_eq_four
    (integralNodeCode w) (integralNodeCode_doublyEven B K hchar w hsq horth hK) hcard
  have hlower :=
    integralNodeCode_finrank_ge_card_sub_index_factorization b B hB Γ w hpair
  omega

/-- For four orthogonal nodes and index exponent at most three, the sum of
all supplied vectors has an integral half. -/
theorem total_node_sum_divisible_of_card_eq_four_of_index_factorization_le_three
    (b : Basis κ ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1)
    (Γ : Submodule ℤ M) [Γ.toAddSubgroup.FiniteIndex] (w : ι → M)
    (hpair : ∀ i y, y ∈ Γ → Even (B (w i) y))
    (K : M) (hchar : IsCharacteristic B K)
    (hsq : ∀ i, B (w i) (w i) = -2)
    (horth : ∀ i j, i ≠ j → B (w i) (w j) = 0)
    (hK : ∀ i, B K (w i) = 0) (hcard : Fintype.card ι = 4)
    (hindex : Γ.toAddSubgroup.index.factorization 2 ≤ 3) :
    ∃ m : M, (2 : ℤ) • m = ∑ i, w i :=
  total_node_sum_divisible_of_card_eq_four_of_range_le_three B K hchar w hsq horth hK
    hcard ((integralNodeMap_finrank_le_index_factorization b B hB Γ w hpair).trans hindex)

/-- The forced four-node half also has its actual integral square and
pairing with the characteristic vector determined. -/
theorem exists_four_node_half_with_pairings_of_index_factorization_le_three
    (b : Basis κ ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1)
    (Γ : Submodule ℤ M) [Γ.toAddSubgroup.FiniteIndex] (w : ι → M)
    (hpair : ∀ i y, y ∈ Γ → Even (B (w i) y))
    (K : M) (hchar : IsCharacteristic B K)
    (hsq : ∀ i, B (w i) (w i) = -2)
    (horth : ∀ i j, i ≠ j → B (w i) (w j) = 0)
    (hK : ∀ i, B K (w i) = 0) (hcard : Fintype.card ι = 4)
    (hindex : Γ.toAddSubgroup.index.factorization 2 ≤ 3) :
    ∃ m : M, (2 : ℤ) • m = (∑ i, w i) ∧ B m m = -2 ∧ B K m = 0 := by
  classical
  obtain ⟨m, hm⟩ :=
    total_node_sum_divisible_of_card_eq_four_of_index_factorization_le_three
      b B hB Γ w hpair K hchar hsq horth hK hcard hindex
  refine ⟨m, hm, ?_, ?_⟩
  · have hs := nodeHalfSum_square B w Finset.univ m
      (fun i _ => hsq i) (fun i _ j _ hij => horth i j hij) hm
    rw [Finset.card_univ, hcard] at hs
    norm_num at hs
    linarith
  · exact nodeHalfSum_pairing_zero B K w Finset.univ m (fun i _ => hK i) hm

end KltDP.Lattices.IntegralNodeObstruction

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-!
# Small ADE count partitions and their determinant arithmetic

The inputs are arbitrary natural counts of `A1`, `A2`, `A3`, `A4`, and `D4`.
Rank and component inequalities prove finite bounds on every count before
kernel decision checks classify the resulting finite arithmetic domain.
The determinant product is explicitly `2^a1 * 3^a2 * 4^a3 * 5^a4 * 4^d4`.
The square condition similarly gives a proved finite bound on its natural
square root before square rows are classified.

This establishes the combinatorial arithmetic tables in manuscript
`lem:eight-curve-forest` and `prop:zero-adjoint`, lines 1448–1540. It does not
classify arbitrary graphs or geometric forests as ADE, identify this product
with the determinant of an actual block matrix, or establish a Picard index
formula. Those graph, matrix, and geometric adapters remain separate.
-/

namespace KltDP.Lattices.SmallADEPartitions

/-- Actual multiplicities of the five permitted component types. -/
structure Counts where
  a1 : ℕ
  a2 : ℕ
  a3 : ℕ
  a4 : ℕ
  d4 : ℕ
  deriving DecidableEq

/-- Sum of the actual component ranks. -/
def Counts.rank (c : Counts) : ℕ := c.a1 + 2 * c.a2 + 3 * c.a3 + 4 * c.a4 + 4 * c.d4

/-- Number of components counted with multiplicity. -/
def Counts.components (c : Counts) : ℕ := c.a1 + c.a2 + c.a3 + c.a4 + c.d4

/-- Product of the stated root determinants, not an assumed matrix identity. -/
def Counts.rootDet (c : Counts) : ℕ :=
  2 ^ c.a1 * 3 ^ c.a2 * 4 ^ c.a3 * 5 ^ c.a4 * 4 ^ c.d4

/-- Rank at most eight and at least five components imply small count bounds. -/
theorem count_bounds_of_small_rank (c : Counts)
    (hrank : c.rank ≤ 8) (hcomp : 5 ≤ c.components) :
    c.a1 < 9 ∧ c.a2 < 4 ∧ c.a3 < 2 ∧ c.a4 < 2 ∧ c.d4 < 2 := by
  rcases c with ⟨a1, a2, a3, a4, d4⟩
  simp only [Counts.rank, Counts.components] at hrank hcomp
  change a1 < 9 ∧ a2 < 4 ∧ a3 < 2 ∧ a4 < 2 ∧ d4 < 2
  omega

/-- The eight rank-eight count partitions, in manuscript table order. -/
def rankEightRows : Finset Counts :=
  {⟨2, 3, 0, 0, 0⟩, ⟨3, 1, 1, 0, 0⟩, ⟨4, 0, 0, 0, 1⟩,
   ⟨4, 0, 0, 1, 0⟩, ⟨4, 2, 0, 0, 0⟩, ⟨5, 0, 1, 0, 0⟩,
   ⟨6, 1, 0, 0, 0⟩, ⟨8, 0, 0, 0, 0⟩}

/-- The three square rows record both the index and all component counts. -/
def rankEightSquareRows : Finset (ℕ × Counts) :=
  {(8, ⟨4, 0, 0, 0, 1⟩), (12, ⟨4, 2, 0, 0, 0⟩), (16, ⟨8, 0, 0, 0, 0⟩)}

/-- The six rows record beta, the index, and all component counts. -/
def betaSquareRows : Finset (ℕ × ℕ × Counts) :=
  {(3, 12, ⟨4, 1, 0, 0, 0⟩), (4, 16, ⟨7, 0, 0, 0, 0⟩),
   (4, 12, ⟨3, 2, 0, 0, 0⟩), (5, 16, ⟨8, 0, 0, 0, 0⟩),
   (5, 12, ⟨4, 2, 0, 0, 0⟩), (5, 8, ⟨4, 0, 0, 0, 1⟩)}

private def boundedCounts (a1 : Fin 9) (a2 : Fin 4) (a3 a4 d4 : Fin 2) : Counts :=
  ⟨a1, a2, a3, a4, d4⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem bounded_rankEight_rows :
    ∀ (a1 : Fin 9) (a2 : Fin 4) (a3 a4 d4 : Fin 2),
      (boundedCounts a1 a2 a3 a4 d4).rank = 8 →
      5 ≤ (boundedCounts a1 a2 a3 a4 d4).components →
      boundedCounts a1 a2 a3 a4 d4 ∈ rankEightRows := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem bounded_rootDet_le :
    ∀ (a1 : Fin 9) (a2 : Fin 4) (a3 a4 d4 : Fin 2),
      (boundedCounts a1 a2 a3 a4 d4).rank ≤ 8 →
      5 ≤ (boundedCounts a1 a2 a3 a4 d4).components →
      (boundedCounts a1 a2 a3 a4 d4).rootDet ≤ 256 := by
  decide

/-- Completeness of the eight-row table for arbitrary natural counts. -/
theorem rankEight_classification (c : Counts)
    (hrank : c.rank = 8) (hcomp : 5 ≤ c.components) : c ∈ rankEightRows := by
  obtain ⟨h1, h2, h3, h4, hd⟩ := count_bounds_of_small_rank c hrank.le hcomp
  exact bounded_rankEight_rows ⟨c.a1, h1⟩ ⟨c.a2, h2⟩ ⟨c.a3, h3⟩
    ⟨c.a4, h4⟩ ⟨c.d4, hd⟩ hrank hcomp

/-- Every table entry satisfies the claimed rank and component inequalities. -/
theorem mem_rankEightRows_iff (c : Counts) :
    c ∈ rankEightRows ↔ c.rank = 8 ∧ 5 ≤ c.components := by
  constructor
  · intro hc
    simp only [rankEightRows, Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rintro ⟨hrank, hcomp⟩
    exact rankEight_classification c hrank hcomp

/-- The determinant values are computed for all eight classified count rows. -/
theorem rankEight_rootDet_table (c : Counts)
    (hrank : c.rank = 8) (hcomp : 5 ≤ c.components) :
    (c, c.rootDet) ∈
      ({(⟨2, 3, 0, 0, 0⟩, 108), (⟨3, 1, 1, 0, 0⟩, 96),
        (⟨4, 0, 0, 0, 1⟩, 64), (⟨4, 0, 0, 1, 0⟩, 80),
        (⟨4, 2, 0, 0, 0⟩, 144), (⟨5, 0, 1, 0, 0⟩, 128),
        (⟨6, 1, 0, 0, 0⟩, 192), (⟨8, 0, 0, 0, 0⟩, 256)} : Finset (Counts × ℕ)) := by
  have hc := rankEight_classification c hrank hcomp
  simp only [rankEightRows, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The determinant bound is proved from rank and component inequalities. -/
theorem rootDet_le_of_small_rank (c : Counts)
    (hrank : c.rank ≤ 8) (hcomp : 5 ≤ c.components) : c.rootDet ≤ 256 := by
  obtain ⟨h1, h2, h3, h4, hd⟩ := count_bounds_of_small_rank c hrank hcomp
  exact bounded_rootDet_le ⟨c.a1, h1⟩ ⟨c.a2, h2⟩ ⟨c.a3, h3⟩
    ⟨c.a4, h4⟩ ⟨c.d4, hd⟩ hrank hcomp

/-- A square determinant bounded by 256 has a natural square root below 17. -/
theorem index_lt_seventeen {d I : ℕ} (hd : d ≤ 256) (hsquare : d = I ^ 2) : I < 17 := by
  by_contra hI
  have h17 : 17 ≤ I := by omega
  have hp := Nat.pow_le_pow_left h17 2
  norm_num at hp
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem bounded_rankEight_square_rows :
    ∀ (I : Fin 17) (a1 : Fin 9) (a2 : Fin 4) (a3 a4 d4 : Fin 2),
      (boundedCounts a1 a2 a3 a4 d4).rank = 8 →
      5 ≤ (boundedCounts a1 a2 a3 a4 d4).components →
      (boundedCounts a1 a2 a3 a4 d4).rootDet = (I : ℕ) ^ 2 →
      ((I : ℕ), boundedCounts a1 a2 a3 a4 d4) ∈ rankEightSquareRows := by
  decide

/-- Only the three stated index/count rows survive the actual square equation. -/
theorem rankEight_square_classification (c : Counts) (I : ℕ)
    (hrank : c.rank = 8) (hcomp : 5 ≤ c.components) (hsquare : c.rootDet = I ^ 2) :
    (I, c) ∈ rankEightSquareRows := by
  obtain ⟨h1, h2, h3, h4, hd⟩ := count_bounds_of_small_rank c hrank.le hcomp
  have hI := index_lt_seventeen (rootDet_le_of_small_rank c hrank.le hcomp) hsquare
  exact bounded_rankEight_square_rows ⟨I, hI⟩ ⟨c.a1, h1⟩ ⟨c.a2, h2⟩
    ⟨c.a3, h3⟩ ⟨c.a4, h4⟩ ⟨c.d4, hd⟩ hrank hcomp hsquare

/-- The square table is exact, including its converse. -/
theorem mem_rankEightSquareRows_iff (c : Counts) (I : ℕ) :
    (I, c) ∈ rankEightSquareRows ↔
      c.rank = 8 ∧ 5 ≤ c.components ∧ c.rootDet = I ^ 2 := by
  constructor
  · intro hc
    simp only [rankEightSquareRows, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at hc
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · rintro ⟨hrank, hcomp, hsquare⟩
    exact rankEight_square_classification c I hrank hcomp hsquare

/-- The index and isolated-node count are precisely the three manuscript pairs. -/
theorem rankEight_square_index_node_pairs (c : Counts) (I : ℕ)
    (hrank : c.rank = 8) (hcomp : 5 ≤ c.components) (hsquare : c.rootDet = I ^ 2) :
    (I = 8 ∧ c.a1 = 4) ∨ (I = 12 ∧ c.a1 = 4) ∨ (I = 16 ∧ c.a1 = 8) := by
  have hc := rankEight_square_classification c I hrank hcomp hsquare
  simp only [rankEightSquareRows, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at hc
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

private theorem factorization_eight : (8 : ℕ).factorization 2 = 3 := by
  change (2 ^ 3 : ℕ).factorization 2 = 3
  rw [Nat.prime_two.factorization_pow]
  simp

private theorem factorization_twelve : (12 : ℕ).factorization 2 = 2 := by
  change (2 ^ 2 * 3 : ℕ).factorization 2 = 2
  rw [Nat.factorization_mul (by decide : (2 : ℕ) ^ 2 ≠ 0) (by decide : (3 : ℕ) ≠ 0),
    Nat.prime_two.factorization_pow, Nat.prime_three.factorization]
  simp

private theorem factorization_sixteen : (16 : ℕ).factorization 2 = 4 := by
  change (2 ^ 4 : ℕ).factorization 2 = 4
  rw [Nat.prime_two.factorization_pow]
  simp

/-- Every rank-eight square row has more isolated nodes than its two-adic index exponent. -/
theorem rankEight_square_factorization_lt_nodes (c : Counts) (I : ℕ)
    (hrank : c.rank = 8) (hcomp : 5 ≤ c.components) (hsquare : c.rootDet = I ^ 2) :
    I.factorization 2 < c.a1 := by
  have hc := rankEight_square_classification c I hrank hcomp hsquare
  simp only [rankEightSquareRows, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at hc
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [factorization_eight, factorization_twelve, factorization_sixteen] <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem bounded_beta_totalDet_le :
    ∀ (beta : Fin 6) (a1 : Fin 9) (a2 : Fin 4) (a3 a4 d4 : Fin 2),
      3 ≤ (beta : ℕ) →
      (boundedCounts a1 a2 a3 a4 d4).rank = (beta : ℕ) + 3 →
      5 ≤ (boundedCounts a1 a2 a3 a4 d4).components →
      (6 - (beta : ℕ)) * (boundedCounts a1 a2 a3 a4 d4).rootDet ≤ 256 := by
  decide

/-- The beta-dependent determinant has the same proven bound of 256. -/
theorem beta_totalDet_le (c : Counts) (beta : ℕ)
    (hbeta3 : 3 ≤ beta) (hbeta5 : beta ≤ 5)
    (hrank : c.rank = beta + 3) (hcomp : 5 ≤ c.components) :
    (6 - beta) * c.rootDet ≤ 256 := by
  have hrank8 : c.rank ≤ 8 := by omega
  obtain ⟨h1, h2, h3, h4, hd⟩ := count_bounds_of_small_rank c hrank8 hcomp
  exact bounded_beta_totalDet_le ⟨beta, by omega⟩ ⟨c.a1, h1⟩ ⟨c.a2, h2⟩
    ⟨c.a3, h3⟩ ⟨c.a4, h4⟩ ⟨c.d4, hd⟩ hbeta3 hrank hcomp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem bounded_beta_square_rows :
    ∀ (beta : Fin 6) (I : Fin 17) (a1 : Fin 9) (a2 : Fin 4) (a3 a4 d4 : Fin 2),
      3 ≤ (beta : ℕ) →
      (boundedCounts a1 a2 a3 a4 d4).rank = (beta : ℕ) + 3 →
      5 ≤ (boundedCounts a1 a2 a3 a4 d4).components →
      (6 - (beta : ℕ)) * (boundedCounts a1 a2 a3 a4 d4).rootDet = (I : ℕ) ^ 2 →
      ((beta : ℕ), (I : ℕ), boundedCounts a1 a2 a3 a4 d4) ∈ betaSquareRows := by
  decide

/-- Exactly six beta/index/count rows survive all the stated arithmetic conditions. -/
theorem beta_square_classification (c : Counts) (beta I : ℕ)
    (hbeta3 : 3 ≤ beta) (hbeta5 : beta ≤ 5)
    (hrank : c.rank = beta + 3) (hcomp : 5 ≤ c.components)
    (hsquare : (6 - beta) * c.rootDet = I ^ 2) :
    (beta, I, c) ∈ betaSquareRows := by
  have hrank8 : c.rank ≤ 8 := by omega
  obtain ⟨h1, h2, h3, h4, hd⟩ := count_bounds_of_small_rank c hrank8 hcomp
  have hI := index_lt_seventeen (beta_totalDet_le c beta hbeta3 hbeta5 hrank hcomp) hsquare
  exact bounded_beta_square_rows ⟨beta, by omega⟩ ⟨I, hI⟩
    ⟨c.a1, h1⟩ ⟨c.a2, h2⟩ ⟨c.a3, h3⟩ ⟨c.a4, h4⟩ ⟨c.d4, hd⟩
    hbeta3 hrank hcomp hsquare

/-- The six-row classification includes verification of every listed row. -/
theorem mem_betaSquareRows_iff (c : Counts) (beta I : ℕ) :
    (beta, I, c) ∈ betaSquareRows ↔
      3 ≤ beta ∧ beta ≤ 5 ∧ c.rank = beta + 3 ∧ 5 ≤ c.components ∧
        (6 - beta) * c.rootDet = I ^ 2 := by
  constructor
  · intro hc
    simp only [betaSquareRows, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at hc
    rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide
  · rintro ⟨hbeta3, hbeta5, hrank, hcomp, hsquare⟩
    exact beta_square_classification c beta I hbeta3 hbeta5 hrank hcomp hsquare

/-- Every beta square row has more isolated nodes than its two-adic index exponent. -/
theorem beta_square_factorization_lt_nodes (c : Counts) (beta I : ℕ)
    (hbeta3 : 3 ≤ beta) (hbeta5 : beta ≤ 5)
    (hrank : c.rank = beta + 3) (hcomp : 5 ≤ c.components)
    (hsquare : (6 - beta) * c.rootDet = I ^ 2) :
    I.factorization 2 < c.a1 := by
  have hc := beta_square_classification c beta I hbeta3 hbeta5 hrank hcomp hsquare
  simp only [betaSquareRows, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at hc
  rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp only [factorization_eight, factorization_twelve, factorization_sixteen] <;> decide

end KltDP.Lattices.SmallADEPartitions

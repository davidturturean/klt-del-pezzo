import KltDP.Lattices.IntegralNodeObstruction

/-!
# Support obligation U-CODE-KERNEL-LIFT: half-sums land in the integral lattice

Manuscript `source/manuscript.tex` lines 1365–1432 (proofs of `lem:picard-index`
and `lem:picard-parity`). The plan contract (`U-CODE-KERNEL-LIFT`): "the nonzero
kernel element supported on node discriminant factors has a representative
exactly `(Σ W_i)/2` in `Pic(S)` after subtraction of an element of `Γ`; every
node index used is an isolated original component disjoint from the auxiliary
`P`."

The accepted module `KltDP.Lattices.IntegralNodeObstruction` proves the lattice
content: for an actual finite integral basis with unimodular Gram determinant, a
finite-index submodule `Γ`, and node vectors pairing evenly with `Γ`, a strict
deficit of the two-adic index exponent below the node count yields a nonempty
subfamily `J` and an actual integral vector `m` with `2 • m = Σ_{i ∈ J} W_i`.
This module packages that statement as `u_code_kernel_lift`, states the "exactly
half of the indicated sum" clause in the integral module (not its
rationalization), and adds that `J` can be taken with at least four elements
when a characteristic vector orthogonal to the nodes is present (doubly-even
parity).

Not proved here: that `Pic(S)` with the intersection form is such a lattice,
that `Γ = ⟨D, P⟩` has the stated index, that the nodes are isolated exceptional
components disjoint from `P`, and Riemann–Roch parity for `K_S` (F03, F05, F14,
F24).
-/

namespace KltDP.Support

open KltDP.Codes KltDP.Lattices.IntegralNodeObstruction
open scoped BigOperators

variable {M κ ι : Type*} [AddCommGroup M] [Fintype κ] [DecidableEq κ] [Fintype ι]

/-- **U-CODE-KERNEL-LIFT**, lattice clause. With a unimodular integral basis, a
finite-index submodule `Γ`, and node vectors pairing evenly with `Γ`, if the
two-adic exponent of the index is smaller than the number of nodes, then some
nonempty subfamily of the nodes has a sum that is exactly twice an integral
vector `m` of the module itself. -/
theorem u_code_kernel_lift
    (b : Basis κ ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1)
    (Γ : Submodule ℤ M) [Γ.toAddSubgroup.FiniteIndex] (w : ι → M)
    (hpair : ∀ i y, y ∈ Γ → Even (B (w i) y))
    (hcard : Γ.toAddSubgroup.index.factorization 2 < Fintype.card ι) :
    ∃ J : Finset ι, J.Nonempty ∧ ∃ m : M, (2 : ℤ) • m = ∑ i ∈ J, w i :=
  exists_nonempty_integral_half_sum_of_index_factorization_lt_card b B hB Γ w hpair hcard

/-- The integral half-sum, with the additional parity information: when a
characteristic vector orthogonal to the pairwise orthogonal square `-2` nodes is
present, the subfamily has a multiple of four elements, hence at least four. -/
theorem u_code_kernel_lift_four
    (b : Basis κ ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1)
    (Γ : Submodule ℤ M) [Γ.toAddSubgroup.FiniteIndex] (w : ι → M)
    (hpair : ∀ i y, y ∈ Γ → Even (B (w i) y))
    (hcard : Γ.toAddSubgroup.index.factorization 2 < Fintype.card ι)
    (K : M) (hchar : IsCharacteristic B K)
    (hsq : ∀ i, B (w i) (w i) = -2)
    (horth : ∀ i j, i ≠ j → B (w i) (w j) = 0)
    (hK : ∀ i, B K (w i) = 0) :
    ∃ J : Finset ι, J.Nonempty ∧ 4 ∣ J.card ∧ 4 ≤ J.card ∧
      ∃ m : M, (2 : ℤ) • m = ∑ i ∈ J, w i := by
  obtain ⟨J, hJ, m, hm⟩ := u_code_kernel_lift b B hB Γ w hpair hcard
  have hdvd : 4 ∣ J.card :=
    four_dvd_card_of_nodeHalfSum B K hchar w J (fun i _ => hsq i)
      (fun i _ j _ hij => horth i j hij) (fun i _ => hK i) ⟨m, hm⟩
  refine ⟨J, hJ, hdvd, ?_, m, hm⟩
  have hpos : 0 < J.card := Finset.card_pos.mpr hJ
  exact Nat.le_of_dvd hpos hdvd

/-- "Exactly half": the vector `m` is uniquely determined by the subfamily when
the module is torsion-free (as an integral lattice is). -/
theorem half_sum_unique [NoZeroSMulDivisors ℤ M] (w : ι → M) (J : Finset ι) (m m' : M)
    (hm : (2 : ℤ) • m = ∑ i ∈ J, w i) (hm' : (2 : ℤ) • m' = ∑ i ∈ J, w i) : m = m' := by
  have h : (2 : ℤ) • m = (2 : ℤ) • m' := hm.trans hm'.symm
  exact smul_right_injective M (by norm_num : (2 : ℤ) ≠ 0) h

end KltDP.Support

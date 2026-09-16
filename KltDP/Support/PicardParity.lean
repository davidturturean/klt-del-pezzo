import KltDP.Codes.NodeParity

/-!
# Support obligation U-PICARD-PARITY: weight of an even set is divisible by four

Manuscript `source/manuscript.tex` lines 1220–1240: "if a sum of `w` disjoint
`(-2)`-curves is twice a Picard class, then `4 ∣ w`. This follows from
Riemann–Roch parity and holds in every characteristic." The plan contract
(`U-PICARD-PARITY`) asks for `K·M = 0`, `M² = -w/2` and `4 ∣ w` when
`2M = Σ W_i` for pairwise disjoint smooth rational `(-2)`-curves `W_i`.

This module packages the accepted lattice theorems of `KltDP.Codes.NodeParity`
into the single support statement `u_picard_parity`, for an arbitrary
`ℤ`-module with an integer-valued bilinear form: the vectors `w i` have square
`-2`, are pairwise orthogonal and orthogonal to a characteristic vector `K`
(`IsCharacteristic B K`: `B x x - B K x` is even for every `x`), and `2 • M`
is their sum. The conclusions are `B K M = 0`, `2 * B M M = -w` (that is,
`M² = -w/2`) and `4 ∣ w`.

The geometric inputs are not proved here: that the actual Picard group of a
smooth projective rational surface with its intersection form is such a
lattice, that `K_S` is characteristic (Riemann–Roch parity, F05, F14), and that
smooth rational `(-2)`-curves satisfy `K·W_i = 0` (adjunction, F03, F04).
-/

namespace KltDP.Support

open KltDP.Codes
open scoped BigOperators

variable {M ι : Type*} [AddCommGroup M] [Module ℤ M] [Fintype ι]

/-- **U-PICARD-PARITY**, lattice clause. For an integer bilinear form `B`, a
characteristic vector `K`, and vectors `w i` of square `-2`, pairwise orthogonal
and orthogonal to `K`, if `2 • m = Σ w i` then `K·m = 0`, `2 m² = -w` and `4 ∣ w`,
where `w` is the number of summands. -/
theorem u_picard_parity (B : LinearMap.BilinForm ℤ M) (K : M)
    (hchar : IsCharacteristic B K) (w : ι → M) (m : M)
    (hsq : ∀ i, B (w i) (w i) = -2)
    (horth : ∀ i j, i ≠ j → B (w i) (w j) = 0)
    (hK : ∀ i, B K (w i) = 0)
    (hm : (2 : ℤ) • m = ∑ i, w i) :
    B K m = 0 ∧ 2 * B m m = -(Fintype.card ι : ℤ) ∧ 4 ∣ Fintype.card ι := by
  have hsq' : ∀ i ∈ (Finset.univ : Finset ι), B (w i) (w i) = -2 := fun i _ => hsq i
  have horth' : ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ (Finset.univ : Finset ι),
      i ≠ j → B (w i) (w j) = 0 := fun i _ j _ hij => horth i j hij
  have hK' : ∀ i ∈ (Finset.univ : Finset ι), B K (w i) = 0 := fun i _ => hK i
  refine ⟨nodeHalfSum_pairing_zero B K w Finset.univ m hK' hm, ?_, ?_⟩
  · have := nodeHalfSum_square B w Finset.univ m hsq' horth' hm
    simpa [Finset.card_univ] using this
  · have := four_dvd_card_of_nodeHalfSum B K hchar w Finset.univ hsq' horth' hK' ⟨m, hm⟩
    simpa [Finset.card_univ] using this

/-- The same statement for a finite subfamily indexed by a `Finset`. -/
theorem u_picard_parity_finset {ι : Type*} (B : LinearMap.BilinForm ℤ M) (K : M)
    (hchar : IsCharacteristic B K) (w : ι → M) (s : Finset ι) (m : M)
    (hsq : ∀ i ∈ s, B (w i) (w i) = -2)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → B (w i) (w j) = 0)
    (hK : ∀ i ∈ s, B K (w i) = 0)
    (hm : (2 : ℤ) • m = ∑ i ∈ s, w i) :
    B K m = 0 ∧ 2 * B m m = -(s.card : ℤ) ∧ 4 ∣ s.card :=
  ⟨nodeHalfSum_pairing_zero B K w s m hK hm, nodeHalfSum_square B w s m hsq horth hm,
    four_dvd_card_of_nodeHalfSum B K hchar w s hsq horth hK ⟨m, hm⟩⟩

end KltDP.Support

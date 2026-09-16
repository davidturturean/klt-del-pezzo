import KltDP.Lattices.IndexDeterminant
import KltDP.Lattices.IntegralNodeObstruction
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Torsion
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Int.AbsoluteValue
import Mathlib.Tactic

/-!
# A02: the independent integral lattice and code core

Supporting obligation A02 (`planning/AUTOFORMALIZATION_PLAN.md` §6 "A02",
`planning/THEOREM_MAP.json` id A02; source `source/manuscript.tex` lines
1342–1432, `lem:picard-index` and `lem:picard-parity`). The planned export
`KltDP.Arithmetic.a02` is provided here as `KltDP.Support.a02`. Everything is
integral linear algebra and finite group theory; no surface, Picard group,
intersection form or canonical class is constructed or assumed.

* Index-square determinant (re-exported from the accepted
  `KltDP.Lattices.IndexDeterminant`): for a full-rank sublattice `N` of a
  finite free `ℤ`-module `M` with bases indexed by the same finite type,
  `|det Gram(N)| = [M : N]² · |det Gram(M)|`, and `= [M : N]²` when the ambient
  form is unimodular (`picard_fullLattice_indexSquare`).
* Discriminant group order (new): for an integral matrix `G` with `det G ≠ 0`,
  the discriminant group `discriminantGroup G := ℤ^ι / G ℤ^ι` is finite of
  order `|det G|` (`discriminantGroup_card`, from the pinned
  `Submodule.natAbs_det_basis_change` with the columns of `G` as a basis of
  the image); for a nondegenerate integral form `B` with Gram matrix `G`, the
  dual quotient `M^∨ / B(M)` has the same order (`dualQuotient_card`).
* 2-primary part (new): for a finite abelian group `A`, the `2`-primary
  component has order `2^{v₂(|A|)}` (`card_addPrimaryComponent`, via the pinned
  Sylow theory on `Multiplicative A`); specialized to `M ⧸ Γ` for a
  finite-index subgroup (`twoPrimary_card_quotient_index`) and to the
  discriminant group (`discriminantGroup_twoPrimary_card`). The accepted binary
  quotient bound `finrank (M/2M ⧸ image Γ) ≤ v₂([M : Γ])` is re-exported.
* Orthogonal node discriminants (new): `det` of an orthogonal (block-diagonal)
  sum is the product (pinned `Matrix.det_blockDiagonal`), and the discriminant
  group of `r` orthogonal nodes of square `-2` (`nodeGram ι = diagonal (-2)`)
  is `ℤ`-linearly isomorphic to `(ZMod 2)^ι` (`nodeDiscriminantEquiv`), of
  order `2^r = |det|`.
* Binary-kernel bounds and characteristic parity (re-exported from the
  accepted `KltDP.Lattices.IntegralNodeObstruction`, `KltDP.Codes.NodeParity`,
  `KltDP.Codes.DoublyEven`).
* `a02` bundles the clauses.

Not proved here: nothing of the A02 goal is omitted. The primary decomposition
is delivered as the order of the `2`-primary component (the clause the geometry
uses); the full product decomposition of a finite abelian group into its
primary components is not restated.
-/

universe u v

namespace KltDP.Support

open KltDP.Lattices KltDP.Codes
open LinearMap (BilinForm)

/-! ### Clause 1: index-square determinant (accepted, re-exported) -/

section IndexSquare

variable {M ι : Type*} [AddCommGroup M] [Fintype ι] [DecidableEq ι]

/-- The index of a full-rank sublattice is the absolute determinant of the
coordinate matrix of its basis (accepted `index_eq_natAbs_det_inclusion`). -/
theorem fullLattice_index_eq_natAbs_det (b : Basis ι ℤ M) (N : Submodule ℤ M)
    (bN : Basis ι ℤ N) :
    N.toAddSubgroup.index = (IndexDeterminant.inclusionMatrix b N bN).det.natAbs :=
  IndexDeterminant.index_eq_natAbs_det_inclusion b N bN

omit [DecidableEq ι] in
/-- The quotient by a full-rank sublattice is finite (accepted `quotient_finite`). -/
theorem fullLattice_quotient_finite (b : Basis ι ℤ M) (N : Submodule ℤ M)
    (bN : Basis ι ℤ N) : Finite (M ⧸ N) :=
  IndexDeterminant.quotient_finite b N bN

/-- `|det Gram(N)| = [M : N]² · |det Gram(M)|` (accepted `natAbs_det_gram_restriction`). -/
theorem fullLattice_det_eq_indexSquare_mul (B : BilinForm ℤ M) (b : Basis ι ℤ M)
    (N : Submodule ℤ M) (bN : Basis ι ℤ N) :
    (BilinForm.toMatrix bN (B.comp N.subtype N.subtype)).det.natAbs =
      N.toAddSubgroup.index ^ 2 * (BilinForm.toMatrix b B).det.natAbs :=
  IndexDeterminant.natAbs_det_gram_restriction B b N bN

/-- **Index-square determinant.** In a unimodular integral lattice the
determinant of a full-rank sublattice is the square of its index (accepted
`natAbs_det_gram_restriction_of_unimodular`). -/
theorem picard_fullLattice_indexSquare (B : BilinForm ℤ M) (b : Basis ι ℤ M)
    (N : Submodule ℤ M) (bN : Basis ι ℤ N)
    (h_unimodular : (BilinForm.toMatrix b B).det.natAbs = 1) :
    (BilinForm.toMatrix bN (B.comp N.subtype N.subtype)).det.natAbs =
      N.toAddSubgroup.index ^ 2 :=
  IndexDeterminant.natAbs_det_gram_restriction_of_unimodular B b N bN h_unimodular

end IndexSquare

/-! ### Clause 2: the discriminant group and its order -/

section Discriminant

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The discriminant group `ℤ^ι / G ℤ^ι` of an integral matrix `G`. -/
abbrev discriminantGroup (G : Matrix ι ι ℤ) : Type _ :=
  (ι → ℤ) ⧸ LinearMap.range (Matrix.toLin' G)

/-- A nonsingular integral matrix acts injectively on `ℤ^ι`. -/
theorem toLin'_injective_of_det_ne_zero (G : Matrix ι ι ℤ) (hG : G.det ≠ 0) :
    Function.Injective (Matrix.toLin' G) := by
  rw [← LinearMap.ker_eq_bot, Matrix.ker_toLin'_eq_bot_iff]
  intro v hv
  exact Matrix.eq_zero_of_mulVec_eq_zero hG hv

/-- The columns of `G` as a basis of the image lattice `G ℤ^ι`. -/
noncomputable def rangeBasis (G : Matrix ι ι ℤ) (hG : G.det ≠ 0) :
    Basis ι ℤ (LinearMap.range (Matrix.toLin' G)) :=
  (Pi.basisFun ℤ ι).map (LinearEquiv.ofInjective _ (toLin'_injective_of_det_ne_zero G hG))

/-- The coordinate matrix of the column basis is `G` itself. -/
theorem toMatrix_rangeBasis (G : Matrix ι ι ℤ) (hG : G.det ≠ 0) :
    (Pi.basisFun ℤ ι).toMatrix ((↑) ∘ rangeBasis G hG) = G := by
  ext i j
  rw [Basis.toMatrix_apply, Pi.basisFun_repr, Function.comp_apply, rangeBasis, Basis.map_apply,
    LinearEquiv.ofInjective_apply, Pi.basisFun_apply, Matrix.toLin'_apply,
    Matrix.mulVec_single_one, Matrix.transpose_apply]

/-- **Discriminant group order.** `|ℤ^ι / G ℤ^ι| = |det G|` for `det G ≠ 0`
(pinned `Submodule.natAbs_det_basis_change`). -/
theorem discriminantGroup_card (G : Matrix ι ι ℤ) (hG : G.det ≠ 0) :
    Nat.card (discriminantGroup G) = G.det.natAbs := by
  haveI : Module.Free ℤ (ι → ℤ) := Module.Free.of_basis (Pi.basisFun ℤ ι)
  haveI : Module.Finite ℤ (ι → ℤ) := Module.Finite.of_basis (Pi.basisFun ℤ ι)
  rw [← Submodule.natAbs_det_basis_change (Pi.basisFun ℤ ι) _ (rangeBasis G hG),
    Basis.det_apply, toMatrix_rangeBasis]

/-- The discriminant group is finite. -/
theorem discriminantGroup_finite (G : Matrix ι ι ℤ) (hG : G.det ≠ 0) :
    Finite (discriminantGroup G) :=
  Nat.finite_of_card_ne_zero (by rw [discriminantGroup_card G hG]; exact Int.natAbs_ne_zero.mpr hG)

/-- The Gram-matrix form of the discriminant group of a nondegenerate integral
form on a finite free module. -/
theorem discriminantGroup_card_of_form {M : Type*} [AddCommGroup M] (b : Basis ι ℤ M)
    (B : BilinForm ℤ M) (hB : (BilinForm.toMatrix b B).det ≠ 0) :
    Nat.card (discriminantGroup (BilinForm.toMatrix b B)) = (BilinForm.toMatrix b B).det.natAbs :=
  discriminantGroup_card _ hB

/-- A nondegenerate integral form embeds the lattice into its dual. -/
theorem bilinForm_injective_of_det_ne_zero {M : Type*} [AddCommGroup M] (b : Basis ι ℤ M)
    (B : BilinForm ℤ M) (hB : (BilinForm.toMatrix b B).det ≠ 0) :
    Function.Injective B :=
  LinearMap.ker_eq_bot.mp
    ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mpr hB).ker_eq_bot

/-- The image of a lattice basis in the dual, as a basis of `B(M) ⊆ M^∨`. -/
noncomputable def dualRangeBasis {M : Type*} [AddCommGroup M] (b : Basis ι ℤ M)
    (B : BilinForm ℤ M) (hB : (BilinForm.toMatrix b B).det ≠ 0) :
    Basis ι ℤ (LinearMap.range B) :=
  b.map (LinearEquiv.ofInjective B (bilinForm_injective_of_det_ne_zero b B hB))

/-- In dual-basis coordinates the image basis has matrix `Gram(B)ᵀ`. -/
theorem toMatrix_dualRangeBasis {M : Type*} [AddCommGroup M] (b : Basis ι ℤ M)
    (B : BilinForm ℤ M) (hB : (BilinForm.toMatrix b B).det ≠ 0) :
    b.dualBasis.toMatrix ((↑) ∘ dualRangeBasis b B hB) = (BilinForm.toMatrix b B).transpose := by
  ext i j
  rw [Matrix.transpose_apply, Basis.toMatrix_apply, Basis.dualBasis_repr, Function.comp_apply,
    dualRangeBasis, Basis.map_apply, LinearEquiv.ofInjective_apply,
    _root_.BilinForm.toMatrix_apply]

/-- **Dual-group order.** For a nondegenerate integral form `B` on a finite free
module `M`, the discriminant group `M^∨ / B(M)` is finite of order `|det Gram(B)|`. -/
theorem dualQuotient_card {M : Type*} [AddCommGroup M] (b : Basis ι ℤ M)
    (B : BilinForm ℤ M) (hB : (BilinForm.toMatrix b B).det ≠ 0) :
    Nat.card (Module.Dual ℤ M ⧸ LinearMap.range B) = (BilinForm.toMatrix b B).det.natAbs := by
  haveI : Module.Free ℤ (Module.Dual ℤ M) := Module.Free.of_basis b.dualBasis
  haveI : Module.Finite ℤ (Module.Dual ℤ M) := Module.Finite.of_basis b.dualBasis
  rw [← Submodule.natAbs_det_basis_change b.dualBasis _ (dualRangeBasis b B hB),
    Basis.det_apply, toMatrix_dualRangeBasis, Matrix.det_transpose]

theorem dualQuotient_finite {M : Type*} [AddCommGroup M] (b : Basis ι ℤ M)
    (B : BilinForm ℤ M) (hB : (BilinForm.toMatrix b B).det ≠ 0) :
    Finite (Module.Dual ℤ M ⧸ LinearMap.range B) :=
  Nat.finite_of_card_ne_zero (by rw [dualQuotient_card b B hB]; exact Int.natAbs_ne_zero.mpr hB)

end Discriminant

/-! ### Clause 3: the 2-primary part -/

section Primary

/-- The `p`-primary component of a finite abelian group has order `p^{v_p(|G|)}`
(multiplicative form, via the pinned Sylow theory: the primary component is a
`p`-group containing every Sylow `p`-subgroup). -/
theorem card_primaryComponent {G : Type*} [CommGroup G] [Finite G] (p : ℕ) [Fact p.Prime] :
    Nat.card (CommGroup.primaryComponent G p) = p ^ (Nat.card G).factorization p := by
  obtain ⟨Q, hQ⟩ := (CommGroup.primaryComponent.isPGroup (G := G) (p := p)).exists_le_sylow
  have hQle : (Q : Subgroup G) ≤ CommGroup.primaryComponent G p := by
    intro g hg
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp Q.isPGroup') ⟨g, hg⟩
    show ∃ n : ℕ, orderOf g = p ^ n
    exact ⟨k, (Subgroup.orderOf_coe (⟨g, hg⟩ : (Q : Subgroup G))).trans hk⟩
  have heq : (Q : Subgroup G) = CommGroup.primaryComponent G p := le_antisymm hQle hQ
  rw [← heq]
  exact Q.card_eq_multiplicity

/-- **Primary decomposition (order).** The `p`-primary component of a finite
abelian group `A` has order `p^{v_p(|A|)}`. -/
theorem card_addPrimaryComponent {A : Type*} [AddCommGroup A] [Finite A] (p : ℕ)
    [Fact p.Prime] :
    Nat.card (AddCommGroup.primaryComponent A p) = p ^ (Nat.card A).factorization p := by
  have h := card_primaryComponent (G := Multiplicative A) p
  have hcard : Nat.card (Multiplicative A) = Nat.card A := Nat.card_congr Multiplicative.toAdd
  rw [hcard] at h
  rw [← h]
  refine Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd fun a => ?_)
  show (∃ n : ℕ, addOrderOf a = p ^ n) ↔ ∃ n : ℕ, orderOf (Multiplicative.ofAdd a) = p ^ n
  simp only [orderOf_ofAdd_eq_addOrderOf]

/-- The `2`-primary part of a finite abelian group of order `I` has order `2^{v₂(I)}`. -/
theorem twoPrimary_card_of_finite {A : Type*} [AddCommGroup A] [Finite A] :
    Nat.card (AddCommGroup.primaryComponent A 2) = 2 ^ (Nat.card A).factorization 2 :=
  card_addPrimaryComponent 2

/-- For a finite-index subgroup `Γ ≤ M`, the `2`-primary part of `M ⧸ Γ` has
order `2^{v₂([M : Γ])}`. -/
theorem twoPrimary_card_quotient_index {M : Type*} [AddCommGroup M] (Γ : AddSubgroup M)
    [Γ.FiniteIndex] :
    Nat.card (AddCommGroup.primaryComponent (M ⧸ Γ) 2) = 2 ^ Γ.index.factorization 2 := by
  rw [AddSubgroup.index_eq_card]
  exact twoPrimary_card_of_finite

/-- The `2`-primary part of the discriminant group of `G` has order `2^{v₂(|det G|)}`. -/
theorem discriminantGroup_twoPrimary_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℤ) (hG : G.det ≠ 0) :
    Nat.card (AddCommGroup.primaryComponent (discriminantGroup G) 2) =
      2 ^ G.det.natAbs.factorization 2 := by
  haveI := discriminantGroup_finite G hG
  rw [twoPrimary_card_of_finite, discriminantGroup_card G hG]

/-- The binary quotient `(M/2M) ⧸ image Γ` has dimension at most `v₂([M : Γ])`
(accepted `modTwoImage_quotient_finrank_le_index_factorization`). -/
theorem binaryQuotient_finrank_le_index_factorization {M : Type*} [AddCommGroup M]
    (Γ : AddSubgroup M) [Γ.FiniteIndex] :
    Module.finrank (ZMod 2) (ModTwo M ⧸ modTwoImage Γ) ≤ Γ.index.factorization 2 :=
  modTwoImage_quotient_finrank_le_index_factorization Γ

/-- Its order is a power of two dividing the index (accepted). -/
theorem binaryQuotient_two_pow_dvd_index {M : Type*} [AddCommGroup M]
    (Γ : AddSubgroup M) [Γ.FiniteIndex] :
    2 ^ Module.finrank (ZMod 2) (ModTwo M ⧸ modTwoImage Γ) ∣ Γ.index :=
  two_pow_modTwoImage_quotient_finrank_dvd_index Γ

end Primary

/-! ### Clause 4: orthogonal node discriminants -/

section Orthogonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant of an orthogonal (block-diagonal) sum is the product of the
determinants (pinned `Matrix.det_blockDiagonal`). -/
theorem discriminant_orthogonalSum {o : Type*} [Fintype o] [DecidableEq o]
    (Ms : o → Matrix ι ι ℤ) :
    (Matrix.blockDiagonal Ms).det = ∏ k, (Ms k).det :=
  Matrix.det_blockDiagonal Ms

/-- The same in absolute value: the discriminant of an orthogonal sum is the
product of the discriminants. -/
theorem discriminant_orthogonalSum_natAbs {o : Type*} [Fintype o] [DecidableEq o]
    (Ms : o → Matrix ι ι ℤ) :
    (Matrix.blockDiagonal Ms).det.natAbs = ∏ k, (Ms k).det.natAbs := by
  rw [Matrix.det_blockDiagonal]
  exact map_prod Int.natAbsHom _ _

/-- Two orthogonal summands (pinned `Matrix.det_fromBlocks_zero₂₁`). -/
theorem discriminant_orthogonalSum_two {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℤ) (D : Matrix κ κ ℤ) :
    (Matrix.fromBlocks A 0 0 D).det = A.det * D.det :=
  Matrix.det_fromBlocks_zero₂₁ A 0 D

/-- The Gram matrix of `ι`-many pairwise orthogonal nodes of square `-2`. -/
def nodeGram (ι : Type*) [Fintype ι] [DecidableEq ι] : Matrix ι ι ℤ :=
  Matrix.diagonal fun _ => -2

theorem nodeGram_det : (nodeGram ι).det = (-2) ^ Fintype.card ι := by
  rw [nodeGram, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ]

theorem nodeGram_det_natAbs : (nodeGram ι).det.natAbs = 2 ^ Fintype.card ι := by
  rw [nodeGram_det, Int.natAbs_pow]
  norm_num

theorem nodeGram_det_ne_zero : (nodeGram ι).det ≠ 0 := by
  rw [nodeGram_det]
  exact pow_ne_zero _ (by norm_num)

/-- Coordinatewise reduction modulo two. -/
def reduceModTwo (ι : Type*) : (ι → ℤ) →+ (ι → ZMod 2) where
  toFun x i := (x i : ZMod 2)
  map_zero' := by
    ext i
    simp
  map_add' x y := by
    ext i
    simp

omit [Fintype ι] [DecidableEq ι] in
theorem reduceModTwo_apply (x : ι → ℤ) (i : ι) : reduceModTwo ι x i = (x i : ZMod 2) := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem reduceModTwo_surjective : Function.Surjective (reduceModTwo ι) := by
  intro y
  refine ⟨fun i => ((y i).val : ℤ), ?_⟩
  ext i
  rw [reduceModTwo_apply, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- The kernel of reduction modulo two is the image lattice of `nodeGram`. -/
theorem ker_reduceModTwo :
    LinearMap.ker (reduceModTwo ι).toIntLinearMap = LinearMap.range (Matrix.toLin' (nodeGram ι)) := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hx
    refine ⟨fun i => -(x i / 2), ?_⟩
    ext i
    have hxi : ((x i : ℤ) : ZMod 2) = 0 := congr_fun hx i
    have hi : (2 : ℤ) ∣ x i := by
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (x i) 2).mp hxi
      exact_mod_cast h
    rw [Matrix.toLin'_apply, nodeGram, Matrix.mulVec_diagonal]
    show -2 * -(x i / 2) = x i
    have h2 := Int.mul_ediv_cancel' hi
    linarith
  · rintro ⟨y, rfl⟩
    ext i
    show (((Matrix.toLin' (nodeGram ι) y) i : ℤ) : ZMod 2) = 0
    rw [Matrix.toLin'_apply, nodeGram, Matrix.mulVec_diagonal]
    show (((-2 * y i : ℤ)) : ZMod 2) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨-y i, by push_cast; ring⟩

/-- **Orthogonal node discriminant.** The discriminant group of `ι`-many
orthogonal nodes of square `-2` is `(ℤ/2)^ι`. -/
noncomputable def nodeDiscriminantEquiv :
    discriminantGroup (nodeGram ι) ≃ₗ[ℤ] (ι → ZMod 2) :=
  (Submodule.quotEquivOfEq _ _ (ker_reduceModTwo (ι := ι))).symm.trans
    ((reduceModTwo ι).toIntLinearMap.quotKerEquivOfSurjective (reduceModTwo_surjective (ι := ι)))

theorem nodeDiscriminant_card : Nat.card (discriminantGroup (nodeGram ι)) = 2 ^ Fintype.card ι := by
  rw [Nat.card_congr (nodeDiscriminantEquiv (ι := ι)).toEquiv, Nat.card_pi, Finset.prod_const,
    Finset.card_univ, Nat.card_zmod]

/-- Consistency with the general order formula: `2^r = |det (nodeGram)|`. -/
theorem nodeDiscriminant_card_eq_det :
    Nat.card (discriminantGroup (nodeGram ι)) = (nodeGram ι).det.natAbs :=
  discriminantGroup_card _ nodeGram_det_ne_zero

end Orthogonal

/-! ### Clause 5: binary-kernel bounds and characteristic parity (accepted, re-exported) -/

section Codes

variable {M κ ι : Type*} [AddCommGroup M] [Fintype κ] [DecidableEq κ] [Fintype ι]

/-- **Binary-kernel dimension bound.** For a unimodular integral lattice, a
finite-index submodule `Γ` and node vectors pairing evenly with `Γ`, the code of
integral half-sums has dimension at least `#nodes − v₂([M : Γ])` (accepted
`integralNodeCode_finrank_ge_card_sub_index_factorization`). -/
theorem binaryKernel_finrank_ge (b : Basis κ ℤ M) (B : BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1)
    (Γ : Submodule ℤ M) [Γ.toAddSubgroup.FiniteIndex] (w : ι → M)
    (hpair : ∀ i y, y ∈ Γ → Even (B (w i) y)) :
    Fintype.card ι - Γ.toAddSubgroup.index.factorization 2 ≤
      Module.finrank (ZMod 2) (integralNodeCode w) :=
  IntegralNodeObstruction.integralNodeCode_finrank_ge_card_sub_index_factorization b B hB Γ w hpair

/-- More nodes than `v₂([M : Γ])` force a nonempty integral half-sum (accepted
`exists_nonempty_integral_half_sum_of_index_factorization_lt_card`). -/
theorem binaryKernel_exists_half_sum (b : Basis κ ℤ M) (B : BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1)
    (Γ : Submodule ℤ M) [Γ.toAddSubgroup.FiniteIndex] (w : ι → M)
    (hpair : ∀ i y, y ∈ Γ → Even (B (w i) y))
    (hcard : Γ.toAddSubgroup.index.factorization 2 < Fintype.card ι) :
    ∃ J : Finset ι, J.Nonempty ∧ ∃ m : M, (2 : ℤ) • m = ∑ i ∈ J, w i :=
  IntegralNodeObstruction.exists_nonempty_integral_half_sum_of_index_factorization_lt_card
    b B hB Γ w hpair hcard

omit [Fintype ι] in
/-- **Characteristic-vector parity.** An integral half-sum of pairwise orthogonal
`(-2)`-vectors orthogonal to a characteristic vector has `4 ∣ #summands`
(accepted `four_dvd_card_of_nodeHalfSum`). -/
theorem characteristic_parity_four_dvd [Module ℤ M] (B : BilinForm ℤ M) (K : M)
    (hchar : IsCharacteristic B K) (w : ι → M) (s : Finset ι)
    (hsq : ∀ i ∈ s, B (w i) (w i) = -2)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → B (w i) (w j) = 0)
    (hK : ∀ i ∈ s, B K (w i) = 0)
    (hdiv : ∃ m : M, (2 : ℤ) • m = ∑ i ∈ s, w i) : 4 ∣ s.card :=
  four_dvd_card_of_nodeHalfSum B K hchar w s hsq horth hK hdiv

/-- The half-sum code is doubly even and satisfies the dimension bound (accepted
`integralNodeCode_doublyEven_and_finrank_ge`). -/
theorem binaryKernel_doublyEven_and_finrank_ge (b : Basis κ ℤ M) (B : BilinForm ℤ M)
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
  IntegralNodeObstruction.integralNodeCode_doublyEven_and_finrank_ge b B hB Γ w hpair K hchar
    hsq horth hK

/-- Short doubly-even codes: trivial below length four, at most one-dimensional
in length four (accepted `doublyEvenCode_eq_bot_of_card_lt_four`,
`doublyEvenCode_finrank_le_one_of_card_eq_four`). -/
theorem doublyEvenCode_short (C : Submodule (ZMod 2) (BinaryWord ι)) (hC : DoublyEvenCode C) :
    (Fintype.card ι < 4 → C = ⊥) ∧ (Fintype.card ι = 4 → Module.finrank (ZMod 2) C ≤ 1) :=
  ⟨fun h => doublyEvenCode_eq_bot_of_card_lt_four C hC h,
    fun h => doublyEvenCode_finrank_le_one_of_card_eq_four C hC h⟩

/-- Three or four orthogonal nodes force `v₂([M : Γ]) ≥ 3` (accepted
`three_le_index_factorization_of_card_eq_three`, `..._four`). -/
theorem three_le_index_factorization_of_nodes (b : Basis κ ℤ M) (B : BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1)
    (Γ : Submodule ℤ M) [Γ.toAddSubgroup.FiniteIndex] (w : ι → M)
    (hpair : ∀ i y, y ∈ Γ → Even (B (w i) y))
    (K : M) (hchar : IsCharacteristic B K)
    (hsq : ∀ i, B (w i) (w i) = -2)
    (horth : ∀ i j, i ≠ j → B (w i) (w j) = 0)
    (hK : ∀ i, B K (w i) = 0) (hcard : Fintype.card ι = 3 ∨ Fintype.card ι = 4) :
    3 ≤ Γ.toAddSubgroup.index.factorization 2 := by
  rcases hcard with h | h
  · exact IntegralNodeObstruction.three_le_index_factorization_of_card_eq_three b B hB Γ w hpair
      K hchar hsq horth hK h
  · exact IntegralNodeObstruction.three_le_index_factorization_of_card_eq_four b B hB Γ w hpair
      K hchar hsq horth hK h

end Codes

/-! ### The bundle -/

/-- **A02 core.** Index-square determinant in a unimodular lattice; the
discriminant group `ℤ^ι / G ℤ^ι` of a nonsingular integral matrix has order
`|det G|`, as does `M^∨ / B(M)` for a nondegenerate form; the `2`-primary part
of a finite abelian group has order `2^{v₂}` of its order, in particular for
`M ⧸ Γ`; the discriminant of an orthogonal sum is the product and `r`
orthogonal `(-2)`-nodes have discriminant group `(ℤ/2)^r` of order `2^r`; the
binary-kernel dimension bound, the forced half-sum, and characteristic parity. -/
theorem a02 :
    (∀ {M : Type u} {ι : Type v} [AddCommGroup M] [Fintype ι] [DecidableEq ι]
      (B : BilinForm ℤ M) (b : Basis ι ℤ M) (N : Submodule ℤ M) (bN : Basis ι ℤ N),
      (BilinForm.toMatrix b B).det.natAbs = 1 →
        (BilinForm.toMatrix bN (B.comp N.subtype N.subtype)).det.natAbs =
          N.toAddSubgroup.index ^ 2) ∧
    (∀ {ι : Type v} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℤ), G.det ≠ 0 →
      Finite (discriminantGroup G) ∧ Nat.card (discriminantGroup G) = G.det.natAbs) ∧
    (∀ {M : Type u} {ι : Type v} [AddCommGroup M] [Fintype ι] [DecidableEq ι]
      (b : Basis ι ℤ M) (B : BilinForm ℤ M), (BilinForm.toMatrix b B).det ≠ 0 →
        Nat.card (Module.Dual ℤ M ⧸ LinearMap.range B) = (BilinForm.toMatrix b B).det.natAbs) ∧
    (∀ {A : Type u} [AddCommGroup A] [Finite A],
      Nat.card (AddCommGroup.primaryComponent A 2) = 2 ^ (Nat.card A).factorization 2) ∧
    (∀ {M : Type u} [AddCommGroup M] (Γ : AddSubgroup M) [Γ.FiniteIndex],
      Nat.card (AddCommGroup.primaryComponent (M ⧸ Γ) 2) = 2 ^ Γ.index.factorization 2 ∧
      Module.finrank (ZMod 2) (ModTwo M ⧸ modTwoImage Γ) ≤ Γ.index.factorization 2) ∧
    (∀ {ι o : Type v} [Fintype ι] [DecidableEq ι] [Fintype o] [DecidableEq o]
      (Ms : o → Matrix ι ι ℤ), (Matrix.blockDiagonal Ms).det.natAbs = ∏ k, (Ms k).det.natAbs) ∧
    (∀ {ι : Type v} [Fintype ι] [DecidableEq ι],
      Nonempty (discriminantGroup (nodeGram ι) ≃ₗ[ℤ] (ι → ZMod 2)) ∧
      Nat.card (discriminantGroup (nodeGram ι)) = 2 ^ Fintype.card ι ∧
      (nodeGram ι).det.natAbs = 2 ^ Fintype.card ι) ∧
    (∀ {M : Type u} {κ ι : Type v} [AddCommGroup M] [Fintype κ] [DecidableEq κ] [Fintype ι]
      (b : Basis κ ℤ M) (B : BilinForm ℤ M), (BilinForm.toMatrix b B).det.natAbs = 1 →
      ∀ (Γ : Submodule ℤ M) [Γ.toAddSubgroup.FiniteIndex] (w : ι → M),
        (∀ i y, y ∈ Γ → Even (B (w i) y)) →
          Fintype.card ι - Γ.toAddSubgroup.index.factorization 2 ≤
              Module.finrank (ZMod 2) (integralNodeCode w) ∧
            (Γ.toAddSubgroup.index.factorization 2 < Fintype.card ι →
              ∃ J : Finset ι, J.Nonempty ∧ ∃ m : M, (2 : ℤ) • m = ∑ i ∈ J, w i)) ∧
    (∀ {M : Type u} {ι : Type v} [AddCommGroup M] [Module ℤ M] (B : BilinForm ℤ M) (K : M),
      IsCharacteristic B K → ∀ (w : ι → M) (s : Finset ι),
        (∀ i ∈ s, B (w i) (w i) = -2) → (∀ i ∈ s, ∀ j ∈ s, i ≠ j → B (w i) (w j) = 0) →
        (∀ i ∈ s, B K (w i) = 0) → (∃ m : M, (2 : ℤ) • m = ∑ i ∈ s, w i) → 4 ∣ s.card) :=
  ⟨fun B b N bN h => picard_fullLattice_indexSquare B b N bN h,
    fun G hG => ⟨discriminantGroup_finite G hG, discriminantGroup_card G hG⟩,
    fun b B hB => dualQuotient_card b B hB,
    fun {_} [_] [_] => twoPrimary_card_of_finite,
    fun Γ _ => ⟨twoPrimary_card_quotient_index Γ, binaryQuotient_finrank_le_index_factorization Γ⟩,
    fun Ms => discriminant_orthogonalSum_natAbs Ms,
    fun {_} [_] [_] => ⟨⟨nodeDiscriminantEquiv⟩, nodeDiscriminant_card, nodeGram_det_natAbs⟩,
    fun b B hB Γ _ w hpair =>
      ⟨binaryKernel_finrank_ge b B hB Γ w hpair,
        fun hcard => binaryKernel_exists_half_sum b B hB Γ w hpair hcard⟩,
    fun B K hchar w s hsq horth hK hdiv =>
      characteristic_parity_four_dvd B K hchar w s hsq horth hK hdiv⟩

end KltDP.Support

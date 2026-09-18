import KltDP.Manuscript.Datum.ResolutionDatum
import KltDP.Geometry.IsolatedNodeVanishing
import KltDP.Geometry.KltIsolatedNodePicardIndex
import KltDP.Geometry.ExceptionalExteriorPicardSpan
import KltDP.Geometry.CanonicalPicardCharacteristic
import KltDP.Geometry.KltExceptionalOrthogonalPositive
import KltDP.Geometry.UnimodularPicardFiniteBasis
import KltDP.Geometry.IsolatedNodePicardPairing
import KltDP.Lattices.TenRowPicardExclusions
import KltDP.LinearAlgebra.SchurComplement
import KltDP.Support.SchurStieltjesLoewner
import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Section 5.2 of the manuscript: the full-index obstruction from isolated nodes

Manuscript `source/manuscript.tex`, Lemma 5.2 (`lem:picard-index`, lines 1342–1392), for the
resolution datum `R = (S, D, L)` of a rank-one klt del Pezzo surface and an exterior
`(−1)`-curve `P ⊂ S`.

The main outputs are:

* `exists_picard_lattice_data`: the integral Picard lattice `Λ = Pic S` (written additively,
  `Additive R.S.toScheme.Pic`) with its intersection form
  `R.S.integralPicardIntersectionBilinForm R.hreg` carries a basis indexed by
  `R.Vertices ⊕ Unit` with unimodular Gram determinant; the class of `K_S` is characteristic
  (Riemann–Roch parity) with `K_S · D_i = b_i − 2`; and the Gram matrix of the family
  `(D_i, P)` is the bordered matrix `borderedGram R.A p (−1)` with `p_i = P · D_i`.
* `index_sq_eq_det_mul` (5.2(i)): `I² = det A · (g − 1)` for `I = [Pic S : ⟨D, P⟩]` and
  `g = pᵀ A⁻¹ p`; the sign uses the Hodge-index positivity of the exceptional complement
  (`one_lt_green`, the strict Green inequality `g > 1` of manuscript `lem:projection`).
* `isolated_nodes_card_le_index` (5.2(ii)): a set of `t` isolated exceptional nodes disjoint
  from `P` satisfies `t ≤ v₂(I)` in characteristic `p > 2` (via Theorem 5.1 of the union).
* `det_mul_green_sub_one_is_square` (5.2(iii)): `det A · (g − 1)` is a positive integer square.
* `isolated_nodes_no_half_sum`: Theorem 5.1 in the class form used by Section 8: no nonempty
  set of isolated nodes has a sum divisible by two in `Pic S`.

An *isolated node* is a vertex `W : R.Vertices` with `R.w W = 2` and no neighbour in `R.graph`.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Codes KltDP.LinearAlgebra KltDP.Lattices.SmallADEForestLattice
open KltDP.Lattices.TenRowPicardExclusions
open scoped BigOperators

universe u

namespace KltDP.Manuscript.S05

section DetPos

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [StarRing 𝕜] [TrivialStar 𝕜]

/-- Positive-definite matrices over an ordered field with trivial star have positive determinant
(the pinned `Matrix.PosDef.det_pos` requires `RCLike`, so it is unavailable over `ℚ`). Proof by
Schur-complement induction on the finite index type, using the union's Schur lemmas. -/
theorem det_pos_of_posDef (ι : Type u) [Fintype ι] :
    ∀ [DecidableEq ι] (A : Matrix ι ι 𝕜), A.PosDef → 0 < A.det := by
  refine Fintype.induction_empty_option
    (P := fun α _ => ∀ [DecidableEq α] (A : Matrix α α 𝕜), A.PosDef → 0 < A.det) ?_ ?_ ?_ ι
  · intro α β _ e hα _ A hA
    letI : Fintype α := Fintype.ofEquiv β e.symm
    letI : DecidableEq α := e.injective.decidableEq
    have h := hα (A.submatrix e e)
      (KltDP.LinearAlgebra.posDef_principal_submatrix hA e e.injective)
    rwa [Matrix.det_submatrix_equiv_self] at h
  · intro _ A _
    rw [Matrix.det_isEmpty]
    exact zero_lt_one
  · intro α _ ih _ A hA
    letI : DecidableEq α := (Option.some_injective α).decidableEq
    let e : Option α ≃ α ⊕ PUnit.{u+1} := Equiv.optionEquivSumPUnit α
    let M : Matrix (α ⊕ PUnit.{u+1}) (α ⊕ PUnit.{u+1}) 𝕜 := A.submatrix e.symm e.symm
    have hM : M.PosDef :=
      KltDP.LinearAlgebra.posDef_principal_submatrix hA e.symm e.symm.injective
    have hdet : A.det = (fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂).det := by
      rw [Matrix.fromBlocks_toBlocks]
      exact (Matrix.det_submatrix_equiv_self e.symm A).symm
    have hM' : (fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂).PosDef := by
      rw [Matrix.fromBlocks_toBlocks]
      exact hM
    obtain ⟨h11, _⟩ := KltDP.Support.F26.principal_blocks_posDef hM'
    rw [hdet, KltDP.Support.F26.schurComplement_det h11]
    apply mul_pos (ih _ h11)
    have hS := KltDP.Support.F26.schurComplement_positiveDefinite' hM'
    rw [Matrix.det_unique]
    exact KltDP.Support.F26.posDef_diag_pos hS default

end DetPos

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)

local instance integralSource (T : NormalProjectiveSurface k) : IsIntegral T.toScheme := T.integral

/-! ### The classes -/

/-- The Picard class `[C] ∈ Pic S` (written additively) of a prime curve `C ⊂ S`. -/
def primeClass (C : R.S.PrimeCurve) : Additive R.S.toScheme.Pic :=
  Additive.ofMul (cartierPicardClass R.S.toScheme (R.S.primeCurveCartier R.hreg C))

/-- The Picard classes `[D_i]` of the exceptional curves. -/
def cls (i : R.Vertices) : Additive R.S.toScheme.Pic := primeClass R i.val

/-- The class of the canonical divisor `K_S`. -/
def Kcls : Additive R.S.toScheme.Pic := cartierPicardHom R.S.toScheme R.KS

/-- The contact vector `p_i = P · D_i` (rational entries). -/
def contact (P : R.S.PrimeCurve) (i : R.Vertices) : ℚ :=
  (P.intersectionNumber (R.S.primeCurveCartier R.hreg i.val) : ℚ)

/-- The family `(D_i, P)` indexed by `R.Vertices ⊕ Unit`. -/
def family (P : R.S.PrimeCurve) : R.Vertices ⊕ Unit → Additive R.S.toScheme.Pic :=
  Sum.elim (cls R) (fun _ => primeClass R P)

/-- The exceptional curves of a finset of vertices, as a finset of prime curves. -/
def nodeFinset (N : Finset R.Vertices) : Finset R.S.PrimeCurve :=
  N.map ⟨Subtype.val, Subtype.val_injective⟩

theorem mem_nodeFinset (N : Finset R.Vertices) (C : R.S.PrimeCurve) :
    C ∈ nodeFinset R N ↔ ∃ W ∈ N, W.val = C := by
  simp [nodeFinset, Finset.mem_map]

theorem card_nodeFinset (N : Finset R.Vertices) : (nodeFinset R N).card = N.card :=
  Finset.card_map _

/-! ### Pairings of the classes -/

theorem pairing_primeClass (C D : R.S.PrimeCurve) :
    R.S.integralPicardIntersectionBilinForm R.hreg (primeClass R C) (primeClass R D) =
      R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg C)
        (R.S.primeCurveCartier R.hreg D) := by
  rw [integralPicardIntersectionBilinForm_apply]
  simp only [primeClass, toMul_ofMul]
  exact R.S.picardPairing_class R.hreg _ _

theorem pairing_cls (i j : R.Vertices) :
    (R.S.integralPicardIntersectionBilinForm R.hreg (cls R i) (cls R j) : ℚ) = R.M i j := by
  simp only [cls]
  rw [pairing_primeClass]
  rfl

theorem pairing_cls_prime (P : R.S.PrimeCurve) (i : R.Vertices) :
    (R.S.integralPicardIntersectionBilinForm R.hreg (cls R i) (primeClass R P) : ℚ) =
      contact R P i := by
  simp only [cls, contact]
  rw [pairing_primeClass, R.S.intersectionPairing_primeCurve R.hreg]

theorem pairing_prime_cls (P : R.S.PrimeCurve) (j : R.Vertices) :
    (R.S.integralPicardIntersectionBilinForm R.hreg (primeClass R P) (cls R j) : ℚ) =
      contact R P j := by
  simp only [cls, contact]
  rw [pairing_primeClass, R.S.intersectionPairing_symm R.hreg,
    R.S.intersectionPairing_primeCurve R.hreg]

theorem pairing_prime_self (P : R.S.PrimeCurve) (hP : IsMinusOneCurve R.hreg P) :
    R.S.integralPicardIntersectionBilinForm R.hreg (primeClass R P) (primeClass R P) = -1 := by
  rw [pairing_primeClass, R.S.intersectionPairing_primeCurve R.hreg]
  exact hP.selfIntersection

/-- `b_i = -D_i²`, in terms of the actual self-intersection number. -/
theorem w_eq_neg_selfIntersection (i : R.Vertices) :
    R.w i = -(i.val.selfIntersectionNumber R.hreg : ℚ) := by
  change -(R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.val)
    (R.S.primeCurveCartier R.hreg i.val) : ℚ) = _
  rw [R.S.intersectionPairing_primeCurve R.hreg]
  rfl

/-- Adjunction on the rational exceptional curves: `K_S · D_i = b_i − 2`. -/
theorem pairing_Kcls_cls (i : R.Vertices) :
    (R.S.integralPicardIntersectionBilinForm R.hreg (Kcls R) (cls R i) : ℚ) = R.w i - 2 := by
  obtain ⟨e, he⟩ := R.exceptional_rational i.val i.property
  have hadj := CompatibleRationalAdjunctionDegree.canonical_intersection_eq
    R.S R.hreg R.KS R.eKS i.val e he
  rw [w_eq_neg_selfIntersection, integralPicardIntersectionBilinForm_apply]
  simp only [Kcls, cls, primeClass, cartierPicardHom_apply, toMul_ofMul]
  rw [R.S.picardPairing_class R.hreg, R.S.intersectionPairing_primeCurve R.hreg, hadj]
  push_cast
  ring

/-- Riemann–Roch parity: the canonical class is characteristic for the intersection form. -/
theorem Kcls_isCharacteristic :
    IsCharacteristic (R.S.integralPicardIntersectionBilinForm R.hreg) (Kcls R) :=
  R.S.canonicalPicard_isCharacteristic R.hreg R.KS R.eKS

/-- The Gram matrix of `(D_i, P)` is the bordered matrix `Q_Γ = [[-A, p], [pᵀ, -1]]`. -/
theorem familyGram_eq_borderedGram (P : R.S.PrimeCurve) (hP : IsMinusOneCurve R.hreg P) :
    (familyGram (R.S.integralPicardIntersectionBilinForm R.hreg)
      (Sum.elim (cls R) (fun _ : Unit => primeClass R P))).map (fun z : ℤ => (z : ℚ)) =
      borderedGram R.A (contact R P) (-1) := by
  ext i j
  rcases i with i | u <;> rcases j with j | v
  · simp only [Matrix.map_apply, familyGram, Sum.elim_inl, borderedGram,
      Matrix.fromBlocks_apply₁₁, pairing_cls, ResolutionDatum.A, Matrix.neg_apply, neg_neg]
  · simp only [Matrix.map_apply, familyGram, Sum.elim_inl, Sum.elim_inr, borderedGram,
      Matrix.fromBlocks_apply₁₂, pairing_cls_prime]
  · simp only [Matrix.map_apply, familyGram, Sum.elim_inl, Sum.elim_inr, borderedGram,
      Matrix.fromBlocks_apply₂₁, pairing_prime_cls]
  · simp only [Matrix.map_apply, familyGram, Sum.elim_inr, borderedGram,
      Matrix.fromBlocks_apply₂₂, pairing_prime_self R P hP, Int.cast_neg, Int.cast_one]

/-- The same Gram identity with `A` written as the weighted graph matrix of the dual graph. -/
theorem familyGram_eq_borderedGram_graph [DecidableEq R.Vertices] [DecidableRel R.graph.Adj]
    (P : R.S.PrimeCurve) (hP : IsMinusOneCurve R.hreg P) :
    (familyGram (R.S.integralPicardIntersectionBilinForm R.hreg)
      (Sum.elim (cls R) (fun _ : Unit => primeClass R P))).map (fun z : ℤ => (z : ℚ)) =
      borderedGram (graphWeightMatrix R.graph R.w) (contact R P) (-1) := by
  rw [familyGram_eq_borderedGram R P hP, R.A_eq_graphWeightMatrix]

/-! ### Unimodularity, rank, and the basis indexed by `R.Vertices ⊕ Unit` -/

theorem picardUnimodular (p : ℕ) [CharP k p] (hp : 0 < p) : R.S.PicardUnimodular R.hreg :=
  (R.hmin.picard_and_structure_invariants_of_kltDelPezzo R.hDP R.hrank p hp).1

/-- `rank_ℤ Pic S = ρ(S) = r + 1`: the integral Picard rank is the number of exceptional
curves plus one. -/
theorem finrank_pic (p : ℕ) [CharP k p] (hp : 0 < p) :
    Module.finrank ℤ (Additive R.S.toScheme.Pic) = Fintype.card R.Vertices + 1 := by
  have hU := picardUnimodular R p hp
  have h1 : Module.finrank ℤ (Additive R.S.toScheme.Pic) =
      Module.finrank ℤ R.S.IntegralNumericalClassGroup :=
    (R.S.picardIntegralNumericalEquiv_of_picardUnimodular R.hreg hU).finrank_eq
  have h2 : Module.finrank ℤ R.S.NumericalClassGroup =
      Module.finrank ℤ R.S.IntegralNumericalClassGroup :=
    IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ) R.S.integralNumericalRationalization le_rfl
  have h3 : Module.rank ℚ R.S.NumericalClassGroup = Module.rank ℤ R.S.NumericalClassGroup :=
    IsLocalization.rank_eq ℚ (nonZeroDivisors ℤ) le_rfl
  have h4 : R.S.picardRank = Module.finrank ℤ R.S.NumericalClassGroup := by
    change Cardinal.toNat (Module.rank ℚ R.S.NumericalClassGroup) =
      Cardinal.toNat (Module.rank ℤ R.S.NumericalClassGroup)
    rw [h3]
  have h5 := R.hmin.picardRank_eq_of_klt R.hklt p hp
  rw [R.hrank] at h5
  have h6 : Nat.card (ActualExceptionalIncidence.Vertices R.π) = Fintype.card R.Vertices :=
    Nat.card_eq_fintype_card
  omega

/-- A basis of the integral Picard lattice indexed by `R.Vertices ⊕ Unit`, with unimodular
Gram determinant of the intersection form. -/
theorem exists_basis_unimodular [DecidableEq R.Vertices] (p : ℕ) [CharP k p] (hp : 0 < p) :
    ∃ b : Basis (R.Vertices ⊕ Unit) ℤ (Additive R.S.toScheme.Pic),
      (BilinForm.toMatrix b (R.S.integralPicardIntersectionBilinForm R.hreg)).det.natAbs = 1 := by
  classical
  have hU := picardUnimodular R p hp
  obtain ⟨hfree, hfin⟩ := R.S.picard_free_and_finite_of_picardUnimodular R.hreg hU
  letI := hfree
  letI := hfin
  have hcard : Fintype.card (Fin (Module.finrank ℤ (Additive R.S.toScheme.Pic))) =
      Fintype.card (R.Vertices ⊕ Unit) := by
    rw [Fintype.card_fin, Fintype.card_sum, Fintype.card_unit, finrank_pic R p hp]
  refine ⟨(Module.finBasis ℤ (Additive R.S.toScheme.Pic)).reindex (Fintype.equivOfCardEq hcard), ?_⟩
  exact KltDP.Lattices.PerfectIntegralGram.toMatrix_det_natAbs_eq_one _ _
    (R.S.integralPicardIntersectionBilinForm_bijective_of_picardUnimodular R.hreg hU)

/-- **The Picard lattice data of the resolution datum** (the input of the Section 8 endgame
`ten_forest_integral_half_sum`): a unimodular basis indexed by `R.Vertices ⊕ Unit`, the
characteristic canonical class with `K_S · D_i = b_i − 2`, and the bordered Gram matrix of
`(D_i, P)` for an exterior `(−1)`-curve `P`. -/
theorem exists_picard_lattice_data [DecidableEq R.Vertices] (p : ℕ) [CharP k p] (hp : 0 < p)
    (P : R.S.PrimeCurve) (hP : IsMinusOneCurve R.hreg P) :
    ∃ b : Basis (R.Vertices ⊕ Unit) ℤ (Additive R.S.toScheme.Pic),
      (BilinForm.toMatrix b (R.S.integralPicardIntersectionBilinForm R.hreg)).det.natAbs = 1 ∧
      IsCharacteristic (R.S.integralPicardIntersectionBilinForm R.hreg) (Kcls R) ∧
      (∀ x : R.Vertices,
        (R.S.integralPicardIntersectionBilinForm R.hreg (Kcls R) (cls R x) : ℚ) = R.w x - 2) ∧
      (familyGram (R.S.integralPicardIntersectionBilinForm R.hreg)
        (Sum.elim (cls R) (fun _ : Unit => primeClass R P))).map (fun z : ℤ => (z : ℚ)) =
        borderedGram R.A (contact R P) (-1) := by
  obtain ⟨b, hb⟩ := exists_basis_unimodular R p hp
  exact ⟨b, hb, Kcls_isCharacteristic R, pairing_Kcls_cls R, familyGram_eq_borderedGram R P hP⟩

/-! ### Linear independence of `(D_i, P)` and the span `Γ = ⟨D, P⟩` -/

/-- The numerical classes of `(D_i, P)` form a `ℚ`-basis of `N¹(S)_ℚ`. -/
theorem numerical_family_linearIndependent (p : ℕ) [CharP k p] (hp : 0 < p)
    (P : R.S.PrimeCurve) (hPext : ¬ IsExceptionalCurve R.π P) :
    LinearIndependent ℚ (Sum.elim
      (fun i : R.Vertices => DisjointNegativeCurvesRank.curveClass R.S R.hreg i.val)
      (fun _ : Unit => DisjointNegativeCurvesRank.curveClass R.S R.hreg P)) := by
  letI : Module.Finite ℚ R.S.NumericalClassGroup :=
    SurfaceNumericalFinitenessProved.numericalClassGroup_finite R.S R.hreg
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · rw [Set.Sum.elim_range, Set.range_const, Set.union_singleton]
    exact (R.hmin.exceptional_exterior_numerical_span_eq_top R.hDP R.hrank p hp P hPext).ge
  · rw [Fintype.card_sum, Fintype.card_unit]
    have h5 := R.hmin.picardRank_eq_of_klt R.hklt p hp
    rw [R.hrank] at h5
    have h6 : Nat.card (ActualExceptionalIncidence.Vertices R.π) = Fintype.card R.Vertices :=
      Nat.card_eq_fintype_card
    change _ = R.S.picardRank
    omega

/-- The classes `(D_i, P)` are `ℤ`-linearly independent in `Pic S`. -/
theorem family_linearIndependent (p : ℕ) [CharP k p] (hp : 0 < p)
    (P : R.S.PrimeCurve) (hPext : ¬ IsExceptionalCurve R.π P) :
    LinearIndependent ℤ (Sum.elim (cls R) (fun _ : Unit => primeClass R P)) := by
  have hQ := numerical_family_linearIndependent R p hp P hPext
  have hZ : LinearIndependent ℤ (Sum.elim
      (fun i : R.Vertices => DisjointNegativeCurvesRank.curveClass R.S R.hreg i.val)
      (fun _ : Unit => DisjointNegativeCurvesRank.curveClass R.S R.hreg P)) :=
    hQ.restrict_scalars (by
      intro a b hab
      simp only [Int.smul_one_eq_cast] at hab
      exact_mod_cast hab)
  refine LinearIndependent.of_comp R.S.picardNumericalMap ?_
  have hcomp : R.S.picardNumericalMap ∘ Sum.elim (cls R) (fun _ : Unit => primeClass R P) =
      Sum.elim (fun i : R.Vertices => DisjointNegativeCurvesRank.curveClass R.S R.hreg i.val)
        (fun _ : Unit => DisjointNegativeCurvesRank.curveClass R.S R.hreg P) := by
    funext j
    rcases j with j | u <;> rfl
  rw [hcomp]
  exact hZ

theorem range_family (P : R.S.PrimeCurve) :
    Set.range (Sum.elim (cls R) (fun _ : Unit => primeClass R P)) =
      insert (primeClass R P) (Set.range (cls R)) := by
  rw [Set.Sum.elim_range, Set.range_const, Set.union_singleton]

/-- `Γ = ⟨D, P⟩` is the span of the family `(D_i, P)`. -/
theorem span_range_family (P : R.S.PrimeCurve) :
    Submodule.span ℤ (Set.range (Sum.elim (cls R) (fun _ : Unit => primeClass R P))) =
      R.S.exceptionalExteriorPicardSpan R.π R.hreg P := by
  rw [range_family]
  rfl

instance finiteIndex_exceptionalExteriorPicardSpan (p : ℕ) [CharP k p] [NeZero p]
    (P : R.S.PrimeCurve) (hPext : ¬ IsExceptionalCurve R.π P) :
    (R.S.exceptionalExteriorPicardSpan R.π R.hreg P).toAddSubgroup.FiniteIndex :=
  R.hmin.exceptional_exterior_picard_span_finiteIndex R.hDP R.hrank p (NeZero.pos p) P hPext

/-! ### 5.2(i): `I² = |det Γ| = det A · (g − 1)` -/

/-- `I² = |det Gram(D, P)|`, for `I = [Pic S : ⟨D, P⟩]`. -/
theorem index_sq_eq_natAbs_det [DecidableEq R.Vertices] (p : ℕ) [CharP k p] (hp : 0 < p)
    (P : R.S.PrimeCurve) (hPext : ¬ IsExceptionalCurve R.π P) :
    (R.S.exceptionalExteriorPicardSpan R.π R.hreg P).toAddSubgroup.index ^ 2 =
      (familyGram (R.S.integralPicardIntersectionBilinForm R.hreg)
        (Sum.elim (cls R) (fun _ : Unit => primeClass R P))).det.natAbs := by
  classical
  obtain ⟨b, hb⟩ := exists_basis_unimodular R p hp
  rw [← span_range_family]
  exact (familyGram_natAbs_det_eq_span_index_sq b _ hb _
    (family_linearIndependent R p hp P hPext)).symm

/-- `I² = |det Q_Γ|` with `Q_Γ` the bordered rational matrix. -/
theorem index_sq_eq_abs_det_borderedGram [DecidableEq R.Vertices] (p : ℕ) [CharP k p]
    (hp : 0 < p)
    (P : R.S.PrimeCurve) (hP : IsMinusOneCurve R.hreg P) (hPext : ¬ IsExceptionalCurve R.π P) :
    (((R.S.exceptionalExteriorPicardSpan R.π R.hreg P).toAddSubgroup.index : ℕ) : ℚ) ^ 2 =
      |(borderedGram R.A (contact R P) (-1)).det| := by
  classical
  have h := index_sq_eq_natAbs_det R p hp P hPext
  have hcast : (((familyGram (R.S.integralPicardIntersectionBilinForm R.hreg)
      (Sum.elim (cls R) (fun _ : Unit => primeClass R P))).det.natAbs : ℕ) : ℚ) =
      |(borderedGram R.A (contact R P) (-1)).det| := by
    rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_det, familyGram_eq_borderedGram R P hP]
  rw [← hcast, ← h]
  push_cast
  ring

/-- The strict Green inequality `g = pᵀ A⁻¹ p > 1` (manuscript `lem:projection`): the corrected
class `P + Σ (A⁻¹p)_i D_i` is a nonzero numerical class orthogonal to all exceptional curves,
hence has positive square by the Hodge index theorem on the rank-one klt resolution. -/
theorem one_lt_green [DecidableEq R.Vertices] (p : ℕ) [CharP k p] (hp : 0 < p)
    (P : R.S.PrimeCurve) (hP : IsMinusOneCurve R.hreg P) (hPext : ¬ IsExceptionalCurve R.π P) :
    1 < dotProduct (contact R P) (R.A⁻¹ *ᵥ contact R P) := by
  classical
  have hA : IsUnit R.A := KltDP.LinearAlgebra.isUnit_of_posDef R.A_posDef
  let pv : R.Vertices → ℚ := contact R P
  let x : R.Vertices ⊕ Unit → ℚ := orthogonalCorrection R.A pv
  let v : R.Vertices ⊕ Unit → Additive R.S.toScheme.Pic :=
    Sum.elim (cls R) (fun _ : Unit => primeClass R P)
  let u : R.Vertices ⊕ Unit → R.S.NumericalClassGroup := fun j => R.S.picardNumericalMap (v j)
  let B := R.S.numericalIntersectionBilinForm R.hreg
  let Q : Matrix (R.Vertices ⊕ Unit) (R.Vertices ⊕ Unit) ℚ := borderedGram R.A pv (-1)
  have hQ : ∀ j l, B (u j) (u l) = Q j l := by
    intro j l
    have h := congr_fun (congr_fun (familyGram_eq_borderedGram R P hP) j) l
    rw [Matrix.map_apply] at h
    change B (R.S.picardNumericalMap (v j)) (R.S.picardNumericalMap (v l)) = Q j l
    rw [R.S.numericalIntersectionBilinForm_picard R.hreg, ← integralPicardIntersectionBilinForm_apply]
    exact h
  let c : R.S.NumericalClassGroup := ∑ j, x j • u j
  have hrow : ∀ l, B (u l) c = (Q *ᵥ x) l := by
    intro l
    simp only [c, map_sum, map_smul, smul_eq_mul, hQ, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hQx : Q *ᵥ x = Sum.elim (0 : R.Vertices → ℚ) (fun _ => -1 + dotProduct pv (R.A⁻¹ *ᵥ pv)) :=
    borderedGram_mulVec_orthogonalCorrection hA pv (-1)
  have hsymm := R.S.numericalIntersectionBilinForm_isSymm R.hreg
  have hc_orth : c ∈ ActualExceptionalNumerical.exceptionalOrthogonal R.π := by
    rw [ActualExceptionalNumerical.mem_exceptionalOrthogonal_iff]
    intro E
    rw [← DisjointNegativeCurvesRank.pairing_curveClass R.S R.hreg c E.val]
    change B c (u (Sum.inl E)) = 0
    rw [hsymm.eq, hrow, hQx]
    rfl
  have hcc : B c c = -1 + dotProduct pv (R.A⁻¹ *ᵥ pv) := by
    have h1 : B c c = dotProduct x (Q *ᵥ x) := by
      have : B c c = ∑ l, x l * B (u l) c := by
        simp only [c, LinearMap.BilinForm.sum_left, LinearMap.BilinForm.smul_left, smul_eq_mul]
      rw [this]
      simp only [dotProduct, hrow]
    rw [h1]
    exact orthogonalCorrection_square hA pv (-1)
  have hc_ne : c ≠ 0 := by
    intro h0
    have hli := numerical_family_linearIndependent R p hp P hPext
    have hu : u = Sum.elim
        (fun i : R.Vertices => DisjointNegativeCurvesRank.curveClass R.S R.hreg i.val)
        (fun _ : Unit => DisjointNegativeCurvesRank.curveClass R.S R.hreg P) := by
      funext j
      rcases j with j | j <;> rfl
    rw [← hu] at hli
    have hx := Fintype.linearIndependent_iff.mp hli x h0 (Sum.inr ())
    simp [x, orthogonalCorrection] at hx
  have hpos := R.hmin.exceptionalOrthogonal_square_pos_of_kltDelPezzo R.hDP p hp R.hrank c hc_orth hc_ne
  change 0 < B c c at hpos
  rw [hcc] at hpos
  linarith

/-- **5.2(i)**: `I² = det A · (g − 1)`, with `I = [Pic S : ⟨D, P⟩]` and `g = pᵀ A⁻¹ p`. -/
theorem index_sq_eq_det_mul [DecidableEq R.Vertices] (p : ℕ) [CharP k p] (hp : 0 < p)
    (P : R.S.PrimeCurve) (hP : IsMinusOneCurve R.hreg P) (hPext : ¬ IsExceptionalCurve R.π P) :
    (((R.S.exceptionalExteriorPicardSpan R.π R.hreg P).toAddSubgroup.index : ℕ) : ℚ) ^ 2 =
      R.A.det * (dotProduct (contact R P) (R.A⁻¹ *ᵥ contact R P) - 1) := by
  classical
  rw [index_sq_eq_abs_det_borderedGram R p hp P hP hPext,
    det_minusOne_borderedGram (KltDP.LinearAlgebra.isUnit_of_posDef R.A_posDef), abs_mul, abs_mul,
    abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (det_pos_of_posDef R.Vertices R.A R.A_posDef),
    abs_of_pos (sub_pos.mpr (one_lt_green R p hp P hP hPext))]

/-- **5.2(iii)**: `det A · (g − 1)` is a positive integer square. -/
theorem det_mul_green_sub_one_is_square [DecidableEq R.Vertices] (p : ℕ) [CharP k p]
    (hp : 0 < p)
    (P : R.S.PrimeCurve) (hP : IsMinusOneCurve R.hreg P) (hPext : ¬ IsExceptionalCurve R.π P) :
    ∃ I : ℕ, 0 < I ∧
      R.A.det * (dotProduct (contact R P) (R.A⁻¹ *ᵥ contact R P) - 1) = (I : ℚ) ^ 2 := by
  haveI : NeZero p := ⟨Nat.pos_iff_ne_zero.mp hp⟩
  refine ⟨(R.S.exceptionalExteriorPicardSpan R.π R.hreg P).toAddSubgroup.index, ?_,
    (index_sq_eq_det_mul R p hp P hP hPext).symm⟩
  exact Nat.pos_of_ne_zero
    (finiteIndex_exceptionalExteriorPicardSpan R p P hPext).index_ne_zero

/-! ### Isolated nodes -/

/-- Two distinct non-adjacent exceptional curves are disjoint. -/
theorem disjoint_of_not_adj {W v : R.Vertices} (hne : W ≠ v) (h : ¬ R.graph.Adj W v) :
    Disjoint (W.val : Set R.S.toScheme) (v.val : Set R.S.toScheme) := by
  rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
  intro hn
  exact h ⟨hne, hn⟩

/-- A finset of isolated vertices is an `IsolatedSelection` of prime curves. -/
theorem isolatedSelection_nodeFinset (N : Finset R.Vertices)
    (hiso : ∀ W ∈ N, ∀ y, ¬ R.graph.Adj W y) :
    UnbranchedExceptionalBlocks.IsolatedSelection R.π (nodeFinset R N) := by
  intro A hA v hv
  obtain ⟨W, hW, rfl⟩ := (mem_nodeFinset R N A).mp hA
  have hne : W ≠ v := fun h => hv (congrArg Subtype.val h).symm
  exact disjoint_of_not_adj R hne (hiso W hW v)

theorem exceptional_of_mem_nodeFinset (N : Finset R.Vertices) :
    ∀ C ∈ nodeFinset R N, IsExceptionalCurve R.π C := by
  intro C hC
  obtain ⟨W, _, rfl⟩ := (mem_nodeFinset R N C).mp hC
  exact W.property

theorem selfIntersection_of_mem_nodeFinset (N : Finset R.Vertices)
    (hw : ∀ W ∈ N, R.w W = 2) :
    ∀ C ∈ nodeFinset R N, C.selfIntersectionNumber R.hreg = -2 := by
  intro C hC
  obtain ⟨W, hW, rfl⟩ := (mem_nodeFinset R N C).mp hC
  have h2 := hw W hW
  rw [w_eq_neg_selfIntersection] at h2
  have : (W.val.selfIntersectionNumber R.hreg : ℚ) = -2 := by linarith
  exact_mod_cast this

/-- The contact of `P` with an isolated node disjoint from `P` vanishes. -/
theorem contact_eq_zero (P : R.S.PrimeCurve) (W : R.Vertices)
    (hPW : P.intersectionNumber (R.S.primeCurveCartier R.hreg W.val) = 0) :
    contact R P W = 0 := by
  simp only [contact, hPW, Int.cast_zero]

/-- **Theorem 5.1 in class form** (`thm:no-even-nodes`, via the union's
`isolated_even_selection_eq_empty`): in characteristic `p > 2`, no nonempty set of isolated
exceptional nodes has a sum divisible by two in `Pic S`. -/
theorem isolated_nodes_no_half_sum (p : ℕ) [CharP k p] (hp : 2 < p)
    (N : Finset R.Vertices) (hne : N.Nonempty)
    (hw : ∀ W ∈ N, R.w W = 2) (hiso : ∀ W ∈ N, ∀ y, ¬ R.graph.Adj W y) :
    ¬ ∃ m : Additive R.S.toScheme.Pic, (2 : ℤ) • m = ∑ W ∈ N, cls R W := by
  classical
  rintro ⟨m, hm⟩
  letI : IsSmooth R.S.structureMorphism :=
    MinimalResolutionQuadraticRegular.source_isSmooth R.π R.hmin
  have hclass : ∀ C : R.S.PrimeCurve,
      R.S.smoothWeilClassPicardEquiv (R.S.weilClassMap (Finsupp.single C 1)) = primeClass R C :=
    fun C => congrArg Additive.ofMul (R.S.smoothWeilClassPicardEquiv_single_toMul R.hreg C)
  have hempty := isolated_even_selection_eq_empty R.π R.hmin R.hDP R.hrank p hp (nodeFinset R N)
    (isolatedSelection_nodeFinset R N hiso) (exceptional_of_mem_nodeFinset R N)
    (selfIntersection_of_mem_nodeFinset R N hw) ⟨m, ?_⟩
  · exact Finset.nonempty_iff_ne_empty.mp
      (Finset.Nonempty.map (f := ⟨Subtype.val, Subtype.val_injective⟩) hne) hempty
  · show R.S.smoothWeilClassPicardEquiv (R.S.weilClassMap (R.S.selectedPrimeWeil (nodeFinset R N))) =
      (2 : ℕ) • m
    have hm' : (2 : ℤ) • m = ∑ W ∈ N, primeClass R W.val := hm
    rw [NormalProjectiveSurface.selectedPrimeWeil, map_sum, map_sum, nodeFinset, Finset.sum_map]
    simp only [hclass, Function.Embedding.coeFn_mk]
    rw [two_nsmul, ← two_zsmul, hm']

/-- **5.2(ii)**: the number of isolated exceptional nodes disjoint from `P` is at most the
exponent of two in the index `I = [Pic S : ⟨D, P⟩]`, in characteristic `p > 2`. The orthogonal
splitting `Γ = Γ₀ ⊕ ⊕ ℤ[W_i]` with `Γ₀ = ⟨P, D_j (j ∉ N)⟩` is exhibited explicitly. -/
theorem isolated_nodes_card_le_index (p : ℕ) [CharP k p] (hp : 2 < p)
    (P : R.S.PrimeCurve) (hPext : ¬ IsExceptionalCurve R.π P)
    (N : Finset R.Vertices)
    (hw : ∀ W ∈ N, R.w W = 2) (hiso : ∀ W ∈ N, ∀ y, ¬ R.graph.Adj W y)
    (hPN : ∀ W ∈ N, P.intersectionNumber (R.S.primeCurveCartier R.hreg W.val) = 0) :
    N.card ≤
      (R.S.exceptionalExteriorPicardSpan R.π R.hreg P).toAddSubgroup.index.factorization 2 := by
  classical
  letI : IsSmooth R.S.structureMorphism :=
    MinimalResolutionQuadraticRegular.source_isSmooth R.π R.hmin
  haveI : NeZero p := ⟨by omega⟩
  haveI : (R.S.exceptionalExteriorPicardSpan R.π R.hreg P).toAddSubgroup.FiniteIndex :=
    finiteIndex_exceptionalExteriorPicardSpan R p P hPext
  have hclass : ∀ C : R.S.PrimeCurve,
      R.S.smoothWeilClassPicardEquiv (R.S.weilClassMap (Finsupp.single C 1)) = primeClass R C :=
    fun C => congrArg Additive.ofMul (R.S.smoothWeilClassPicardEquiv_single_toMul R.hreg C)
  let Γ0 : Submodule ℤ (Additive R.S.toScheme.Pic) :=
    Submodule.span ℤ (insert (primeClass R P)
      (Set.range (fun j : {j : R.Vertices // j ∉ N} => cls R j.val)))
  rw [← card_nodeFinset R N]
  refine isolated_nodes_card_le_picard_index_of_kltDelPezzo R.π R.hmin R.hDP R.hrank p hp
    (nodeFinset R N) (isolatedSelection_nodeFinset R N hiso) (exceptional_of_mem_nodeFinset R N)
    (selfIntersection_of_mem_nodeFinset R N hw) _ Γ0 ?_ ?_
  · show R.S.exceptionalExteriorPicardSpan R.π R.hreg P = Γ0 ⊔ Submodule.span ℤ (Set.range
      (fun C : {C : R.S.PrimeCurve // C ∈ nodeFinset R N} =>
        R.S.smoothWeilClassPicardEquiv (R.S.weilClassMap (Finsupp.single C.val 1))))
    simp only [hclass]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x (rfl | ⟨i, rfl⟩)
      · exact Submodule.mem_sup_left (Submodule.subset_span (Set.mem_insert _ _))
      · by_cases hi : i ∈ N
        · exact Submodule.mem_sup_right (Submodule.subset_span
            ⟨⟨i.val, (mem_nodeFinset R N i.val).mpr ⟨i, hi, rfl⟩⟩, rfl⟩)
        · exact Submodule.mem_sup_left (Submodule.subset_span
            (Set.mem_insert_of_mem _ ⟨⟨i, hi⟩, rfl⟩))
    · apply sup_le
      · apply Submodule.span_le.mpr
        rintro x (rfl | ⟨j, rfl⟩)
        · exact Submodule.subset_span (Set.mem_insert _ _)
        · exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨j.val, rfl⟩)
      · apply Submodule.span_le.mpr
        rintro x ⟨C, rfl⟩
        obtain ⟨W, _, hWC⟩ := (mem_nodeFinset R N C.val).mp C.property
        refine Submodule.subset_span (Set.mem_insert_of_mem _ ⟨W, ?_⟩)
        show primeClass R W.val = primeClass R C.val
        rw [hWC]
  · show ∀ C : {C : R.S.PrimeCurve // C ∈ nodeFinset R N}, ∀ y ∈ Γ0,
      R.S.integralPicardIntersectionBilinForm R.hreg
        (R.S.smoothWeilClassPicardEquiv (R.S.weilClassMap (Finsupp.single C.val 1))) y = 0
    intro C y hy
    obtain ⟨W, hW, hWC⟩ := (mem_nodeFinset R N C.val).mp C.property
    rw [hclass, ← hWC]
    have hker : Γ0 ≤ LinearMap.ker
        (R.S.integralPicardIntersectionBilinForm R.hreg (primeClass R W.val)) := by
      apply Submodule.span_le.mpr
      rintro x (rfl | ⟨j, rfl⟩)
      · show R.S.integralPicardIntersectionBilinForm R.hreg (primeClass R W.val) (primeClass R P) = 0
        have h := pairing_cls_prime R P W
        rw [contact_eq_zero R P W (hPN W hW)] at h
        exact_mod_cast h
      · show R.S.integralPicardIntersectionBilinForm R.hreg (primeClass R W.val) (cls R j.val) = 0
        have hne : W ≠ j.val := fun h => j.property (h ▸ hW)
        have hne' : W.val ≠ j.val.val := fun h => hne (Subtype.ext h)
        rw [cls, pairing_primeClass]
        exact (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
          R.S R.hreg W.val j.val.val hne').mpr (disjoint_of_not_adj R hne (hiso W hW j.val))
    exact hker hy

/-- **Lemma 5.2 (`lem:picard-index`)**, bundled: for `I = [Pic S : ⟨D, P⟩]` and `g = pᵀA⁻¹p`,
(i) `I² = det A (g − 1)`; (ii) every finset of `t` isolated exceptional nodes disjoint from `P`
has `t ≤ v₂(I)`; (iii) `det A (g − 1)` is a positive integer square. -/
theorem fullPicardIndexObstruction [DecidableEq R.Vertices] (p : ℕ) [CharP k p] (hp : 2 < p)
    (P : R.S.PrimeCurve) (hP : IsMinusOneCurve R.hreg P) (hPext : ¬ IsExceptionalCurve R.π P) :
    (((R.S.exceptionalExteriorPicardSpan R.π R.hreg P).toAddSubgroup.index : ℕ) : ℚ) ^ 2 =
        R.A.det * (dotProduct (contact R P) (R.A⁻¹ *ᵥ contact R P) - 1) ∧
      (∀ N : Finset R.Vertices, (∀ W ∈ N, R.w W = 2) → (∀ W ∈ N, ∀ y, ¬ R.graph.Adj W y) →
        (∀ W ∈ N, P.intersectionNumber (R.S.primeCurveCartier R.hreg W.val) = 0) →
        N.card ≤
          (R.S.exceptionalExteriorPicardSpan R.π R.hreg P).toAddSubgroup.index.factorization 2) ∧
      ∃ I : ℕ, 0 < I ∧
        R.A.det * (dotProduct (contact R P) (R.A⁻¹ *ᵥ contact R P) - 1) = (I : ℚ) ^ 2 :=
  ⟨index_sq_eq_det_mul R p (by omega) P hP hPext,
    fun N hw hiso hPN => isolated_nodes_card_le_index R p hp P hPext N hw hiso hPN,
    det_mul_green_sub_one_is_square R p (by omega) P hP hPext⟩

end KltDP.Manuscript.S05

#print axioms KltDP.Manuscript.S05.exists_picard_lattice_data
#print axioms KltDP.Manuscript.S05.fullPicardIndexObstruction
#print axioms KltDP.Manuscript.S05.isolated_nodes_no_half_sum

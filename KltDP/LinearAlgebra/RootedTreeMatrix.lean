import KltDP.LinearAlgebra.ChainMatrix
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-!
# A weighted center with weight-two chain arms

The matrices here are actual stars of paths, with arbitrary finite arm lengths.
The center has weight `b`, each arm has diagonal weight two, and the center
meets the first vertex of each nonempty arm with entry minus one.

The scalar Schur complement, center inverse entry, and determinant are proved
from the certified chain matrices. Zero-length arms and an empty arm type are
allowed. No classification of rooted trees or geometric realization is claimed.
These formulas supply the star-of-paths calculations used in manuscript
`lem:rooted-trees` (planning task WP-R39).
-/

namespace KltDP.LinearAlgebra

open Matrix

variable {α 𝕜 : Type*} [Fintype α] [DecidableEq α] [Field 𝕜] [CharZero 𝕜]

/-- Coordinates of the disjoint chain arms. -/
abbrev ArmIndex (length : α → ℕ) := Σ a, Fin (length a)

/-- The disjoint union of the weight-two chain matrices. -/
def chainArms (length : α → ℕ) : Matrix (ArmIndex length) (ArmIndex length) 𝕜 :=
  Matrix.blockDiagonal' (fun a => weightTwoChain (length a))

/-- The corresponding explicit block Green matrix. -/
def chainArmsGreen (length : α → ℕ) : Matrix (ArmIndex length) (ArmIndex length) 𝕜 :=
  Matrix.blockDiagonal' (fun a => chainGreen (length a))

theorem chainArms_mul_green (length : α → ℕ) :
    chainArms (𝕜 := 𝕜) length * chainArmsGreen length = 1 := by
  rw [chainArms, chainArmsGreen, ← Matrix.blockDiagonal'_mul]
  simp only [weightTwoChain_mul_chainGreen]
  exact Matrix.blockDiagonal'_one

theorem chainArms_inverse (length : α → ℕ) :
    (chainArms (𝕜 := 𝕜) length)⁻¹ = chainArmsGreen length :=
  Matrix.inv_eq_right_inv (chainArms_mul_green length)

theorem isUnit_chainArms (length : α → ℕ) : IsUnit (chainArms (𝕜 := 𝕜) length) :=
  (Matrix.isUnit_iff_isUnit_det _).2
    (Matrix.isUnit_det_of_right_inverse (chainArms_mul_green length))

private def armFiberEquiv (length : α → ℕ) (a : α) :
    Fin (length a) ≃ {x : ArmIndex length // x.1 = a} where
  toFun i := ⟨⟨a, i⟩, rfl⟩
  invFun x := x.2 ▸ x.1.2
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨b, i⟩, h⟩
    cases h
    rfl

/-- The determinant is the product of the individual chain determinants. The
proof explicitly identifies each dependent block's subtype coordinates. -/
theorem det_chainArms (length : α → ℕ) :
    (chainArms (𝕜 := 𝕜) length).det = ∏ a, ((length a + 1 : ℕ) : 𝕜) := by
  classical
  letI : LinearOrder α := LinearOrder.lift' (Fintype.equivFin α)
    (Fintype.equivFin α).injective
  have htri := Matrix.blockTriangular_blockDiagonal'
    (fun a => weightTwoChain (𝕜 := 𝕜) (length a))
  change (Matrix.blockDiagonal' (fun a => weightTwoChain (𝕜 := 𝕜) (length a))).det = _
  rw [htri.det_fintype]
  apply Finset.prod_congr rfl
  intro a _
  let e := armFiberEquiv length a
  have hblock :
      ((chainArms (𝕜 := 𝕜) length).toSquareBlock Sigma.fst a).submatrix e e =
        weightTwoChain (length a) := by
    ext i j
    simp [e, armFiberEquiv, Matrix.toSquareBlock_def, Matrix.submatrix_apply,
      chainArms]
  calc
    _ = (((chainArms (𝕜 := 𝕜) length).toSquareBlock Sigma.fst a).submatrix e e).det :=
      (Matrix.det_submatrix_equiv_self e _).symm
    _ = (weightTwoChain (𝕜 := 𝕜) (length a)).det := by rw [hblock]
    _ = _ := det_weightTwoChain _

/-- Incidence of a spoke with the first vertex of each nonempty arm. -/
def armSpokes (length : α → ℕ) : ArmIndex length → 𝕜 :=
  fun x => if x.2.val = 0 then 1 else 0

omit [CharZero 𝕜] in
private theorem blockDiagonal_mulVec_at
    (length : α → ℕ) (B : ∀ a, Matrix (Fin (length a)) (Fin (length a)) 𝕜)
    (x : ArmIndex length → 𝕜) (a : α) (i : Fin (length a)) :
    (Matrix.blockDiagonal' B *ᵥ x) ⟨a, i⟩ =
      (B a *ᵥ (fun j => x ⟨a, j⟩)) i := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  rw [Fintype.sum_eq_single a]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro b hba
    apply Finset.sum_eq_zero
    intro j _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hba.symm, zero_mul]

private theorem chain_endpoint_charge (n : ℕ) :
    dotProduct (fun i : Fin n => if i.val = 0 then (1 : 𝕜) else 0)
      (chainGreen n *ᵥ (fun i => if i.val = 0 then 1 else 0)) =
        (n : 𝕜) / ((n + 1 : ℕ) : 𝕜) := by
  cases n with
  | zero => simp [dotProduct]
  | succ n =>
    have hvec : (fun i : Fin (n + 1) => if i.val = 0 then (1 : 𝕜) else 0) =
        Pi.single (0 : Fin (n + 1)) 1 := by
      ext i
      by_cases hi : i = 0
      · subst i
        simp only [Fin.val_zero, if_pos rfl, if_true, Pi.single_eq_same]
      · have hi' : i.val ≠ 0 := by
          intro h
          exact hi (Fin.ext h)
        rw [if_neg hi', Pi.single_eq_of_ne hi]
    rw [hvec, Matrix.mulVec_single_one, single_one_dotProduct]
    change chainGreen (n + 1) 0 0 = _
    rw [← weightTwoChain_inverse, weightTwoChain_inverse_first_diagonal]

/-- Sum of the endpoint contributions of the actual disjoint chain arms. -/
theorem armSpokes_inverse_charge (length : α → ℕ) :
    dotProduct (armSpokes (𝕜 := 𝕜) length)
      ((chainArms length)⁻¹ *ᵥ armSpokes length) =
        ∑ a, (length a : 𝕜) / ((length a + 1 : ℕ) : 𝕜) := by
  rw [chainArms_inverse]
  simp only [dotProduct, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  change (∑ i, armSpokes length ⟨a, i⟩ *
    (Matrix.blockDiagonal' (fun b => chainGreen (length b)) *ᵥ armSpokes length) ⟨a, i⟩) = _
  simp_rw [blockDiagonal_mulVec_at]
  exact chain_endpoint_charge (length a)

/-- The center weight after eliminating every chain arm. -/
def rootedStarSchur (length : α → ℕ) (b : 𝕜) : 𝕜 :=
  b - ∑ a, (length a : 𝕜) / ((length a + 1 : ℕ) : 𝕜)

/-- The actual star-of-paths matrix, with center coordinate `Sum.inl ()`. -/
def rootedStarMatrix (length : α → ℕ) (b : 𝕜) :
    Matrix (Unit ⊕ ArmIndex length) (Unit ⊕ ArmIndex length) 𝕜 :=
  Matrix.fromBlocks (fun (_ : Unit) (_ : Unit) => b)
    (Matrix.replicateRow Unit (-armSpokes length))
    (Matrix.replicateCol Unit (-armSpokes length)) (chainArms length)

/-- The scalar Schur complement is an equality of actual `Unit`-indexed
matrices. Its value includes zero-length arms as zero contributions. -/
theorem rootedStar_schur (length : α → ℕ) (b : 𝕜) :
    (fun (_ : Unit) (_ : Unit) => b) -
      Matrix.replicateRow Unit (-armSpokes length) * (chainArms length)⁻¹ *
        Matrix.replicateCol Unit (-armSpokes length) =
      (fun (_ : Unit) (_ : Unit) => rootedStarSchur length b) := by
  ext i j
  have hcontraction :
      ((Matrix.replicateRow Unit (-armSpokes (𝕜 := 𝕜) length) *
        (chainArms (𝕜 := 𝕜) length)⁻¹ *
        Matrix.replicateCol Unit (-armSpokes (𝕜 := 𝕜) length)) : Matrix Unit Unit 𝕜) i j =
      dotProduct (armSpokes (𝕜 := 𝕜) length)
        ((chainArms (𝕜 := 𝕜) length)⁻¹ *ᵥ armSpokes (𝕜 := 𝕜) length) := by
    rw [Matrix.mul_assoc]
    change dotProduct (-armSpokes length) ((chainArms length)⁻¹ *ᵥ (-armSpokes length)) = _
    rw [Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  change b - _ = _
  rw [hcontraction, armSpokes_inverse_charge]
  rfl

/-- Determinant of a weighted center with arbitrary finite chain arms. -/
theorem det_rootedStarMatrix (length : α → ℕ) (b : 𝕜) :
    (rootedStarMatrix length b).det =
      (∏ a, ((length a + 1 : ℕ) : 𝕜)) * rootedStarSchur length b := by
  letI : Invertible (chainArms (𝕜 := 𝕜) length) := (isUnit_chainArms length).invertible
  rw [rootedStarMatrix, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv,
    rootedStar_schur, Matrix.det_unique (n := Unit), det_chainArms]

/-- The whole rooted matrix is invertible precisely when its explicit scalar
Schur complement is nonzero. -/
theorem isUnit_rootedStarMatrix_iff (length : α → ℕ) (b : 𝕜) :
    IsUnit (rootedStarMatrix length b) ↔ rootedStarSchur length b ≠ 0 := by
  letI : Invertible (chainArms (𝕜 := 𝕜) length) := (isUnit_chainArms length).invertible
  rw [rootedStarMatrix, Matrix.isUnit_fromBlocks_iff_of_invertible₂₂,
    Matrix.invOf_eq_nonsing_inv, rootedStar_schur,
    Matrix.isUnit_iff_isUnit_det, Matrix.det_unique (n := Unit), isUnit_iff_ne_zero]

private def scalarUnitMatrix (s : 𝕜) : Matrix Unit Unit 𝕜 := fun _ _ => s

omit [CharZero 𝕜] in
private theorem scalarUnitMatrix_inverse {s : 𝕜} (hs : s ≠ 0) :
    (scalarUnitMatrix s)⁻¹ = scalarUnitMatrix s⁻¹ := by
  apply Matrix.inv_eq_right_inv
  ext i j
  simp [scalarUnitMatrix, Matrix.mul_apply, hs]

/-- The center inverse entry is the reciprocal of the explicit Schur scalar.
The nonvanishing hypothesis is necessary and is stated separately. -/
theorem rootedStarMatrix_inverse_center (length : α → ℕ) (b : 𝕜)
    (hs : rootedStarSchur length b ≠ 0) :
    (rootedStarMatrix length b)⁻¹ (Sum.inl ()) (Sum.inl ()) =
      (rootedStarSchur length b)⁻¹ := by
  letI : Invertible (chainArms (𝕜 := 𝕜) length) := (isUnit_chainArms length).invertible
  let S : Matrix Unit Unit 𝕜 := scalarUnitMatrix b -
    Matrix.replicateRow Unit (-armSpokes length) * ⅟ (chainArms length) *
      Matrix.replicateCol Unit (-armSpokes length)
  have hS : S = scalarUnitMatrix (rootedStarSchur length b) := by
    simpa only [S, scalarUnitMatrix, Matrix.invOf_eq_nonsing_inv] using rootedStar_schur length b
  have hSunit : IsUnit S := by
    rw [hS, Matrix.isUnit_iff_isUnit_det, Matrix.det_unique (n := Unit), isUnit_iff_ne_zero]
    exact hs
  letI : Invertible S := hSunit.invertible
  letI : Invertible (scalarUnitMatrix b -
      Matrix.replicateRow Unit (-armSpokes (𝕜 := 𝕜) length) *
        ⅟ (chainArms (𝕜 := 𝕜) length) *
        Matrix.replicateCol Unit (-armSpokes (𝕜 := 𝕜) length)) :=
    hSunit.invertible
  letI : Invertible (Matrix.fromBlocks (scalarUnitMatrix b)
      (Matrix.replicateRow Unit (-armSpokes (𝕜 := 𝕜) length))
      (Matrix.replicateCol Unit (-armSpokes (𝕜 := 𝕜) length))
      (chainArms (𝕜 := 𝕜) length)) := Matrix.fromBlocks₂₂Invertible _ _ _ _
  change (Matrix.fromBlocks (scalarUnitMatrix b)
    (Matrix.replicateRow Unit (-armSpokes (𝕜 := 𝕜) length))
    (Matrix.replicateCol Unit (-armSpokes (𝕜 := 𝕜) length))
    (chainArms (𝕜 := 𝕜) length))⁻¹ (Sum.inl ()) (Sum.inl ()) = _
  rw [← Matrix.invOf_eq_nonsing_inv, Matrix.invOf_fromBlocks₂₂_eq]
  change (⅟ S) () () = _
  rw [Matrix.invOf_eq_nonsing_inv, hS, scalarUnitMatrix_inverse hs]; rfl

/-- The center coefficient for a source of strength `t` supported at the root.
The canonical source in the manuscript is the specialization `t = b - 2`. -/
theorem rootedStarMatrix_source_center (length : α → ℕ) (b t : 𝕜)
    (hs : rootedStarSchur length b ≠ 0) :
    ((rootedStarMatrix length b)⁻¹ *ᵥ Pi.single (Sum.inl ()) t) (Sum.inl ()) =
      t / rootedStarSchur length b := by
  change dotProduct ((rootedStarMatrix length b)⁻¹ (Sum.inl ()))
    (Pi.single (Sum.inl ()) t) = _
  rw [dotProduct_single, rootedStarMatrix_inverse_center length b hs]
  ring

/-- Quadratic correction for a source supported at the root. With `t = b-2`
this is the canonical correction `(b-2)^2` times the root inverse entry. -/
theorem rootedStarMatrix_source_correction (length : α → ℕ) (b t : 𝕜)
    (hs : rootedStarSchur length b ≠ 0) :
    dotProduct (Pi.single (Sum.inl ()) t)
      ((rootedStarMatrix length b)⁻¹ *ᵥ Pi.single (Sum.inl ()) t) =
        t ^ 2 / rootedStarSchur length b := by
  rw [single_dotProduct, rootedStarMatrix_source_center length b t hs]
  ring

end KltDP.LinearAlgebra

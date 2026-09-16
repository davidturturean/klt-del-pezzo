import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Polynomial.AlgebraMap
import KltDP.Compatibility.ReesGrading

/-!
# The associated graded ring of an ideal, as a quotient of the Rees algebra

BRIEF37 task 1. For an ideal `I` of a commutative ring, this constructs

  `gr_I R := R[It] ⧸ I·R[It]`

as an honest commutative ring, together with the degree-`n` classes `ofPow` and the identification of
when such a class vanishes.

## Why a quotient of the Rees algebra, and not a direct sum

The textbook definition is `⊕ₙ Iⁿ ⧸ Iⁿ⁺¹` with the multiplication induced by `Iᵃ · Iᵇ ⊆ Iᵃ⁺ᵇ`.
Building that directly in Lean means supplying `DirectSum.GCommRing`, whose `GMonoid` fields are
heterogeneous equalities over `GradedMonoid.mk` — associativity and unitality as dependent `Sigma`
equalities. That is where this construction usually dies, and none of it is mathematical content.

The standard identity `R[It] ⧸ I·R[It] = ⊕ₙ Iⁿ/Iⁿ⁺¹` gives the same ring with **every ring axiom
free**, since a quotient of a commutative ring is a commutative ring. The graded pieces and the direct
sum then become a *theorem about* this ring rather than its definition. This is a deliberate
substitution for the shape the brief described, and it is recorded as such.

It is also cheap here specifically, because the accepted tree already carries the graded Rees algebra:
`KltDP.ReesGrading` supplies `single`, `component`, `SetLike.GradedOne`, `SetLike.GradedMul`,
`DirectSum.IsInternal` and a `GradedAlgebra` instance on Mathlib's `reesAlgebra I`. Nothing of that is
rebuilt.

## What the pinned Mathlib does and does not have

Re-checked at this pin, and one earlier claim of mine needs correcting:

* **The graded piece exists.** `Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow` (in the `PowQuot`
  section of `RingTheory/Ideal/Quotient/Operations.lean`) constructs
  `↥(Iⁿ) ⧸ (I • ⊤)` — which *is* `Iⁿ/Iⁿ⁺¹` — and identifies it with an ideal of `R ⧸ Iⁿ⁺¹`. Earlier
  notes in this lane said Mathlib "has `Ideal.Filtration` and no associated-graded construction". That
  is correct about the **ring** and wrong about the **pieces**.
* **Nothing above piece level exists.** The `PowQuot` section contains exactly two declarations, both
  equivalences of a single piece. There is no multiplication `gr_a × gr_b → gr_{a+b}`, no direct sum, no
  ring, and no associated graded ring anywhere in Mathlib at this pin (the sole textual match for
  "associated graded" is an unrelated homological bicomplex file). So everything above the piece is new.
* `Submodule.mem_smul_top_iff` is the bridge Mathlib itself uses for `x ∈ I • ⊤ ↔ (x : R) ∈ I • N`, and
  it is reused here rather than reproved.

## What is proved

* `shiftIdeal`, `AssociatedGraded`, and its `CommRing` instance.
* `coeffShift` and `shiftIdeal_le_coeffShift` — the degreewise bound: the degree-`m` coefficient of any
  element of `I·R[It]` lies in `Iᵐ⁺¹`. This is what makes leading forms nonzero.
* **`single_mem_shiftIdeal_iff`** — the sharp statement, both directions: a degree-`n` monomial lies in
  `I·R[It]` exactly when its coefficient lies in `Iⁿ⁺¹`.
* `ofPow`, **`ofPow_eq_zero_iff`**, and **`ofPow_mul`** — the degree-`n` class, its vanishing criterion,
  and multiplicativity `ofPow a r * ofPow b s = ofPow (a+b) (r*s)`.

## What is deliberately not built

The isomorphism `gr_n ≅ ↥(Iⁿ) ⧸ (I • ⊤)` with Mathlib's `PowQuot` piece, and the direct-sum
decomposition of `AssociatedGraded` into those pieces. Neither consumer needs them: additivity of the
order needs only the ring, the classes, and their multiplicativity. Per BRIEF37, `gr` of a regular local
ring being a polynomial ring is **not** attempted.
-/

noncomputable section

open Polynomial

universe u

namespace KltDP.RingTheory.AssociatedGradedRees

variable {R : Type u} [CommRing R] (I : Ideal R)

/-! ## The ring -/

/-- The ideal `I · R[It]` of the Rees algebra. -/
def shiftIdeal : Ideal (reesAlgebra I) := I.map (algebraMap R (reesAlgebra I))

/-- **The associated graded ring** `gr_I R = R[It] ⧸ I·R[It]`. -/
def AssociatedGraded : Type u := (reesAlgebra I) ⧸ shiftIdeal I

/-- The associated graded ring is a commutative ring, inherited from the quotient. -/
instance commRing : CommRing (AssociatedGraded I) := by
  delta AssociatedGraded; infer_instance

/-- The quotient map onto the associated graded ring. -/
def gradedMk : reesAlgebra I →+* AssociatedGraded I := Ideal.Quotient.mk (shiftIdeal I)

/-! ## The degreewise bound -/

/-- The Rees elements whose degree `m` coefficient lies in `I ^ (m + 1)`. This is an ideal of the Rees
algebra but **not** of `R[X]`: the argument needs the degree-`j` coefficient of the multiplier to lie in
`I ^ j`, which is exactly the defining property of `reesAlgebra`. -/
def coeffShift : Ideal (reesAlgebra I) where
  carrier := {f : reesAlgebra I | ∀ m, (f : R[X]).coeff m ∈ I ^ (m + 1)}
  zero_mem' := by
    intro m
    simp
  add_mem' := by
    intro a b ha hb m
    have hco : ((a + b : reesAlgebra I) : R[X]) = (a : R[X]) + (b : R[X]) := rfl
    rw [hco, coeff_add]
    exact Ideal.add_mem _ (ha m) (hb m)
  smul_mem' := by
    intro c f hf m
    have hco : ((c • f : reesAlgebra I) : R[X]) = (c : R[X]) * (f : R[X]) := rfl
    rw [hco, coeff_mul]
    refine Ideal.sum_mem _ ?_
    rintro ⟨j, k⟩ e
    have hjk : j + k = m := Finset.mem_antidiagonal.mp e
    have hprod := Ideal.mul_mem_mul (c.property j) (hf k)
    rw [← pow_add] at hprod
    have hexp : j + (k + 1) = m + 1 := by omega
    rwa [hexp] at hprod

/-- **The degreewise bound.** Every element of `I·R[It]` has its degree `m` coefficient in `I ^ (m+1)`. -/
theorem shiftIdeal_le_coeffShift : shiftIdeal I ≤ coeffShift I := by
  refine Ideal.map_le_iff_le_comap.mpr ?_
  intro a ha
  show ∀ m, ((algebraMap R (reesAlgebra I) a : reesAlgebra I) : R[X]).coeff m ∈ I ^ (m + 1)
  intro m
  have hco : ((algebraMap R (reesAlgebra I) a : reesAlgebra I) : R[X]) = C a := by
    rw [Subalgebra.coe_algebraMap]
    exact (Polynomial.C_eq_algebraMap a).symm
  rw [hco, coeff_C]
  split_ifs with h
  · subst h
    simpa using ha
  · exact Ideal.zero_mem _

/-! ## The vanishing criterion -/

/-- **The sharp criterion.** A degree-`n` monomial of the Rees algebra lies in `I·R[It]` exactly when its
coefficient lies in `I ^ (n+1)`. The forward direction is the degreewise bound; the reverse writes
`I ^ (n+1) = I * I ^ n` and pushes the scalar through the `R`-linear map `single`. -/
theorem single_mem_shiftIdeal_iff (n : ℕ) (r : ↥(I ^ n)) :
    KltDP.ReesGrading.single I n r ∈ shiftIdeal I ↔ (r : R) ∈ I ^ (n + 1) := by
  constructor
  · intro h
    have hb := shiftIdeal_le_coeffShift I h n
    rwa [KltDP.ReesGrading.single_val, coeff_monomial, if_pos rfl] at hb
  · intro h
    have hmul : I * I ^ n = I ^ (n + 1) := by rw [pow_succ, mul_comm]
    have hmem : r ∈ I • (⊤ : Submodule R ↥(I ^ n)) := by
      rw [Submodule.mem_smul_top_iff, Ideal.smul_eq_mul, hmul]
      exact h
    refine Submodule.smul_induction_on
      (p := fun z => KltDP.ReesGrading.single I n z ∈ shiftIdeal I) hmem ?_ ?_
    · intro a ha x _
      have hsm : KltDP.ReesGrading.single I n (a • x)
          = algebraMap R (reesAlgebra I) a * KltDP.ReesGrading.single I n x := by
        rw [map_smul, Algebra.smul_def]
      rw [hsm]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
    · intro x y hx hy
      rw [map_add]
      exact Ideal.add_mem _ hx hy

/-- **The converse inclusion.** A Rees element all of whose coefficients lie one power deeper is in
`I·R[It]`: expand it as the finite sum of its monomials and apply `single_mem_shiftIdeal_iff`. -/
theorem coeffShift_le_shiftIdeal : coeffShift I ≤ shiftIdeal I := by
  classical
  intro f hf
  have hmap := map_sum (Subalgebra.val (reesAlgebra I))
    (fun m => KltDP.ReesGrading.single I m ⟨(f : R[X]).coeff m, f.property m⟩)
    (f : R[X]).support
  simp only [Subalgebra.val_apply, KltDP.ReesGrading.single_val] at hmap
  have hpoly : (∑ m ∈ (f : R[X]).support, (Polynomial.monomial m ((f : R[X]).coeff m)))
      = (f : R[X]) := by
    have hsm := (f : R[X]).sum_monomial_eq
    rwa [Polynomial.sum_def] at hsm
  have hfeq : f = ∑ m ∈ (f : R[X]).support,
      KltDP.ReesGrading.single I m ⟨(f : R[X]).coeff m, f.property m⟩ := by
    apply Subtype.ext
    rw [hmap, hpoly]
  rw [hfeq]
  refine Ideal.sum_mem _ fun m _ => ?_
  exact (single_mem_shiftIdeal_iff I m _).mpr (hf m)

/-- **The two ideals coincide.** This is what makes the initial-form map injective on the quotient. -/
theorem shiftIdeal_eq_coeffShift : shiftIdeal I = coeffShift I :=
  le_antisymm (shiftIdeal_le_coeffShift I) (coeffShift_le_shiftIdeal I)

/-! ## Degree-`n` classes -/

/-- The class in `gr_I R` of an element of `I ^ n`, placed in degree `n`. -/
def ofPow (n : ℕ) (r : ↥(I ^ n)) : AssociatedGraded I :=
  gradedMk I (KltDP.ReesGrading.single I n r)

/-- **A degree-`n` class vanishes exactly when its representative lies one power deeper.** -/
theorem ofPow_eq_zero_iff (n : ℕ) (r : ↥(I ^ n)) :
    ofPow I n r = 0 ↔ (r : R) ∈ I ^ (n + 1) :=
  Ideal.Quotient.eq_zero_iff_mem.trans (single_mem_shiftIdeal_iff I n r)

/-- **Multiplicativity of the classes**: the product of the degree-`a` and degree-`b` classes is the
degree-`a+b` class of the product. This is the multiplication induced by `Iᵃ · Iᵇ ⊆ Iᵃ⁺ᵇ`. -/
theorem ofPow_mul (a b : ℕ) (r : ↥(I ^ a)) (s : ↥(I ^ b)) :
    ofPow I a r * ofPow I b s
      = ofPow I (a + b)
          ⟨(r : R) * (s : R), by rw [pow_add]; exact Ideal.mul_mem_mul r.property s.property⟩ := by
  show gradedMk I _ * gradedMk I _ = gradedMk I _
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subalgebra.coe_mul, KltDP.ReesGrading.single_val, KltDP.ReesGrading.single_val,
    KltDP.ReesGrading.single_val, monomial_mul_monomial]

/-- **Transport along an equality of degrees.** `ofPow` is indexed by the degree, so identifying two
degrees requires moving the representative across the corresponding subtype. -/
theorem ofPow_congr {m n : ℕ} (h : m = n) (r : ↥(I ^ m)) (s : ↥(I ^ n))
    (hrs : (r : R) = (s : R)) : ofPow I m r = ofPow I n s := by
  subst h
  congr 1
  exact Subtype.ext hrs

end KltDP.RingTheory.AssociatedGradedRees

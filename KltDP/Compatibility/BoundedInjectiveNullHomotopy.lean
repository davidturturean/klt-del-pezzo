/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import KltDP.Compatibility.HomComplexSingleCochain
import KltDP.Compatibility.InjectiveResolutionExtend

/-!
# Null homotopies into bounded-below complexes of injectives

The induction of cochains and the null-homotopy construction are ported from
Mathlib commit 79d0395a1825a6264ad5d269e35e60537518955e, from
`HomotopyCategory/HomComplexInduction` and `HomotopyCategory/KInjective`.
They use the original pinned cochains, differential, exactness and injectivity.
The final theorem applies this construction to the original extended injective
resolution. No localization or Ext comparison is assumed or asserted.
-/

universe v u

open CategoryTheory Limits Preadditive

namespace CochainComplex.HomComplex.Cochain

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K L : CochainComplex C ℤ}

/-- Two cochains agree through the given source degree. -/
def EqUpTo {n : ℤ} (α β : Cochain K L n) (p₀ : ℤ) : Prop :=
  ∀ (p q : ℤ) (hpq : p + n = q), p ≤ p₀ → α.v p q hpq = β.v p q hpq

namespace InductionUp

variable {d : ℤ} {X : ℕ → Set (Cochain K L d)}
  (φ : ∀ (n : ℕ), X n → X (n + 1))
  {p₀ : ℤ} (hφ : ∀ (n : ℕ) (x : X n), (φ n x).val.EqUpTo x.val (p₀ + n))
  (x₀ : X 0)

/-- The sequence obtained by iterating the actual cochain improvement maps. -/
def sequence : ∀ n, X n
  | 0 => x₀
  | n + 1 => φ n (sequence n)

include hφ in
lemma sequence_eqUpTo (n₁ n₂ : ℕ) (h : n₁ ≤ n₂) :
    (sequence φ x₀ n₁).val.EqUpTo (sequence φ x₀ n₂).val (p₀ + n₁) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k generalizing n₁ with
  | zero => intro _ _ _ _; simp
  | succ k hk =>
    intro p q hpq hp
    rw [hk n₁ p q hpq hp,
      ← hφ (n₁ + k) (sequence φ x₀ (n₁ + k)) p q hpq (by omega)]
    dsimp [sequence]

/-- The cochain obtained by taking the stabilized value in each source degree. -/
def limitSequence
    (_ : ∀ (n : ℕ) (x : X n), (φ n x).val.EqUpTo x.val (p₀ + n))
    (x₀ : X 0) : Cochain K L d :=
  Cochain.mk (fun p q hpq => (sequence φ x₀ (p - p₀).toNat).1.v p q hpq)

lemma limitSequence_eqUpTo (n : ℕ) :
    (limitSequence φ hφ x₀).EqUpTo (sequence φ x₀ n).1 (p₀ + n) := by
  intro p q hpq hp
  exact sequence_eqUpTo φ hφ _ _ _ (by omega) _ _ _ (by omega)

end InductionUp

end CochainComplex.HomComplex.Cochain

namespace CochainComplex

open HomComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Exactness in the source and injectivity in the target improve a partial
null homotopy by one degree, without changing its lower components. -/
lemma nullHomotopy_step {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (α : Cochain K L (-1)) (n m : ℤ) (hnm : n + 1 = m)
    (hK : K.ExactAt m) [Injective (L.X m)]
    (hα : (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) n) :
    ∃ (h : K.X (n + 2) ⟶ L.X (n + 1)),
      (δ (-1) 0 (α + Cochain.single h (-1))).EqUpTo (Cochain.ofHom f) m := by
  subst hnm
  let u := f.f (n + 1) - α.v (n + 1) n (by omega) ≫ L.d n (n + 1) -
    K.d (n + 1) (n + 2) ≫ α.v (n + 2) (n + 1) (by omega)
  have hu : K.d n (n + 1) ≫ u = 0 := by
    have eq := hα n n (add_zero n) (by rfl)
    simp only [δ_v (-1) 0 (neg_add_cancel 1) α n n (add_zero _) (n - 1) (n + 1)
      (by omega) (by omega), Int.negOnePow_zero, one_smul, Cochain.ofHom_v] at eq
    simp only [u, comp_sub, HomologicalComplex.d_comp_d_assoc, zero_comp,
      ← f.comm, ← eq, add_comp, Category.assoc, L.d_comp_d, comp_zero, zero_add, sub_self]
  rw [K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp; omega)] at hK
  obtain ⟨β, hβ⟩ : ∃ (β : K.X (n + 2) ⟶ L.X (n + 1)), K.d (n + 1) (n + 2) ≫ β = u :=
    ⟨hK.descToInjective _ hu, hK.comp_descToInjective _ _⟩
  refine ⟨β, ?_⟩
  intro p q hpq hp
  obtain rfl : p = q := by omega
  obtain hp | rfl := hp.lt_or_eq
  · rw [δ_add, Cochain.add_v, hα p p (by omega) (by omega), add_eq_left,
      δ_v (-1) 0 (neg_add_cancel 1) _ p p hpq (p - 1) (p + 1) rfl rfl,
      Cochain.single_v_eq_zero _ _ _ _ _ (by omega),
      Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
    simp
  · rw [δ_v (-1) 0 (neg_add_cancel 1) _ (n + 1) (n + 1) (by omega) n (n + 2)
      (by omega) (by omega), Cochain.add_v,
      Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
    simp [hβ, u]

open HomComplex.Cochain.InductionUp in
/-- Every morphism from an acyclic complex into a bounded-below complex of
injectives admits an actual null homotopy. -/
lemma nonempty_homotopy_zero_of_boundedBelow_injective
    (L : CochainComplex C ℤ) (d : ℤ)
    [L.IsStrictlyGE d] [∀ (n : ℤ), Injective (L.X n)]
    {K : CochainComplex C ℤ} (f : K ⟶ L) (hK : K.Acyclic) :
    Nonempty (Homotopy f 0) := by
  classical
  let X (n : ℕ) : Set (Cochain K L (-1)) :=
    setOf (fun α => (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) (n + d - 1))
  let x₀ : X 0 := ⟨0, fun p q hpq hp =>
    IsZero.eq_of_tgt (L.isZero_of_isStrictlyGE d _ (by omega)) _ _⟩
  let φ (n : ℕ) (α : X n) : X (n + 1) :=
    ⟨_, (nullHomotopy_step f α.1 (n + d - 1) ((n + 1 : ℕ) + d - 1)
      (by omega) (hK _) α.2).choose_spec⟩
  have hφ (k : ℕ) (x : X k) : (φ k x).1.EqUpTo x.1 (d + k) := fun p q hpq hp => by
    dsimp [φ]
    rw [add_eq_left, Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
  refine ⟨(Cochain.equivHomotopy f 0).symm ⟨limitSequence φ hφ x₀, ?_⟩⟩
  rw [Cochain.ofHom_zero, add_zero]
  apply Cochain.ext₀
  intro n
  let k₀ := (n - d + 1).toNat
  rw [← (sequence φ x₀ k₀).2 n n (add_zero n) (by omega),
    δ_v (-1) 0 (neg_add_cancel 1) _ n n (by omega) (n - 1) (n + 1) rfl (by omega),
    δ_v (-1) 0 (neg_add_cancel 1) _ n n (by omega) (n - 1) (n + 1) rfl (by omega),
    limitSequence_eqUpTo φ hφ x₀ k₀ n (n - 1) (by omega) (by omega),
    limitSequence_eqUpTo φ hφ x₀ k₀ (n + 1) n (by omega) (by omega)]

end CochainComplex

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] {X : C}

/-- The actual extension of the original injective resolution has the
null-homotopy property, by its proved component injectivity and lower bound. -/
lemma nonempty_homotopy_zero_to_cochainComplex (R : InjectiveResolution X)
    {K : CochainComplex C ℤ} (f : K ⟶ R.cochainComplex) (hK : K.Acyclic) :
    Nonempty (Homotopy f 0) :=
  CochainComplex.nonempty_homotopy_zero_of_boundedBelow_injective R.cochainComplex 0 f hK

end CategoryTheory.InjectiveResolution

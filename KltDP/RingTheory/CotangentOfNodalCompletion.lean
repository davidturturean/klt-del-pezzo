import KltDP.RingTheory.AdicCompletionKernelEval
import KltDP.RingTheory.OrdinaryDoublePointModelCotangent
import KltDP.Geometry.AdicCompletionAlgebraEquiv

/-!
# The cotangent space of a Noetherian local ring whose completion is the node model

BRIEF26, algebraic part on the ring. Let `O` be a Noetherian local `k`-algebra, `m` its maximal ideal,
`Ô = AdicCompletion m O` its completion, and `e : Ô ≃ₐ[k] k⟦x, y⟧ ⧸ (x y)` a `k`-algebra isomorphism
with the accepted ordinary double point model. Using the task-25 kernel lemma
(`ker (evalₐ m n) = m ^ n Ô`, so `m̂ = m Ô`, `m̂ ^ n ∩ O = m ^ n` and `O → Ô ⧸ m̂ ^ n` is onto) and
the model's cotangent structure (`OrdinaryDoublePointModelCotangent`):

* `algebraMap_mem_maximalIdeal_pow_iff`: `ι r ∈ m̂ ^ n ↔ r ∈ m ^ n`; `exists_sub_algebraMap_mem_pow`:
  every element of `Ô` is an element of `O` modulo `m̂ ^ n`; `mem_maximalIdeal_iff_map`, `mem_maximalIdeal_sq_iff_map`: `e`
  carries `m̂`, `m̂ ^ 2` to `m_M`, `m_M ^ 2`;
* `xBarLift e i ∈ m`: lifts of `x̄`, `ȳ` modulo `m̂ ^ 2`;
* **`linearIndependent_of_model`**: elements `w i ∈ m` whose completions are nonzero constant multiples
  of `x̄`, `ȳ` modulo `m̂ ^ 2` have linearly independent cotangent classes over the residue field of `O`
  (with `exists_const_of_mem_span` producing the constants from `e (ι w) ∈ (x̄ᵢ)`, `w ∉ m ^ 2`);
* **`finrank_cotangentSpace_eq_two`**: the cotangent space of `O` is two-dimensional (the classes of
  the lifts form a basis, `xBarLiftBasis`).

These are the ring-theoretic halves of the completed-stalk nodality interface; the scheme-level
statements are in `Geometry/TransverseBranchesOfCompletedStalk`.
-/

noncomputable section

open IsLocalRing

universe u

namespace KltDP.RingTheory.NodalCompletion

open KltDP.RingTheory.AdicCompletionKernelEval KltDP.RingTheory.OrdinaryDoublePointModel
  KltDP.Geometry.IntrinsicNodal

variable {k : Type u} [Field k] {O : Type u} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Algebra k O]

/-- The maximal-ideal completion of a local ring. -/
abbrev Compl (O : Type u) [CommRing O] [IsLocalRing O] : Type u :=
  AdicCompletion (maximalIdeal O) O

local instance compl_isLocalRing : IsLocalRing (Compl O) :=
  isLocalRing_adicCompletion (maximalIdeal O)

/-! ## Contraction and surjectivity modulo powers of the maximal ideal -/

omit [IsNoetherianRing O] in
theorem algebraMap_algebraMap (c : k) :
    algebraMap O (Compl O) (algebraMap k O c) = algebraMap k (Compl O) c :=
  AdicCompletion.ext fun _ => rfl

theorem algebraMap_mem_maximalIdeal_pow_iff (n : ℕ) (r : O) :
    algebraMap O (Compl O) r ∈ maximalIdeal (Compl O) ^ n ↔ r ∈ maximalIdeal O ^ n := by
  rw [maximalIdeal_adicCompletion, ← Ideal.map_pow, mem_map_pow_iff, ← evalₐ_eq_zero_iff,
    evalₐ_algebraMap, Ideal.Quotient.eq_zero_iff_mem]

theorem algebraMap_mem_maximalIdeal_iff (r : O) :
    algebraMap O (Compl O) r ∈ maximalIdeal (Compl O) ↔ r ∈ maximalIdeal O := by
  have h := algebraMap_mem_maximalIdeal_pow_iff (O := O) 1 r
  rwa [pow_one, pow_one] at h

theorem exists_sub_algebraMap_mem_pow (n : ℕ) (z : Compl O) :
    ∃ r : O, z - algebraMap O (Compl O) r ∈ maximalIdeal (Compl O) ^ n := by
  obtain ⟨f, rfl⟩ := AdicCompletion.mk_surjective (maximalIdeal O) O z
  refine ⟨f.val n, ?_⟩
  rw [maximalIdeal_adicCompletion, ← Ideal.map_pow, mem_map_pow_iff, ← evalₐ_eq_zero_iff, map_sub,
    AdicCompletion.evalₐ_mk, evalₐ_algebraMap, sub_self]

/-! ## Transport along the isomorphism with the model -/

variable (e : Compl O ≃ₐ[k] ordinaryDoublePointModel k)

omit [IsNoetherianRing O] in
/-- Membership in an ideal of the completion is checked after transport along `e`. -/
theorem mem_iff_map (I : Ideal (Compl O)) (z : Compl O) :
    z ∈ I ↔ e z ∈ Ideal.map e.toRingHom I := by
  constructor
  · intro h
    exact Ideal.mem_map_of_mem _ h
  · intro h
    obtain ⟨y, hy, hyz⟩ := (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp h
    have hyz' : e y = e z := hyz
    rw [← e.injective hyz']
    exact hy

theorem mem_maximalIdeal_iff_map (z : Compl O) :
    z ∈ maximalIdeal (Compl O) ↔ e z ∈ maximalIdeal (ordinaryDoublePointModel k) := by
  rw [mem_iff_map e, ← KltDP.Geometry.maximalIdeal_eq_map_algEquiv e]

theorem mem_maximalIdeal_sq_iff_map (z : Compl O) :
    z ∈ maximalIdeal (Compl O) ^ 2 ↔
      e z ∈ maximalIdeal (ordinaryDoublePointModel k) ^ 2 := by
  rw [mem_iff_map e, Ideal.map_pow, ← KltDP.Geometry.maximalIdeal_eq_map_algEquiv e]

/-- Lifts of `x̄`, `ȳ` to the maximal ideal of `O`, modulo `m̂ ^ 2`. -/
theorem exists_lift (i : Fin 2) : ∃ w : O, w ∈ maximalIdeal O ∧
    e (algebraMap O (Compl O) w) - (xBar k i : ordinaryDoublePointModel k) ∈
      maximalIdeal (ordinaryDoublePointModel k) ^ 2 := by
  obtain ⟨w, hw⟩ := exists_sub_algebraMap_mem_pow (O := O) 2 (e.symm (xBar k i))
  refine ⟨w, ?_, ?_⟩
  · have h1 : e.symm (xBar k i) ∈ maximalIdeal (Compl O) := by
      rw [mem_maximalIdeal_iff_map e, AlgEquiv.apply_symm_apply]
      exact (xBar k i).2
    have h2 : e.symm (xBar k i) - algebraMap O (Compl O) w ∈ maximalIdeal (Compl O) :=
      Ideal.pow_le_self two_ne_zero hw
    rw [← algebraMap_mem_maximalIdeal_iff]
    have h3 := Ideal.sub_mem _ h1 h2
    rwa [sub_sub_cancel] at h3
  · have h3 : algebraMap O (Compl O) w - e.symm (xBar k i) ∈ maximalIdeal (Compl O) ^ 2 := by
      rw [← neg_sub]
      exact (Ideal.neg_mem_iff _).mpr hw
    have h4 := (mem_maximalIdeal_sq_iff_map e _).mp h3
    rwa [map_sub, AlgEquiv.apply_symm_apply] at h4

/-- Lifts of `x̄`, `ȳ` to the maximal ideal of `O`. -/
def xBarLift (i : Fin 2) : maximalIdeal O :=
  ⟨(exists_lift e i).choose, (exists_lift e i).choose_spec.1⟩

theorem xBarLift_spec (i : Fin 2) :
    e (algebraMap O (Compl O) (xBarLift e i : O)) - (xBar k i : ordinaryDoublePointModel k) ∈
      maximalIdeal (ordinaryDoublePointModel k) ^ 2 :=
  (exists_lift e i).choose_spec.2

/-! ## The cotangent classes -/

theorem mul_sub_mul_mem_sq {R : Type u} [CommRing R] (I : Ideal R) {a a' b b' : R}
    (ha : a - a' ∈ I) (hb : b ∈ I) (hb' : b - b' ∈ I ^ 2) : a * b - a' * b' ∈ I ^ 2 := by
  have h : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  rw [h]
  refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ hb')
  rw [pow_two]
  exact Ideal.mul_mem_mul ha hb

/-- **Independence of branch germs.** Elements `w 0`, `w 1` of `m` whose completions are nonzero
constant multiples of `x̄`, `ȳ` modulo `m̂ ^ 2` have linearly independent cotangent classes. -/
theorem linearIndependent_of_model (w : Fin 2 → maximalIdeal O) (c : Fin 2 → k)
    (hc : ∀ i, c i ≠ 0)
    (hw : ∀ i, e (algebraMap O (Compl O) (w i : O)) -
      algebraMap k (ordinaryDoublePointModel k) (c i) * (xBar k i : ordinaryDoublePointModel k) ∈
        maximalIdeal (ordinaryDoublePointModel k) ^ 2) :
    LinearIndependent (ResidueField O) (fun i => (maximalIdeal O).toCotangent (w i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  choose a ha using fun j => residue_surjective (R := O) (g j)
  have hsum : (∑ j, g j • (maximalIdeal O).toCotangent (w j)) =
      (maximalIdeal O).toCotangent (∑ j, a j • w j) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← ha j, residue_smul_toCotangent]
  rw [hsum, Ideal.toCotangent_eq_zero] at hg
  have hval : ((∑ j, a j • w j : maximalIdeal O) : O) = a 0 * w 0 + a 1 * w 1 := by
    simp only [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul, smul_eq_mul]
  rw [hval] at hg
  have h1 := (mem_maximalIdeal_sq_iff_map e _).mp
    ((algebraMap_mem_maximalIdeal_pow_iff 2 _).mpr hg)
  simp only [map_add, map_mul] at h1
  choose d hd using fun j =>
    exists_sub_algebraMap_mem_maximalIdeal k (e (algebraMap O (Compl O) (a j)))
  have hwm : ∀ j, e (algebraMap O (Compl O) (w j : O)) ∈
      maximalIdeal (ordinaryDoublePointModel k) := fun j =>
    (mem_maximalIdeal_iff_map e _).mp ((algebraMap_mem_maximalIdeal_iff _).mpr (w j).2)
  have h3 : ∀ j, e (algebraMap O (Compl O) (a j)) * e (algebraMap O (Compl O) (w j : O)) -
      algebraMap k (ordinaryDoublePointModel k) (d j * c j) * (xBar k j : ordinaryDoublePointModel k) ∈
        maximalIdeal (ordinaryDoublePointModel k) ^ 2 := fun j => by
    rw [map_mul, mul_assoc]
    exact mul_sub_mul_mem_sq _ (hd j) (hwm j) (hw j)
  have h2 : algebraMap k (ordinaryDoublePointModel k) (d 0 * c 0) *
        (xBar k 0 : ordinaryDoublePointModel k) +
      algebraMap k (ordinaryDoublePointModel k) (d 1 * c 1) *
        (xBar k 1 : ordinaryDoublePointModel k) ∈
      maximalIdeal (ordinaryDoublePointModel k) ^ 2 := by
    have h4 := Ideal.sub_mem _ h1 (Ideal.add_mem _ (h3 0) (h3 1))
    have h5 : ∀ A₀ A₁ B₀ B₁ : ordinaryDoublePointModel k,
        A₀ + A₁ - (A₀ - B₀ + (A₁ - B₁)) = B₀ + B₁ := fun _ _ _ _ => by ring
    rwa [h5] at h4
  have h6 : residue (ordinaryDoublePointModel k)
      (algebraMap k (ordinaryDoublePointModel k) (d i * c i)) = 0 := by
    refine (Fintype.linearIndependent_iff.mp (linearIndependent_xBar k))
      (fun j => residue (ordinaryDoublePointModel k)
        (algebraMap k (ordinaryDoublePointModel k) (d j * c j))) ?_ i
    rw [Fin.sum_univ_two, residue_smul_toCotangent, residue_smul_toCotangent, ← map_add,
      Ideal.toCotangent_eq_zero]
    simpa only [Submodule.coe_add, Submodule.coe_smul, smul_eq_mul] using h2
  rw [residue_eq_zero_iff, OrdinaryDoublePointModel.algebraMap_mem_maximalIdeal_iff] at h6
  have hdi : d i = 0 := (mul_eq_zero.mp h6).resolve_right (hc i)
  have h7 : e (algebraMap O (Compl O) (a i)) ∈ maximalIdeal (ordinaryDoublePointModel k) := by
    have h8 := hd i
    rwa [hdi, map_zero, sub_zero] at h8
  rw [← ha i, residue_eq_zero_iff, ← algebraMap_mem_maximalIdeal_iff, mem_maximalIdeal_iff_map e]
  exact h7

/-- A germ of `m` whose completion is a multiple of `x̄ᵢ` and which is not in `m ^ 2` is a nonzero
constant multiple of `x̄ᵢ` modulo `m̂ ^ 2`. -/
theorem exists_const_of_mem_span (w : maximalIdeal O) (i : Fin 2) (u : ordinaryDoublePointModel k)
    (hu : e (algebraMap O (Compl O) (w : O)) = u * xBar k i)
    (hw : (w : O) ∉ maximalIdeal O ^ 2) :
    ∃ c : k, c ≠ 0 ∧ e (algebraMap O (Compl O) (w : O)) -
      algebraMap k (ordinaryDoublePointModel k) c * (xBar k i : ordinaryDoublePointModel k) ∈
        maximalIdeal (ordinaryDoublePointModel k) ^ 2 := by
  obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_maximalIdeal k u
  refine ⟨c, ?_, ?_⟩
  · rintro rfl
    apply hw
    rw [← algebraMap_mem_maximalIdeal_pow_iff, mem_maximalIdeal_sq_iff_map e, hu, pow_two]
    rw [map_zero, sub_zero] at hc
    exact Ideal.mul_mem_mul hc (xBar k i).2
  · rw [hu, ← sub_mul, pow_two]
    exact Ideal.mul_mem_mul hc (xBar k i).2

theorem linearIndependent_xBarLift :
    LinearIndependent (ResidueField O) (fun i => (maximalIdeal O).toCotangent (xBarLift e i)) :=
  linearIndependent_of_model e (xBarLift e) (fun _ => 1) (fun _ => one_ne_zero) fun i => by
    rw [map_one, one_mul]
    exact xBarLift_spec e i

theorem top_le_span_xBarLift :
    ⊤ ≤ Submodule.span (ResidueField O)
      (Set.range (fun i => (maximalIdeal O).toCotangent (xBarLift e i))) := by
  rintro z -
  obtain ⟨⟨r, hr⟩, rfl⟩ := (maximalIdeal O).toCotangent_surjective z
  have hr' : e (algebraMap O (Compl O) r) ∈ maximalIdeal (ordinaryDoublePointModel k) :=
    (mem_maximalIdeal_iff_map e _).mp ((algebraMap_mem_maximalIdeal_iff r).mpr hr)
  obtain ⟨a, b, hab⟩ := exists_eq_mul_xBar_add k hr'
  obtain ⟨ca, hca⟩ := exists_sub_algebraMap_mem_maximalIdeal k a
  obtain ⟨cb, hcb⟩ := exists_sub_algebraMap_mem_maximalIdeal k b
  have hs0 : (xBar k 0 : ordinaryDoublePointModel k) - e (algebraMap O (Compl O) (xBarLift e 0 : O)) ∈
      maximalIdeal (ordinaryDoublePointModel k) ^ 2 := by
    rw [← neg_sub]
    exact (Ideal.neg_mem_iff _).mpr (xBarLift_spec e 0)
  have hs1 : (xBar k 1 : ordinaryDoublePointModel k) - e (algebraMap O (Compl O) (xBarLift e 1 : O)) ∈
      maximalIdeal (ordinaryDoublePointModel k) ^ 2 := by
    rw [← neg_sub]
    exact (Ideal.neg_mem_iff _).mpr (xBarLift_spec e 1)
  have hmem : r - (algebraMap k O ca * xBarLift e 0 + algebraMap k O cb * xBarLift e 1) ∈
      maximalIdeal O ^ 2 := by
    rw [← algebraMap_mem_maximalIdeal_pow_iff, mem_maximalIdeal_sq_iff_map e]
    simp only [map_sub, map_add, map_mul, algebraMap_algebraMap, AlgEquiv.commutes]
    rw [hab, add_sub_add_comm]
    exact Ideal.add_mem _ (mul_sub_mul_mem_sq _ hca (xBar k 0).2 hs0)
      (mul_sub_mul_mem_sq _ hcb (xBar k 1).2 hs1)
  have hclass : (maximalIdeal O).toCotangent ⟨r, hr⟩ =
      residue O (algebraMap k O ca) • (maximalIdeal O).toCotangent (xBarLift e 0) +
        residue O (algebraMap k O cb) • (maximalIdeal O).toCotangent (xBarLift e 1) := by
    rw [residue_smul_toCotangent, residue_smul_toCotangent, ← map_add, ← sub_eq_zero, ← map_sub,
      Ideal.toCotangent_eq_zero]
    simpa only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, smul_eq_mul] using hmem
  rw [hclass]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

/-- The classes of the lifts of `x̄`, `ȳ` form a basis of the cotangent space of `O`. -/
def xBarLiftBasis : Basis (Fin 2) (ResidueField O) (CotangentSpace O) :=
  Basis.mk (linearIndependent_xBarLift e) (top_le_span_xBarLift e)

include e in
/-- **The cotangent space of a Noetherian local `k`-algebra whose completion is the node model is
two-dimensional.** -/
theorem finrank_cotangentSpace_eq_two :
    Module.finrank (ResidueField O) (CotangentSpace O) = 2 := by
  rw [Module.finrank_eq_card_basis (xBarLiftBasis e), Fintype.card_fin]

end KltDP.RingTheory.NodalCompletion

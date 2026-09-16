import KltDP.RingTheory.OrdinaryDoublePointModelIdeals
import KltDP.RingTheory.CompletionFlatNonzeroDivisor
import KltDP.RingTheory.CotangentOfNodalCompletion
import KltDP.Geometry.ComponentStalkIdealsProduct
import KltDP.Geometry.TransverseBranchesOfCompletedStalk
import Mathlib.RingTheory.AdicCompletion.Noetherian

/-!
# Transverse component branches from the completed-stalk node model, unconditionally

BRIEF27, item (G4): the assembly of the fibre-product ideal theory of `k⟦x, y⟧ ⧸ (x y)` (G1), the stalk
ideals of the components (G2) and the flatness of the completion (G3).

**Ring-theoretic part** (`O` a Noetherian reduced local `k`-algebra with `e : Ô ≃ₐ[k] model`):
* `algebraMap_compl_injective`: `O → Ô` is injective (Krull intersection, Mathlib's `IsHausdorff`);
* **`exists_mem_not_mem_sq`**: for a prime `P` and an ideal `Q ≠ 0` with `P · Q = 0` and
  `e (Q Ô) ⊆ (x̄ⱼ)` (`j ≠ i`), `P` is not contained in `m ^ 2` — otherwise `x̂ᵢ := e⁻¹ x̄ᵢ` would lie in
  `P Ô ⊆ m̂ ^ 2` (a nonzero `t ∈ Q` has `t x̂ᵢ = 0 ∈ P Ô`, `t ∉ P` by reducedness, and `t` is a
  nonzerodivisor modulo `P Ô` by flatness), contradicting `x̄ᵢ ∉ m_M ^ 2`;
* **`exists_branch_germs`**: hence branch germs `w 0 ∈ P`, `w 1 ∈ Q` with independent cotangent classes
  (`linearIndependent_of_model'`, the permuted form of BRIEF26's independence lemma).

**Scheme-theoretic part**: **`hasTransverseComponentBranches_of_completedStalk`** — for a reduced
Noetherian, locally Noetherian scheme `X` over `k` with no point on three components and with
completed stalk `Ô_{X, q} ≃ₐ[k] k⟦x, y⟧ ⧸ (x y)` at every point where two components meet, `X` has
transverse component branches (the nodality hypothesis of `lem:tree-picard`). The two stalk ideals are
nonzero primes with zero product (G2), their images in the model lie on the two different branches (G1),
and the branch germs are provided by the ring-theoretic part. The no-triple-point hypothesis identifies
the stalk ideal of the complementary union `Z_{Cᶜ}` with that of the other component `D` through `q`
(the accepted `chartIdeal_compl_map_germ_eq`).
-/

noncomputable section

open IsLocalRing

universe u

namespace KltDP.RingTheory.NodalCompletion

open KltDP.RingTheory.AdicCompletionKernelEval KltDP.RingTheory.OrdinaryDoublePointModel
  KltDP.Geometry.IntrinsicNodal

variable {k : Type u} [Field k] {O : Type u} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Algebra k O]

local instance compl_isLocalRing' : IsLocalRing (Compl O) :=
  isLocalRing_adicCompletion (maximalIdeal O)

/-- The canonical map to the completion is injective (Krull's intersection theorem). -/
theorem algebraMap_compl_injective : Function.Injective (algebraMap O (Compl O)) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  have h : ∀ n, r ∈ maximalIdeal O ^ n := fun n =>
    (algebraMap_mem_maximalIdeal_pow_iff n r).mp (by rw [hr]; exact Ideal.zero_mem _)
  have h2 : r ∈ ⨅ n : ℕ, (maximalIdeal O ^ n • ⊤ : Submodule O O) := by
    rw [Submodule.mem_iInf]
    intro n
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact h n
  rw [IsHausdorff.iInf_pow_smul (inferInstance : IsHausdorff (maximalIdeal O) O)] at h2
  exact (Submodule.mem_bot O).mp h2

variable (e : Compl O ≃ₐ[k] ordinaryDoublePointModel k)

/-- Independence of branch germs, with the branches permuted by `σ`. -/
theorem linearIndependent_of_model' (σ : Fin 2 ≃ Fin 2) (w : Fin 2 → maximalIdeal O)
    (c : Fin 2 → k) (hc : ∀ i, c i ≠ 0)
    (hw : ∀ i, e (algebraMap O (Compl O) (w i : O)) -
      algebraMap k (ordinaryDoublePointModel k) (c i) * (xBar k (σ i) : ordinaryDoublePointModel k) ∈
        maximalIdeal (ordinaryDoublePointModel k) ^ 2) :
    LinearIndependent (ResidueField O) (fun i => (maximalIdeal O).toCotangent (w i)) := by
  have h := linearIndependent_of_model e (w ∘ σ.symm) (c ∘ σ.symm) (fun i => hc _) fun i => by
    have h1 := hw (σ.symm i)
    rwa [Equiv.apply_symm_apply] at h1
  have h2 := h.comp σ σ.injective
  convert h2 using 1
  funext i
  simp only [Function.comp_apply, Equiv.symm_apply_apply]

/-- An element of the branch `(x̄ⱼ)` kills `x̄ᵢ` for `i ≠ j`. -/
theorem _root_.KltDP.RingTheory.OrdinaryDoublePointModel.mul_xBar_eq_zero_of_mem_span (k : Type u)
    [Field k] (i j : Fin 2) (hij : i ≠ j) (z : ordinaryDoublePointModel k)
    (hz : z ∈ Ideal.span {(xBar k j : ordinaryDoublePointModel k)}) :
    z * (xBar k i : ordinaryDoublePointModel k) = 0 := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · rw [mul_comm z]
    exact mul_eq_zero_of_mem_span_xBar k (Ideal.mem_span_singleton_self _) hz
  · exact mul_eq_zero_of_mem_span_xBar k hz (Ideal.mem_span_singleton_self _)
  · exact absurd rfl hij

/-- **A branch ideal is not contained in `m ^ 2`.** -/
theorem exists_mem_not_mem_sq [IsReduced O] (P Q : Ideal O) [P.IsPrime] (hQ : Q ≠ ⊥)
    (hPQ : P * Q = ⊥) (i j : Fin 2) (hij : i ≠ j)
    (hQ' : Ideal.map e.toRingHom (Ideal.map (algebraMap O (Compl O)) Q) ≤
      Ideal.span {(xBar k j : ordinaryDoublePointModel k)}) :
    ∃ w ∈ P, w ∉ maximalIdeal O ^ 2 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨t, htQ, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ
  have htP : t ∉ P := fun htP => by
    apply ht0
    have h : t * t ∈ P * Q := Ideal.mul_mem_mul htP htQ
    rw [hPQ, Ideal.mem_bot] at h
    exact IsNilpotent.eq_zero ⟨2, by rw [pow_two]; exact h⟩
  have hxy : e (algebraMap O (Compl O) t) * (xBar k i : ordinaryDoublePointModel k) = 0 :=
    mul_xBar_eq_zero_of_mem_span k i j hij _
      (hQ' (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ htQ)))
  have h1 : algebraMap O (Compl O) t * e.symm (xBar k i) ∈ Ideal.map (algebraMap O (Compl O)) P := by
    rw [mem_iff_map e, map_mul, AlgEquiv.apply_symm_apply, hxy]
    exact Ideal.zero_mem _
  have h4 := KltDP.RingTheory.AdicCompletion.mem_map_of_smul_mem_map (maximalIdeal O) P htP h1
  have h5 : e.symm (xBar k i) ∈ maximalIdeal (Compl O) ^ 2 := by
    have h6 := Ideal.map_mono (f := algebraMap O (Compl O))
      (show P ≤ maximalIdeal O ^ 2 from fun w hw => hcon w hw) h4
    rwa [Ideal.map_pow, ← maximalIdeal_adicCompletion] at h6
  have h7 := (mem_maximalIdeal_sq_iff_map e _).mp h5
  rw [AlgEquiv.apply_symm_apply] at h7
  exact xBar_not_mem_sq k i h7

/-- **Branch germs**: for primes `P`, `Q` of `O` with zero product whose completions lie on the two
different branches (`σ 0`, `σ 1`) of the model, there are germs `w 0 ∈ P`, `w 1 ∈ Q` with independent
cotangent classes. -/
theorem exists_branch_germs [IsReduced O] (P Q : Ideal O) [P.IsPrime] [Q.IsPrime] (hP0 : P ≠ ⊥)
    (hQ0 : Q ≠ ⊥) (hPQ : P * Q = ⊥) (σ : Fin 2 ≃ Fin 2)
    (hP : Ideal.map e.toRingHom (Ideal.map (algebraMap O (Compl O)) P) ≤
      Ideal.span {(xBar k (σ 0) : ordinaryDoublePointModel k)})
    (hQ : Ideal.map e.toRingHom (Ideal.map (algebraMap O (Compl O)) Q) ≤
      Ideal.span {(xBar k (σ 1) : ordinaryDoublePointModel k)}) :
    ∃ w : Fin 2 → maximalIdeal O, (w 0 : O) ∈ P ∧ (w 1 : O) ∈ Q ∧
      LinearIndependent (ResidueField O) (fun l => (maximalIdeal O).toCotangent (w l)) := by
  have hσ : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  obtain ⟨w₀, hw₀, hw₀'⟩ := exists_mem_not_mem_sq e P Q hQ0 hPQ (σ 0) (σ 1) hσ hQ
  obtain ⟨w₁, hw₁, hw₁'⟩ := exists_mem_not_mem_sq e Q P hP0 (by rw [mul_comm]; exact hPQ) (σ 1) (σ 0)
    hσ.symm hP
  let w : Fin 2 → maximalIdeal O :=
    ![⟨w₀, le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance) hw₀⟩,
      ⟨w₁, le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance) hw₁⟩]
  refine ⟨w, hw₀, hw₁, ?_⟩
  have hc : ∀ l, ∃ c : k, c ≠ 0 ∧ e (algebraMap O (Compl O) (w l : O)) -
      algebraMap k (ordinaryDoublePointModel k) c * (xBar k (σ l) : ordinaryDoublePointModel k) ∈
        maximalIdeal (ordinaryDoublePointModel k) ^ 2 := by
    intro l
    fin_cases l
    · obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp
        (hP (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hw₀)))
      exact exists_const_of_mem_span e (w 0) (σ 0) u hu.symm hw₀'
    · obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp
        (hQ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hw₁)))
      exact exists_const_of_mem_span e (w 1) (σ 1) u hu.symm hw₁'
  choose c hc0 hcw using hc
  exact linearIndependent_of_model' e σ w c hc0 hcw

end KltDP.RingTheory.NodalCompletion

namespace KltDP.Geometry.RationalTreePicard

open AlgebraicGeometry CategoryTheory TopologicalSpace
open KltDP.Geometry.IntrinsicNodal KltDP.RingTheory.OrdinaryDoublePointModel

variable {k : Type u} [Field k] (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X]
  [AlgebraicGeometry.IsReduced X] (f : X ⟶ Spec (CommRingCat.of k))

/-- **Transverse component branches from the completed-stalk node model** (unconditional form). -/
theorem hasTransverseComponentBranches_of_completedStalk
    (hno : ∀ (C D E : ↥(irreducibleComponents X)) (q : X),
      q ∈ C.1 → q ∈ D.1 → q ∈ E.1 → C = D ∨ C = E ∨ D = E)
    (e : ∀ (C : ↥(irreducibleComponents X)) (q : X), q ∈ C.1 →
      q ∈ (componentClosedUnion X ({C}ᶜ) : Set X) →
      (letI := stalkAlgebra f q; completedStalk X q ≃ₐ[k] ordinaryDoublePointModel k)) :
    HasTransverseComponentBranches X := by
  intro C q hqC hqCc U hq
  obtain ⟨D, hD, hqD⟩ := (mem_componentClosedUnion X _ q).mp hqCc
  have hCD : C ≠ D := fun hCD => hD (Set.mem_singleton_iff.mpr hCD.symm)
  have hno' : ∀ E : ↥(irreducibleComponents X), q ∈ E.1 → E = C ∨ E = D := by
    intro E hqE
    rcases hno C D E q hqC hqD hqE with hCD' | hCE | hDE
    · exact absurd hCD' hCD
    · exact Or.inl hCE.symm
    · exact Or.inr hDE.symm
  letI := stalkAlgebra f q
  haveI : IsNoetherianRing (X.presheaf.stalk q) :=
    KltDP.Geometry.isNoetherianRing_stalk_of_isLocallyNoetherian X q
  have hpD : stalkIdeal ({C}ᶜ) U hq = stalkIdeal {D} U hq :=
    chartIdeal_compl_map_germ_eq C D hCD q hno' U hq
  haveI hPC : (stalkIdeal {C} U hq).IsPrime := stalkIdeal_singleton_isPrime C U hq hqC
  haveI hPD : (stalkIdeal {D} U hq).IsPrime := stalkIdeal_singleton_isPrime D U hq hqD
  have hC0 : stalkIdeal {C} U hq ≠ ⊥ := stalkIdeal_ne_bot_of_ne C D hCD U hq hqD
  have hD0 : stalkIdeal {D} U hq ≠ ⊥ := stalkIdeal_ne_bot_of_ne D C hCD.symm U hq hqC
  have hmul : stalkIdeal {C} U hq * stalkIdeal {D} U hq = ⊥ := by
    rw [← hpD]
    exact stalkIdeal_mul_compl {C} U hq
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk q) (completedStalk X q)) :=
    KltDP.RingTheory.NodalCompletion.algebraMap_compl_injective
  have hAB : Ideal.map (e C q hqC hqCc).toRingHom
        (Ideal.map (algebraMap (X.presheaf.stalk q) (completedStalk X q)) (stalkIdeal {C} U hq)) *
      Ideal.map (e C q hqC hqCc).toRingHom
        (Ideal.map (algebraMap (X.presheaf.stalk q) (completedStalk X q)) (stalkIdeal {D} U hq)) =
        ⊥ := by
    rw [← Ideal.map_mul, ← Ideal.map_mul, hmul, Ideal.map_bot, Ideal.map_bot]
  have hA : Ideal.map (e C q hqC hqCc).toRingHom
      (Ideal.map (algebraMap (X.presheaf.stalk q) (completedStalk X q)) (stalkIdeal {C} U hq)) ≠ ⊥ :=
    fun h => hC0 ((Ideal.map_eq_bot_iff_of_injective hinj).mp
      ((Ideal.map_eq_bot_iff_of_injective (e C q hqC hqCc).injective).mp h))
  have hB : Ideal.map (e C q hqC hqCc).toRingHom
      (Ideal.map (algebraMap (X.presheaf.stalk q) (completedStalk X q)) (stalkIdeal {D} U hq)) ≠ ⊥ :=
    fun h => hD0 ((Ideal.map_eq_bot_iff_of_injective hinj).mp
      ((Ideal.map_eq_bot_iff_of_injective (e C q hqC hqCc).injective).mp h))
  obtain ⟨w, hw0, hw1, hli⟩ : ∃ w : Fin 2 → maximalIdeal (X.presheaf.stalk q),
      (w 0 : X.presheaf.stalk q) ∈ stalkIdeal {C} U hq ∧
      (w 1 : X.presheaf.stalk q) ∈ stalkIdeal {D} U hq ∧
      LinearIndependent (ResidueField (X.presheaf.stalk q))
        (fun l => (maximalIdeal (X.presheaf.stalk q)).toCotangent (w l)) := by
    rcases branches_of_mul_eq_bot k hAB hA hB with ⟨hA0, hB1⟩ | ⟨hA1, hB0⟩
    · exact KltDP.RingTheory.NodalCompletion.exists_branch_germs (e C q hqC hqCc) _ _ hC0 hD0 hmul
        (Equiv.refl _) hA0 hB1
    · exact KltDP.RingTheory.NodalCompletion.exists_branch_germs (e C q hqC hqCc) _ _ hC0 hD0 hmul
        (Equiv.swap 0 1) (by rw [Equiv.swap_apply_left]; exact hA1)
        (by rw [Equiv.swap_apply_right]; exact hB0)
  have hw1' : (w 1 : X.presheaf.stalk q) ∈ stalkIdeal ({C}ᶜ) U hq := by
    rw [hpD]
    exact hw1
  exact ⟨w, hw0, hw1', KltDP.RingTheory.NodalCompletion.finrank_cotangentSpace_eq_two (e C q hqC hqCc),
    hli⟩

/-- Universe check at universe `0`. -/
example (k₀ : Type) [Field k₀] (X₀ : Scheme.{0}) [NoetherianSpace X₀] [IsLocallyNoetherian X₀]
    [AlgebraicGeometry.IsReduced X₀] (f₀ : X₀ ⟶ Spec (CommRingCat.of k₀))
    (hno : ∀ (C D E : ↥(irreducibleComponents X₀)) (q : X₀),
      q ∈ C.1 → q ∈ D.1 → q ∈ E.1 → C = D ∨ C = E ∨ D = E)
    (e : ∀ (C : ↥(irreducibleComponents X₀)) (q : X₀), q ∈ C.1 →
      q ∈ (componentClosedUnion X₀ ({C}ᶜ) : Set X₀) →
      (letI := stalkAlgebra f₀ q; completedStalk X₀ q ≃ₐ[k₀] ordinaryDoublePointModel k₀)) :
    HasTransverseComponentBranches X₀ :=
  hasTransverseComponentBranches_of_completedStalk X₀ f₀ hno e

end KltDP.Geometry.RationalTreePicard

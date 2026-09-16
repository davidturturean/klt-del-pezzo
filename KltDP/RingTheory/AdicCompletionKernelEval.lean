import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Ideal.Cotangent

/-!
# The kernel of `AdicCompletion.eval`, completeness and locality of the completion, `m/m² ≃ m̂/m̂²`

BRIEF25, task 2. Let `R` be a Noetherian ring, `I` an ideal and `R̂ = AdicCompletion I R`. The
pinned Mathlib has the evaluation maps `evalₐ I n : R̂ →ₐ[R] R ⧸ I ^ n` (surjective) but not their
kernels. This module proves:

* **(M1)** `RingHom.ker (evalₐ I n) = Ideal.map (algebraMap R R̂) (I ^ n)` (`ker_evalₐ_eq_map_pow`),
  equivalently `LinearMap.ker (eval I R n) = I ^ n • ⊤` (`ker_eval_eq_smul_top`). The inclusion
  `⊇` is immediate; for `⊆`, an element `x = mk f` of the completion with `f n ∈ I ^ n` is the image
  of the Cauchy sequence `m ↦ f (n + m)` of the `I`-adic completion of the module `I ^ n`
  (`exists_map_subtype_eq`; the two filtrations `I ^ m • I ^ n = I ^ (m + n)` and `I ^ m ∩ I ^ n`
  on `I ^ n` are cofinal), and the completion of the finitely generated module `I ^ n` is generated
  over `R̂` by the images of `I ^ n` (Mathlib's `ofTensorProduct_surjective_of_finite`), which lie
  in `I ^ n R̂`.
* **(M2)** `R̂` is `I R̂`-adically complete (`isAdicComplete_map`): Hausdorff because
  `(I R̂) ^ n = ker (eval n)`, precomplete by the diagonal limit `L n = (f n) n`.
* **(M3)** for `m` maximal, `m R̂` is maximal (`map_isMaximal`, through `R̂ ⧸ m R̂ ≅ R ⧸ m`), `R̂` is
  a local ring (`isLocalRing_adicCompletion`, from Mathlib's `isLocalRing_of_isAdicComplete_maximal`)
  with maximal ideal `m R̂` (`maximalIdeal_adicCompletion`).
* **`m/m² ≃ m̂/m̂²`**: the comparison map `Ideal.mapCotangent m (m R̂) (Algebra.ofId R R̂)` of the
  cotangent spaces is bijective (`mapCotangent_bijective`), giving the `R`-linear equivalence
  `cotangentEquiv : m.Cotangent ≃ₗ[R] (m R̂).Cotangent`.
-/

noncomputable section

open AdicCompletion

universe u

namespace KltDP.RingTheory.AdicCompletionKernelEval

variable {R : Type u} [CommRing R] (I : Ideal R)

/-! ## Elementary identities -/

theorem algebraMap_eq_of (r : R) : algebraMap R (AdicCompletion I R) r = of I R r :=
  AdicCompletion.ext fun _ => rfl

theorem map_of {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (x : M) : map I f (of I M x) = of I N (f x) :=
  AdicCompletion.ext fun _ => rfl

theorem evalₐ_algebraMap (n : ℕ) (r : R) :
    evalₐ I n (algebraMap R (AdicCompletion I R) r) = Ideal.Quotient.mk (I ^ n) r := by
  rw [AlgHom.commutes]
  rfl

theorem evalₐ_surjective (n : ℕ) : Function.Surjective (evalₐ I n) := fun y => by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨algebraMap R (AdicCompletion I R) r, evalₐ_algebraMap I n r⟩

theorem evalₐ_eq_zero_iff (n : ℕ) (x : AdicCompletion I R) :
    evalₐ I n x = 0 ↔ eval I R n x = 0 := by
  obtain ⟨f, rfl⟩ := AdicCompletion.mk_surjective I R x
  rw [evalₐ_mk, Ideal.Quotient.eq_zero_iff_mem]
  show _ ↔ Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R R)) (f.val n) = 0
  rw [Submodule.Quotient.mk_eq_zero, Ideal.smul_eq_mul, Ideal.mul_top]

/-- The easy inclusion `I ^ n R̂ ⊆ ker (evalₐ I n)`. -/
theorem map_pow_le_ker_evalₐ (n : ℕ) :
    Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n) ≤ RingHom.ker (evalₐ I n) := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  rw [Ideal.mem_comap, RingHom.mem_ker, evalₐ_algebraMap]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hr

/-! ## The kernel of the evaluation for a Noetherian ring -/

/-- An element `mk f` of the completion with `f n ∈ I ^ n` comes from the `I`-adic completion of the
module `I ^ n`: the Cauchy sequence `m ↦ f (n + m)`. -/
theorem exists_map_subtype_eq (n : ℕ) (f : AdicCauchySequence I R) (hf : f.val n ∈ I ^ n) :
    ∃ y : AdicCompletion I ↥(I ^ n), map I (I ^ n).subtype y = mk I R f := by
  have hmem : ∀ m, f.val (n + m) ∈ I ^ n := fun m => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, AdicCompletion.Ideal.mk_eq_mk I (Nat.le_add_right n m) f]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hf
  let g : ℕ → ↥(I ^ n) := fun m => ⟨f.val (n + m), hmem m⟩
  have hg : ∀ m, g m ≡ g (m + 1) [SMOD (I ^ m • ⊤ : Submodule R ↥(I ^ n))] := fun m => by
    rw [SModEq.sub_mem, Submodule.mem_smul_top_iff]
    show f.val (n + m) - f.val (n + (m + 1)) ∈ I ^ m • I ^ n
    rw [Ideal.smul_eq_mul, ← pow_add, show m + n = n + m from Nat.add_comm m n]
    have h := f.property (Nat.le_succ (n + m))
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] at h
    exact h
  refine ⟨mk I ↥(I ^ n) (AdicCauchySequence.mk I ↥(I ^ n) g hg), AdicCompletion.ext fun m => ?_⟩
  show Submodule.Quotient.mk ((I ^ n).subtype (g m)) = Submodule.Quotient.mk (f.val m)
  exact AdicCauchySequence.mk_eq_mk (Nat.le_add_left m n) f

section Noetherian

variable [IsNoetherianRing R]

/-- **The kernel of the evaluation is `I ^ n R̂`** (the hard inclusion): the completion of the
finitely generated module `I ^ n` is generated over `R̂` by the images of `I ^ n`. -/
theorem ker_evalₐ_le_map_pow (n : ℕ) :
    RingHom.ker (evalₐ I n) ≤ Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n) := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  obtain ⟨f, rfl⟩ := AdicCompletion.mk_surjective I R x
  rw [evalₐ_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
  obtain ⟨y, hy⟩ := exists_map_subtype_eq I n f hx
  rw [← hy]
  clear hy
  obtain ⟨t, rfl⟩ := ofTensorProduct_surjective_of_finite I ↥(I ^ n) y
  induction t using TensorProduct.induction_on with
  | zero =>
    rw [_root_.map_zero, _root_.map_zero]
    exact Ideal.zero_mem _
  | tmul r j =>
    rw [ofTensorProduct_tmul, map_smul, map_of]
    refine Submodule.smul_mem _ r ?_
    rw [← algebraMap_eq_of]
    exact Ideal.mem_map_of_mem _ j.2
  | add t₁ t₂ h₁ h₂ =>
    rw [map_add, map_add]
    exact Ideal.add_mem _ h₁ h₂

/-- **(M1)** `ker (evalₐ I n) = I ^ n R̂` for a Noetherian ring `R`. -/
theorem ker_evalₐ_eq_map_pow (n : ℕ) :
    RingHom.ker (evalₐ I n) = Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n) :=
  le_antisymm (ker_evalₐ_le_map_pow I n) (map_pow_le_ker_evalₐ I n)

/-- **(M1)**, module form: `ker (eval I R n) = I ^ n • ⊤`. -/
theorem ker_eval_eq_smul_top (n : ℕ) :
    LinearMap.ker (eval I R n) = (I ^ n • ⊤ : Submodule R (AdicCompletion I R)) := by
  ext x
  rw [LinearMap.mem_ker, ← evalₐ_eq_zero_iff, ← RingHom.mem_ker, ker_evalₐ_eq_map_pow,
    Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]

theorem mem_map_pow_iff (n : ℕ) (x : AdicCompletion I R) :
    x ∈ Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n) ↔ eval I R n x = 0 := by
  rw [← ker_evalₐ_eq_map_pow, RingHom.mem_ker, evalₐ_eq_zero_iff]

/-! ## (M2): the completion is complete -/

/-- **(M2)** `R̂` is `I R̂`-adically complete. -/
theorem isAdicComplete_map :
    IsAdicComplete (Ideal.map (algebraMap R (AdicCompletion I R)) I) (AdicCompletion I R) where
  haus' x hx := by
    refine AdicCompletion.ext fun n => ?_
    have h := hx n
    rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow, mem_map_pow_iff] at h
    exact h
  prec' f hf := by
    refine ⟨⟨fun n => (f n).val n, fun {m n} hmn => ?_⟩, fun n => ?_⟩
    · show transitionMap I R hmn ((f n).val n) = (f m).val m
      rw [transitionMap_comp_eval_apply I R hmn (f n)]
      have h := hf hmn
      rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow, mem_map_pow_iff,
        map_sub, sub_eq_zero] at h
      exact h.symm
    · rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow, mem_map_pow_iff,
        map_sub, sub_eq_zero]
      rfl

end Noetherian

/-! ## (M3): the completion of a Noetherian ring at a maximal ideal is local -/

section Local

variable (m : Ideal R) [m.IsMaximal] [IsNoetherianRing R]

/-- `m R̂` is maximal: `R̂ ⧸ m R̂ ≅ R ⧸ m` is a field. -/
theorem map_isMaximal : (Ideal.map (algebraMap R (AdicCompletion m R)) m).IsMaximal := by
  haveI : (m ^ 1).IsMaximal := by rwa [pow_one]
  letI : Field (R ⧸ m ^ 1) := Ideal.Quotient.field (m ^ 1)
  have h := RingHom.ker_isMaximal_of_surjective (evalₐ m 1) (evalₐ_surjective m 1)
  rwa [ker_evalₐ_eq_map_pow, pow_one] at h

/-- **(M3)** `R̂` is a local ring. -/
theorem isLocalRing_adicCompletion : IsLocalRing (AdicCompletion m R) :=
  haveI := map_isMaximal m
  haveI := isAdicComplete_map m
  isLocalRing_of_isAdicComplete_maximal (Ideal.map (algebraMap R (AdicCompletion m R)) m)

/-- The maximal ideal of `R̂` is `m R̂`. -/
theorem maximalIdeal_adicCompletion :
    @IsLocalRing.maximalIdeal (AdicCompletion m R) _ (isLocalRing_adicCompletion m) =
      Ideal.map (algebraMap R (AdicCompletion m R)) m := by
  letI := isLocalRing_adicCompletion m
  exact (IsLocalRing.eq_maximalIdeal (map_isMaximal m)).symm

/-! ## `m/m² ≃ m̂/m̂²` -/

omit [m.IsMaximal] [IsNoetherianRing R] in
theorem le_comap_map_ofId :
    m ≤ (Ideal.map (algebraMap R (AdicCompletion m R)) m).comap (Algebra.ofId R (AdicCompletion m R)) :=
  fun x hx => by
    rw [Ideal.mem_comap, Algebra.ofId_apply]
    exact Ideal.mem_map_of_mem _ hx

/-- The comparison map `m/m² → m̂/m̂²`. -/
def cotangentMap : m.Cotangent →ₗ[R] (Ideal.map (algebraMap R (AdicCompletion m R)) m).Cotangent :=
  Ideal.mapCotangent m (Ideal.map (algebraMap R (AdicCompletion m R)) m)
    (Algebra.ofId R (AdicCompletion m R)) (le_comap_map_ofId m)

omit [m.IsMaximal] [IsNoetherianRing R] in
theorem cotangentMap_toCotangent (x : m) :
    cotangentMap m (m.toCotangent x) =
      (Ideal.map (algebraMap R (AdicCompletion m R)) m).toCotangent
        ⟨algebraMap R (AdicCompletion m R) x, le_comap_map_ofId m x.2⟩ :=
  Ideal.mapCotangent_toCotangent _ _ _ _ x

omit [m.IsMaximal] in
/-- Membership in `(m R̂) ^ 2 = m ^ 2 R̂ = ker (evalₐ m 2)`. -/
theorem mem_map_sq_iff (y : AdicCompletion m R) :
    y ∈ Ideal.map (algebraMap R (AdicCompletion m R)) m ^ 2 ↔ evalₐ m 2 y = 0 := by
  rw [← Ideal.map_pow, ← ker_evalₐ_eq_map_pow, RingHom.mem_ker]

omit [m.IsMaximal] in
theorem cotangentMap_injective : Function.Injective (cotangentMap m) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨x, rfl⟩ := m.toCotangent_surjective a
  rw [cotangentMap_toCotangent, Ideal.toCotangent_eq_zero, mem_map_sq_iff, evalₐ_algebraMap,
    Ideal.Quotient.eq_zero_iff_mem] at ha
  exact (Ideal.toCotangent_eq_zero m x).mpr ha

omit [m.IsMaximal] in
theorem cotangentMap_surjective : Function.Surjective (cotangentMap m) := by
  intro b
  obtain ⟨⟨y, hy⟩, rfl⟩ := (Ideal.map (algebraMap R (AdicCompletion m R)) m).toCotangent_surjective b
  obtain ⟨f, rfl⟩ := AdicCompletion.mk_surjective m R y
  have hf1 : f.val 1 ∈ m := by
    have h := (mem_map_pow_iff m 1 (mk m R f)).mp (by rwa [pow_one])
    rw [← evalₐ_eq_zero_iff, evalₐ_mk, Ideal.Quotient.eq_zero_iff_mem, pow_one] at h
    exact h
  have hf2 : f.val 2 ∈ m := by
    have h := AdicCompletion.Ideal.mk_eq_mk m (show 1 ≤ 2 by omega) f
    rw [pow_one] at h
    rw [← Ideal.Quotient.eq_zero_iff_mem, h]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hf1
  refine ⟨m.toCotangent ⟨f.val 2, hf2⟩, ?_⟩
  rw [cotangentMap_toCotangent, Ideal.toCotangent_eq]
  show algebraMap R (AdicCompletion m R) (f.val 2) - mk m R f ∈ _
  rw [mem_map_sq_iff, map_sub, evalₐ_algebraMap, evalₐ_mk, sub_self]

omit [m.IsMaximal] in
/-- **`m/m² ≃ m̂/m̂²`**: the comparison map of the cotangent spaces is bijective. -/
theorem mapCotangent_bijective : Function.Bijective (cotangentMap m) :=
  ⟨cotangentMap_injective m, cotangentMap_surjective m⟩

/-- The `R`-linear equivalence `m/m² ≃ₗ[R] m̂/m̂²`. -/
def cotangentEquiv : m.Cotangent ≃ₗ[R] (Ideal.map (algebraMap R (AdicCompletion m R)) m).Cotangent :=
  LinearEquiv.ofBijective (cotangentMap m) (mapCotangent_bijective m)

end Local

/-- Universe check at universe `0`. -/
example (R₀ : Type) [CommRing R₀] [IsNoetherianRing R₀] (m₀ : Ideal R₀) [m₀.IsMaximal] :
    m₀.Cotangent ≃ₗ[R₀] (Ideal.map (algebraMap R₀ (AdicCompletion m₀ R₀)) m₀).Cotangent :=
  cotangentEquiv m₀

end KltDP.RingTheory.AdicCompletionKernelEval

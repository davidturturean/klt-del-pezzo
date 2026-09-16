import Mathlib.RingTheory.Length
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.FiniteLength
import Mathlib.Algebra.Exact
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Length over a local `k`-algebra versus `k`-dimension

For a local ring `R` that is a `k`-algebra and a finite-length `R`-module `M`
(with the induced `k`-module structure), the `k`-length of `M` is the `R`-length
of `M` times the `k`-length of the residue field `R ⧸ m`. The proof takes a
simple submodule (the first step of a composition series), identifies it with the
residue field (every simple module over a local ring is `R ⧸ m`), and uses
additivity of length in exact sequences for both rings. When the residue field is
finite dimensional over `k`, this gives `dim_k M = length_R M · [R/m : k]`.

No geometric hypothesis appears; the scheme specialisation is a separate module.
-/

noncomputable section

universe u v

namespace KltDP.RingTheory

variable {k : Type u} {R : Type v} [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]

/-- Every simple module over a local ring is isomorphic to the residue field. -/
theorem exists_linearEquiv_quotient_maximalIdeal_of_isSimpleModule
    (N : Type*) [AddCommGroup N] [Module R N] [IsSimpleModule R N] :
    Nonempty (N ≃ₗ[R] R ⧸ IsLocalRing.maximalIdeal R) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R N›
  have h := IsLocalRing.eq_maximalIdeal hI
  subst h
  exact ⟨e⟩

/-- The `k`-length of a module of `R`-length `n` is `n` times the `k`-length of the
residue field. -/
theorem length_eq_length_mul_length_residue_of_eq (n : ℕ) :
    ∀ (M : Type v) [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M],
      Module.length R M = n →
      Module.length k M = (n : ℕ∞) * Module.length k (R ⧸ IsLocalRing.maximalIdeal R) := by
  induction n with
  | zero =>
    intro M _ _ _ _ hM
    haveI : Subsingleton M := Module.length_eq_zero_iff.mp (by simpa using hM)
    simp [Module.length_eq_zero]
  | succ n ih =>
    intro M _ _ _ _ hM
    have hfin : IsFiniteLength R M :=
      Module.length_ne_top_iff.mp (by rw [hM]; exact ENat.coe_ne_top _)
    obtain ⟨s, hs0, hs1⟩ := isFiniteLength_iff_exists_compositionSeries.mp hfin
    have hlen : Module.length R M = s.length := (Module.length_compositionSeries s hs0 hs1).symm
    have hpos : 0 < s.length := by
      have h1 : (s.length : ℕ∞) = ((n + 1 : ℕ) : ℕ∞) := hlen.symm.trans hM
      have h2 := ENat.coe_inj.mp h1
      omega
    -- The first step of the composition series is a simple submodule.
    have hstep := s.step ⟨0, hpos⟩
    have h0 : (Fin.castSucc (⟨0, hpos⟩ : Fin s.length)) = (0 : Fin (s.length + 1)) := by
      ext
      simp
    rw [h0] at hstep
    have hb : s 0 = ⊥ := hs0
    rw [hb] at hstep
    let N : Submodule R M := s (Fin.succ ⟨0, hpos⟩)
    haveI hN : IsSimpleModule R N := isSimpleModule_iff_isAtom.mpr (bot_covBy_iff.mp hstep)
    -- `R`-length of the quotient.
    have hadd : Module.length R M = Module.length R N + Module.length R (M ⧸ N) :=
      Module.length_eq_add_of_exact (f := N.subtype) (g := N.mkQ)
        (Submodule.injective_subtype N) (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N)
    rw [Module.length_eq_one R N] at hadd
    have hq : Module.length R (M ⧸ N) = n := by
      have hne : Module.length R (M ⧸ N) ≠ ⊤ := by
        intro h
        rw [h, add_top, hM] at hadd
        exact ENat.coe_ne_top _ hadd
      obtain ⟨m, hm⟩ : ∃ m : ℕ, Module.length R (M ⧸ N) = m :=
        ⟨_, (ENat.coe_toNat_eq_self.mpr hne).symm⟩
      rw [hm, hM] at hadd
      have h3 : n + 1 = 1 + m := by exact_mod_cast hadd
      rw [hm]
      exact congrArg _ (by omega)
    have hih := ih (M ⧸ N) hq
    -- `k`-length additivity and the residue-field identification.
    have haddk : Module.length k M = Module.length k N + Module.length k (M ⧸ N) :=
      Module.length_eq_add_of_exact (f := N.subtype.restrictScalars k) (g := N.mkQ.restrictScalars k)
        (Submodule.injective_subtype N) (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N)
    obtain ⟨e⟩ := exists_linearEquiv_quotient_maximalIdeal_of_isSimpleModule (R := R) N
    have hNk : Module.length k N = Module.length k (R ⧸ IsLocalRing.maximalIdeal R) :=
      (e.restrictScalars k).length_eq
    rw [haddk, hNk, hih, Nat.cast_succ, add_mul, one_mul, add_comm]

/-- `k`-length equals `R`-length times the residue length, for finite-length modules. -/
theorem length_eq_length_mul_length_residue
    (M : Type v) [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
    (hfl : IsFiniteLength R M) :
    Module.length k M = Module.length R M * Module.length k (R ⧸ IsLocalRing.maximalIdeal R) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Module.length R M = n :=
    ⟨_, (ENat.coe_toNat_eq_self.mpr (Module.length_ne_top_iff.mpr hfl)).symm⟩
  rw [hn]
  exact length_eq_length_mul_length_residue_of_eq n M hn

/-- `dim_k M = length_R M · [R/m : k]` for a finite-length `R`-module `M` when the
residue field is finite dimensional over `k`; `M` is then finite dimensional. -/
theorem finite_and_finrank_eq_length_mul_finrank_residue
    (M : Type v) [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
    (hfl : IsFiniteLength R M) [Module.Finite k (R ⧸ IsLocalRing.maximalIdeal R)] :
    Module.Finite k M ∧
      Module.finrank k M =
        (Module.length R M).toNat * Module.finrank k (R ⧸ IsLocalRing.maximalIdeal R) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Module.length R M = n :=
    ⟨_, (ENat.coe_toNat_eq_self.mpr (Module.length_ne_top_iff.mpr hfl)).symm⟩
  have h := length_eq_length_mul_length_residue_of_eq (k := k) n M hn
  rw [Module.length_eq_finrank k (R ⧸ IsLocalRing.maximalIdeal R), ← Nat.cast_mul] at h
  have hfin : IsFiniteLength k M :=
    Module.length_ne_top_iff.mp (by rw [h]; exact ENat.coe_ne_top _)
  haveI : IsNoetherian k M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).1
  haveI hM : Module.Finite k M := ⟨IsNoetherian.noetherian ⊤⟩
  refine ⟨hM, ?_⟩
  rw [Module.length_eq_finrank k M] at h
  have h' : Module.finrank k M = n * Module.finrank k (R ⧸ IsLocalRing.maximalIdeal R) :=
    ENat.coe_inj.mp h
  rw [h', hn, ENat.toNat_coe]

end KltDP.RingTheory

/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel,
  Jujian Zhang, Weihong Xu, Andrew Yang, Brian Nugent

Adapted from QuasicoherentTilde.Aux.of_eq_iSup_basicOpen in Mathlib
633b366493a76df88a2bff099ed0cbf711a59ec9. Finite maxima use the pinned
Finset API; all gluing uses the original sheaf and section restrictions.
-/
import KltDP.Geometry.AffineModuleDenominators
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Descent of denominator extension across a finite basic-open cover

Local extensions can be multiplied by uniform powers of a function until
they agree on every overlap. The actual sheaf condition then glues them.
The same finite maximum argument detects zero globally. This proves the
denominator properties from the corresponding properties on an actual
finite basic-open cover; no global extension or gluing section is an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineModuleTilde

variable {R : Type u} [CommRing R] (M : (Spec (.of R)).Modules)

/-- The actual denominator properties descend through a finite basic-open cover. -/
theorem DenominatorExtension.of_finite_basicOpen_cover
    (V : (Spec (.of R)).Opens) {ι : Type u} [Fintype ι]
    (g : ι → R) (hg : V = ⨆ i, PrimeSpectrum.basicOpen (g i))
    (h₁ : ∀ i, DenominatorExtension M (PrimeSpectrum.basicOpen (g i))) :
    DenominatorExtension M V := by
  classical
  have hgle (i : ι) : PrimeSpectrum.basicOpen (g i) ≤ V := by
    rw [hg]
    exact le_iSup (fun i => PrimeSpectrum.basicOpen (g i)) i
  have h₂ (i j : ι) : DenominatorExtension M (PrimeSpectrum.basicOpen (g i * g j)) :=
    DenominatorExtension.of_le M (g i * g j)
      (PrimeSpectrum.basicOpen_mul_le_left (g i) (g j)) (h₁ i)
  refine ⟨?_, ?_⟩
  · intro f hf s
    have hfgi (i : ι) : PrimeSpectrum.basicOpen (f * g i) ≤ PrimeSpectrum.basicOpen (g i) :=
      PrimeSpectrum.basicOpen_mul_le_right f (g i)
    let s' (i : ι) : sectionModule M (PrimeSpectrum.basicOpen (f * g i)) :=
      sectionRestrict M (PrimeSpectrum.basicOpen_mul_le_left f (g i)) s
    have hlocal (i : ι) : ∃ (n : ℕ) (t : sectionModule M (PrimeSpectrum.basicOpen (g i))),
        f ^ n • s' i = sectionRestrict M (hfgi i) t := by
      obtain ⟨n, t', ht'⟩ := (h₁ i).existence (f * g i) (hfgi i) (s' i)
      have hu := sectionScalar_map_units M (g i) le_rfl
        (⟨g i ^ n, n, rfl⟩ : Submonoid.powers (g i))
      obtain ⟨ψ, hψ⟩ := IsUnit.exists_right_inv hu
      have hc : g i ^ n • ψ t' = t' := by
        exact DFunLike.congr_fun hψ t'
      refine ⟨n, ψ t', ?_⟩
      apply sectionScalar_pow_smul_injective M (g i) (hfgi i) n
      calc
        g i ^ n • (f ^ n • s' i) = (f * g i) ^ n • s' i := by
          rw [mul_pow, mul_smul, smul_comm]
        _ = sectionRestrict M (hfgi i) t' := ht'.symm
        _ = g i ^ n • sectionRestrict M (hfgi i) (ψ t') := by
          rw [← sectionRestrict_smul, hc]
    choose n t' ht' using hlocal
    let N : ℕ := Finset.univ.sup n
    have hnN (i : ι) : n i ≤ N := Finset.le_sup (f := n) (Finset.mem_univ i)
    let t (i : ι) : sectionModule M (PrimeSpectrum.basicOpen (g i)) :=
      f ^ (N - n i) • t' i
    have ht (i : ι) : f ^ N • s' i = sectionRestrict M (hfgi i) (t i) := by
      dsimp only [t]
      rw [sectionRestrict_smul, ← ht', ← mul_smul, ← pow_add,
        Nat.sub_add_cancel (hnN i)]
    have hpairs (i j : ι) : ∃ m : ℕ,
        sectionRestrict M (PrimeSpectrum.basicOpen_mul_le_left (g i) (g j))
            (f ^ m • t i) =
          sectionRestrict M (PrimeSpectrum.basicOpen_mul_le_right (g i) (g j))
            (f ^ m • t j) := by
      let ui : sectionModule M (PrimeSpectrum.basicOpen (g i * g j)) :=
        sectionRestrict M (PrimeSpectrum.basicOpen_mul_le_left (g i) (g j)) (t i)
      let uj : sectionModule M (PrimeSpectrum.basicOpen (g i * g j)) :=
        sectionRestrict M (PrimeSpectrum.basicOpen_mul_le_right (g i) (g j)) (t j)
      have hi : PrimeSpectrum.basicOpen (f * (g i * g j)) ≤
          PrimeSpectrum.basicOpen (f * g i) := by
        rw [← mul_assoc]
        exact PrimeSpectrum.basicOpen_mul_le_left (f * g i) (g j)
      have hj : PrimeSpectrum.basicOpen (f * (g i * g j)) ≤
          PrimeSpectrum.basicOpen (f * g j) := by
        rw [mul_comm (g i) (g j), ← mul_assoc]
        exact PrimeSpectrum.basicOpen_mul_le_left (f * g j) (g i)
      have hui : sectionRestrict M (PrimeSpectrum.basicOpen_mul_le_right f (g i * g j)) ui =
          sectionRestrict M hi (sectionRestrict M (hfgi i) (t i)) := by
        simp only [ui, sectionRestrict_comp]
      have huj : sectionRestrict M (PrimeSpectrum.basicOpen_mul_le_right f (g i * g j)) uj =
          sectionRestrict M hj (sectionRestrict M (hfgi j) (t j)) := by
        simp only [uj, sectionRestrict_comp]
      have hz : sectionRestrict M (PrimeSpectrum.basicOpen_mul_le_right f (g i * g j))
          (ui - uj) = 0 := by
        rw [map_sub, hui, huj, ← ht i, ← ht j, sectionRestrict_smul, sectionRestrict_smul]
        simp only [s', sectionRestrict_comp, sub_self]
      obtain ⟨m, hm⟩ := (h₂ i j).uniqueness (f * (g i * g j))
        (PrimeSpectrum.basicOpen_mul_le_right f (g i * g j)) (ui - uj) hz
      refine ⟨m, ?_⟩
      calc
        _ = f ^ m • ui := sectionRestrict_smul M
          (PrimeSpectrum.basicOpen_mul_le_left (g i) (g j)) (f ^ m) (t i)
        _ = f ^ m • uj := by
          apply sectionScalar_pow_smul_injective M (g i * g j) le_rfl m
          have hzero : (g i * g j) ^ m • (f ^ m • (ui - uj)) = 0 := by
            calc
              _ = (f * (g i * g j)) ^ m • (ui - uj) := by
                rw [mul_pow f (g i * g j), mul_smul]
                exact smul_comm ((g i * g j) ^ m) (f ^ m) (ui - uj)
              _ = 0 := hm
          simpa only [smul_sub, sub_eq_zero] using hzero
        _ = _ := (sectionRestrict_smul M
          (PrimeSpectrum.basicOpen_mul_le_right (g i) (g j)) (f ^ m) (t j)).symm
    choose k hk using hpairs
    let K : ℕ := Finset.univ.sup (fun q : ι × ι => k q.1 q.2)
    have hkK (i j : ι) : k i j ≤ K :=
      Finset.le_sup (f := fun q : ι × ι => k q.1 q.2) (Finset.mem_univ (i, j))
    have hK (i j : ι) :
        sectionRestrict M (PrimeSpectrum.basicOpen_mul_le_left (g i) (g j))
            (f ^ K • t i) =
          sectionRestrict M (PrimeSpectrum.basicOpen_mul_le_right (g i) (g j))
            (f ^ K • t j) := by
      have h := congrArg
        (fun z : sectionModule M (PrimeSpectrum.basicOpen (g i * g j)) =>
          f ^ (K - k i j) • z) (hk i j)
      simpa only [sectionRestrict_smul, ← mul_smul, ← pow_add,
        Nat.sub_add_cancel (hkK i j)] using h
    obtain ⟨a, ha, _⟩ := TopCat.Sheaf.existsUnique_gluing'
      ((modulesSpecToSheaf R).obj M) (fun i => PrimeSpectrum.basicOpen (g i)) V
      (fun i => homOfLE (hgle i)) (by rw [hg]) (fun i => f ^ K • t i) (by
        intro i j
        change sectionRestrict M
            (show PrimeSpectrum.basicOpen (g i) ⊓ PrimeSpectrum.basicOpen (g j) ≤
              PrimeSpectrum.basicOpen (g i) from inf_le_left) (f ^ K • t i) =
          sectionRestrict M
            (show PrimeSpectrum.basicOpen (g i) ⊓ PrimeSpectrum.basicOpen (g j) ≤
              PrimeSpectrum.basicOpen (g j) from inf_le_right) (f ^ K • t j)
        have hprod : PrimeSpectrum.basicOpen (g i) ⊓ PrimeSpectrum.basicOpen (g j) ≤
            PrimeSpectrum.basicOpen (g i * g j) :=
          le_of_eq (PrimeSpectrum.basicOpen_mul (g i) (g j)).symm
        have hij := congrArg (sectionRestrict M hprod) (hK i j)
        simpa only [sectionRestrict_comp] using hij)
    refine ⟨N + K, a, ?_⟩
    have hcover : PrimeSpectrum.basicOpen f ≤ ⨆ i, PrimeSpectrum.basicOpen (f * g i) := by
      intro x hx
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp ((le_of_eq hg) (hf hx))
      refine Opens.mem_iSup.mpr ⟨i, ?_⟩
      rw [PrimeSpectrum.basicOpen_mul]
      exact ⟨hx, hi⟩
    apply TopCat.Sheaf.eq_of_locally_eq' ((modulesSpecToSheaf R).obj M)
      (fun i => PrimeSpectrum.basicOpen (f * g i)) (PrimeSpectrum.basicOpen f)
      (fun i => homOfLE (PrimeSpectrum.basicOpen_mul_le_left f (g i))) hcover
    intro i
    change sectionRestrict M (PrimeSpectrum.basicOpen_mul_le_left f (g i))
        (sectionRestrict M hf a) =
      sectionRestrict M (PrimeSpectrum.basicOpen_mul_le_left f (g i)) (f ^ (N + K) • s)
    have hai : sectionRestrict M (hgle i) a = f ^ K • t i := ha i
    calc
      _ = sectionRestrict M (hfgi i) (sectionRestrict M (hgle i) a) := by
        simp only [sectionRestrict_comp]
      _ = sectionRestrict M (hfgi i) (f ^ K • t i) :=
        congrArg (sectionRestrict M (hfgi i)) hai
      _ = f ^ K • sectionRestrict M (hfgi i) (t i) :=
        sectionRestrict_smul M (hfgi i) (f ^ K) (t i)
      _ = f ^ K • (f ^ N • s' i) :=
        congrArg (fun z => f ^ K • z) (ht i).symm
      _ = _ := by
        rw [sectionRestrict_smul, pow_add, mul_smul]
        exact smul_comm (f ^ K) (f ^ N) (s' i)
  · intro f hf t hs
    have hlocal (i : ι) : ∃ n : ℕ,
        sectionRestrict M (hgle i) (f ^ n • t) = 0 := by
      have hz : sectionRestrict M (PrimeSpectrum.basicOpen_mul_le_right f (g i))
          (sectionRestrict M (hgle i) t) = 0 := by
        rw [sectionRestrict_comp,
          ← sectionRestrict_comp M hf (PrimeSpectrum.basicOpen_mul_le_left f (g i)), hs, map_zero]
      obtain ⟨n, hn⟩ := (h₁ i).uniqueness (f * g i)
        (PrimeSpectrum.basicOpen_mul_le_right f (g i)) (sectionRestrict M (hgle i) t) hz
      refine ⟨n, ?_⟩
      rw [sectionRestrict_smul]
      apply sectionScalar_pow_smul_injective M (g i) le_rfl n
      change g i ^ n • (f ^ n • sectionRestrict M (hgle i) t) = g i ^ n • 0
      calc
        _ = (f * g i) ^ n • sectionRestrict M (hgle i) t := by
          rw [mul_pow, mul_smul, smul_comm]
        _ = 0 := hn
        _ = _ := (smul_zero (g i ^ n)).symm
    choose n hn using hlocal
    let N : ℕ := Finset.univ.sup n
    have hnN (i : ι) : n i ≤ N := Finset.le_sup (f := n) (Finset.mem_univ i)
    refine ⟨N, ?_⟩
    apply TopCat.Sheaf.eq_of_locally_eq' ((modulesSpecToSheaf R).obj M)
      (fun i => PrimeSpectrum.basicOpen (g i)) V
      (fun i => homOfLE (hgle i)) (by rw [hg])
    intro i
    change sectionRestrict M (hgle i) (f ^ N • t) = sectionRestrict M (hgle i) 0
    have he : N = (N - n i) + n i := (Nat.sub_add_cancel (hnN i)).symm
    rw [he, pow_add, mul_smul, sectionRestrict_smul, hn i, smul_zero, map_zero]

end KltDP.Geometry.AffineModuleTilde

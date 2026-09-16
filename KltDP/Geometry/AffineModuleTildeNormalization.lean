/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Andrew Yang

The finite normalization follows the generalized StructureSheaf argument in
Mathlib at 633b366493a76df88a2bff099ed0cbf711a59ec9, adapted to the original
pinned tilde sections. Pairwise equality is detected by the separately proved
annihilator lemma; scalar identities use the pinned ring and module laws.
-/
import KltDP.Geometry.AffineModuleTildeFractions
import KltDP.Geometry.AffineModuleTildeSeparation
import Mathlib.Tactic.Ring

/-!
# Compatible fractions on compact opens

A section on a compact open admits a finite basic-open cover by fractions.
After multiplying each numerator and denominator by a common power of its
denominator, every pair of numerators satisfies the cross-multiplication
identity in the original module. The restrictions remain those of the
original pinned tilde sheaf.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineModuleTilde

variable {R : Type u} [CommRing R]

/-- A compact open has a finite fraction presentation with exact pairwise
cross-multiplication identities in the original module. -/
theorem exists_compatible_fractions (M : ModuleCat.{u} R)
    (U : Opens (PrimeSpectrum R)) (hU : IsCompact (U : Set (PrimeSpectrum R)))
    (s : M.tildeInModuleCat.obj (op U)) :
    ∃ (ι : Type u) (_ : Fintype ι) (a : ι → M) (b : ι → R)
      (ibU : ∀ i, PrimeSpectrum.basicOpen (b i) ≤ U),
      (U ≤ ⨆ i, PrimeSpectrum.basicOpen (b i)) ∧
      (∀ i j, b j • a i = b i • a j) ∧
      ∀ i, M.tildeInModuleCat.map (homOfLE (ibU i)).op s =
        ModuleCat.Tilde.const M (a i) (b i) (PrimeSpectrum.basicOpen (b i))
          (fun _ hy => hy) := by
  classical
  choose g a hg hx H using fun x : U => exists_const_basicOpen M U s x
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover
    (fun i : U => (PrimeSpectrum.basicOpen (g i) : Set (PrimeSpectrum R)))
    (fun i => (PrimeSpectrum.basicOpen (g i)).isOpen)
    (fun x hxU => Set.mem_iUnion.mpr ⟨⟨x, hxU⟩, hx ⟨x, hxU⟩⟩)
  have hpair (i j : t) : ∃ k : ℕ,
      (g i * g j) ^ k • (g j • a i) = (g i * g j) ^ k • (g i • a j) := by
    apply toOpen_eq_imp_exists_pow_smul_eq M (g i * g j) (g j • a i) (g i • a j)
    apply Subtype.ext
    funext x
    have hxi : x.val ∈ PrimeSpectrum.basicOpen (g i) :=
      PrimeSpectrum.basicOpen_mul_le_left (g i) (g j) x.property
    have hxj : x.val ∈ PrimeSpectrum.basicOpen (g j) :=
      PrimeSpectrum.basicOpen_mul_le_right (g i) (g j) x.property
    have hiDen := const_smul_denominator M (PrimeSpectrum.basicOpen (g i))
      (a i) (g i) (fun _ hy => hy)
    have hjDen := const_smul_denominator M (PrimeSpectrum.basicOpen (g j))
      (a j) (g j) (fun _ hy => hy)
    rw [H i] at hiDen
    rw [H j] at hjDen
    have hi := congrArg
      (fun v : M.tildeInModuleCat.obj (op (PrimeSpectrum.basicOpen (g i))) =>
        v.val ⟨x.val, hxi⟩) hiDen
    have hj := congrArg
      (fun v : M.tildeInModuleCat.obj (op (PrimeSpectrum.basicOpen (g j))) =>
        v.val ⟨x.val, hxj⟩) hjDen
    change g i • s.val ⟨x.val, hg i hxi⟩ =
      LocalizedModule.mkLinearMap x.val.asIdeal.primeCompl M (a i) at hi
    change g j • s.val ⟨x.val, hg j hxj⟩ =
      LocalizedModule.mkLinearMap x.val.asIdeal.primeCompl M (a j) at hj
    change LocalizedModule.mkLinearMap x.val.asIdeal.primeCompl M (g j • a i) =
      LocalizedModule.mkLinearMap x.val.asIdeal.primeCompl M (g i • a j)
    rw [map_smul, map_smul, ← hi, ← hj]
    exact smul_comm (g j) (g i) _
  choose n hn using hpair
  let N : ℕ := Finset.univ.sup (fun q : t × t => n q.1 q.2)
  have hnN (i j : t) : n i j ≤ N :=
    Finset.le_sup (f := fun q : t × t => n q.1 q.2) (Finset.mem_univ (i, j))
  have hN (i j : t) :
      (g i * g j) ^ N • (g j • a i) = (g i * g j) ^ N • (g i • a j) := by
    let c : R := g i * g j
    have hc : c ^ N = c ^ (N - n i j) * c ^ n i j := by
      rw [← pow_add, Nat.sub_add_cancel (hnN i j)]
    calc
      c ^ N • (g j • a i) =
          (c ^ (N - n i j) * c ^ n i j) • (g j • a i) :=
        congrArg (fun r : R => r • (g j • a i)) hc
      _ = c ^ (N - n i j) • (c ^ n i j • (g j • a i)) := mul_smul _ _ _
      _ = c ^ (N - n i j) • (c ^ n i j • (g i • a j)) :=
        congrArg (fun m : M => c ^ (N - n i j) • m) (hn i j)
      _ = (c ^ (N - n i j) * c ^ n i j) • (g i • a j) :=
        (mul_smul _ _ _).symm
      _ = c ^ N • (g i • a j) :=
        congrArg (fun r : R => r • (g i • a j)) hc.symm
  have hb (i : t) : PrimeSpectrum.basicOpen (g i ^ (N + 1)) =
      PrimeSpectrum.basicOpen (g i) :=
    PrimeSpectrum.basicOpen_pow (g i) (N + 1) (Nat.succ_pos N)
  have ibU (i : t) : PrimeSpectrum.basicOpen (g i ^ (N + 1)) ≤ U :=
    (hb i).trans_le (hg i)
  refine ⟨t, inferInstance, (fun i => g i ^ N • a i),
    (fun i => g i ^ (N + 1)), ibU, ?_, ?_, ?_⟩
  · intro x hxU
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht hxU)
    obtain ⟨hit, hxi⟩ := Set.mem_iUnion.mp hi
    refine Opens.mem_iSup.mpr ⟨⟨i, hit⟩, ?_⟩
    simpa only [hb ⟨i, hit⟩] using hxi
  · intro i j
    calc
      g j ^ (N + 1) • (g i ^ N • a i) =
          (g i * g j) ^ N • (g j • a i) := by
        simp only [← mul_smul, mul_pow, pow_succ]
        congr 1
        ring
      _ = (g i * g j) ^ N • (g i • a j) := hN i j
      _ = g i ^ (N + 1) • (g j ^ N • a j) := by
        simp only [← mul_smul, mul_pow, pow_succ]
        congr 1
        ring
  · intro i
    apply Subtype.ext
    funext x
    have hxi : x.val ∈ PrimeSpectrum.basicOpen (g i) := by
      simpa only [hb i] using x.property
    have e := congrArg
      (fun v : M.tildeInModuleCat.obj (op (PrimeSpectrum.basicOpen (g i))) =>
        v.val ⟨x.val, hxi⟩) (H i)
    change LocalizedModule.mk (a i) ⟨g i, hxi⟩ =
      s.val ⟨x.val, hg i hxi⟩ at e
    change s.val ⟨x.val, ibU i x.property⟩ =
      LocalizedModule.mk (g i ^ N • a i) ⟨g i ^ (N + 1), x.property⟩
    refine e.symm.trans (LocalizedModule.mk_eq.mpr ⟨1, ?_⟩)
    simp only [Submonoid.smul_def, Subtype.coe_mk, one_smul, ← mul_smul]
    rw [pow_succ']

end KltDP.Geometry.AffineModuleTilde

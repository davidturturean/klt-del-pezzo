/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Andrew Yang

The denominator-clearing argument follows the generalized StructureSheaf
proof in Mathlib at 633b366493a76df88a2bff099ed0cbf711a59ec9, adapted to
the original pinned tilde sections and their original canonical map.
-/
import KltDP.Geometry.AffineModuleTildeNormalization
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Localization of the original affine module sheaf on basic opens

The original canonical map from M to its tilde sections on D(f) satisfies
the three localization axioms. Surjectivity up to a denominator follows
from compatible local fractions and an ideal radical calculation. No
replacement sheaf or affine reconstruction hypothesis is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineModuleTilde

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)

/-- A power of f clears the denominators of an actual tilde section on D(f). -/
theorem exists_pow_smul_eq_toOpen (f : R)
    (s : M.tildeInModuleCat.obj (op (PrimeSpectrum.basicOpen f))) :
    ∃ (n : ℕ) (m : M),
      f ^ n • s = ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen f) m := by
  classical
  obtain ⟨ι, hι, a, b, ibU, hcover, hab, H⟩ :=
    exists_compatible_fractions M (PrimeSpectrum.basicOpen f)
      (PrimeSpectrum.isCompact_basicOpen f) s
  letI := hι
  have hrad : f ∈ (Ideal.span (Set.range b)).radical := by
    rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
      PrimeSpectrum.zeroLocus_span, PrimeSpectrum.mem_vanishingIdeal]
    intro x hx
    by_contra hfx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover hfx)
    exact hi ((PrimeSpectrum.mem_zeroLocus x (Set.range b)).mp hx (Set.mem_range_self i))
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
  rw [Ideal.span, Finsupp.mem_span_range_iff_exists_finsupp] at hn
  obtain ⟨c, hc⟩ := hn
  rw [Finsupp.sum_fintype _ _ (by simp)] at hc
  change ∑ i, c i * b i = f ^ n at hc
  let m : M := ∑ i, c i • a i
  have hcombo (i : ι) : b i • m = f ^ n • a i := by
    calc
      b i • m = ∑ j, c j • (b i • a j) := by
        simp only [m, Finset.smul_sum]
        exact Finset.sum_congr rfl (fun j _ => smul_comm (b i) (c j) (a j))
      _ = ∑ j, c j • (b j • a i) := by simp_rw [hab _ i]
      _ = (∑ j, c j * b j) • a i := by
        simp only [mul_smul, Finset.sum_smul]
      _ = f ^ n • a i := by rw [hc]
  refine ⟨n, m, ?_⟩
  apply Subtype.ext
  funext y
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover y.property)
  have hden := const_smul_denominator M (PrimeSpectrum.basicOpen (b i))
    (a i) (b i) (fun _ hy => hy)
  rw [← H i] at hden
  have hei := congrArg
    (fun v : M.tildeInModuleCat.obj (op (PrimeSpectrum.basicOpen (b i))) =>
      v.val ⟨y.val, hi⟩) hden
  change b i • s.val y = LocalizedModule.mkLinearMap y.val.asIdeal.primeCompl M (a i) at hei
  apply IsLocalizedModule.smul_injective
    (LocalizedModule.mkLinearMap y.val.asIdeal.primeCompl M)
    (⟨b i, hi⟩ : y.val.asIdeal.primeCompl)
  change b i • (f ^ n • s.val y) =
    b i • LocalizedModule.mkLinearMap y.val.asIdeal.primeCompl M m
  calc
    b i • (f ^ n • s.val y) = f ^ n • (b i • s.val y) := smul_comm _ _ _
    _ = f ^ n • LocalizedModule.mkLinearMap y.val.asIdeal.primeCompl M (a i) := by rw [hei]
    _ = LocalizedModule.mkLinearMap y.val.asIdeal.primeCompl M (f ^ n • a i) :=
      (map_smul _ _ _).symm
    _ = LocalizedModule.mkLinearMap y.val.asIdeal.primeCompl M (b i • m) := by rw [hcombo]
    _ = b i • LocalizedModule.mkLinearMap y.val.asIdeal.primeCompl M m := map_smul _ _ _

/-- The pinned canonical map to sections on D(f) is the actual module localization. -/
instance toOpen_isLocalizedModule (f : R) :
    IsLocalizedModule (Submonoid.powers f)
      (ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom where
  map_units := basicOpen_map_units M f
  surj' s := by
    obtain ⟨n, m, hm⟩ := exists_pow_smul_eq_toOpen M f s
    exact ⟨(m, ⟨f ^ n, n, rfl⟩), hm⟩
  exists_of_eq h := by
    obtain ⟨n, hn⟩ := toOpen_eq_imp_exists_pow_smul_eq M f _ _ h
    exact ⟨⟨f ^ n, n, rfl⟩, hn⟩

/-- The canonical localization is linearly equivalent to the original basic-open sections. -/
def basicOpenSectionsEquiv (f : R) :
    LocalizedModule (Submonoid.powers f) M ≃ₗ[R]
      M.tildeInModuleCat.obj (op (PrimeSpectrum.basicOpen f)) :=
  IsLocalizedModule.iso (Submonoid.powers f)
    (ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom

@[simp]
theorem basicOpenSectionsEquiv_mkLinearMap (f : R) (m : M) :
    basicOpenSectionsEquiv M f (LocalizedModule.mkLinearMap (Submonoid.powers f) M m) =
      ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen f) m := by
  exact IsLocalizedModule.iso_mk_one (Submonoid.powers f)
    (ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom m

end KltDP.Geometry.AffineModuleTilde

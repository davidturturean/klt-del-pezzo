/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Andrew Yang

The radical argument follows Mathlib's StructureSheaf.toBasicOpen_injective,
adapted to the original pinned module-valued sections using the annihilator
of a singleton span. All algebraic and spectrum lemmas are imported from
the pinned library.
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Ideal.Maps

/-!
# Equality of canonical module sections on a basic open

If two canonical sections agree on D(f), a power of f makes their original
module elements equal. The argument uses the annihilator of their difference
and tests membership at every prime containing that annihilator. It applies
to arbitrary modules over a commutative ring.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineModuleTilde

variable {R : Type u} [CommRing R]

/-- Equality of the original canonical sections on D(f) is detected by a power of f. -/
theorem toOpen_eq_imp_exists_pow_smul_eq (M : ModuleCat.{u} R) (f : R) (m n : M)
    (h : ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen f) m =
      ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen f) n) :
    ∃ k : ℕ, f ^ k • m = f ^ k • n := by
  let I : Ideal R := (Submodule.span R ({m - n} : Set M)).annihilator
  have hf : f ∈ I.radical := by
    rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
      PrimeSpectrum.mem_vanishingIdeal]
    intro p hp
    by_contra hfp
    have he : LocalizedModule.mk m (1 : p.asIdeal.primeCompl) =
        LocalizedModule.mk n (1 : p.asIdeal.primeCompl) :=
      congrArg (fun s : (ModuleCat.tildeInModuleCat M).obj
        (op (PrimeSpectrum.basicOpen f)) => s.val ⟨p, hfp⟩) h
    obtain ⟨r, hr⟩ := LocalizedModule.mk_eq.mp he
    have hrmn : (r : R) • m = (r : R) • n := by
      simpa only [one_smul, Submonoid.smul_def] using hr
    have hrI : (r : R) ∈ I := by
      exact (Submodule.mem_annihilator_span_singleton (m - n) (r : R)).mpr
        (by simpa only [smul_sub, sub_eq_zero] using hrmn)
    exact r.property ((PrimeSpectrum.mem_zeroLocus p (I : Set R)).mp hp hrI)
  obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp hf
  refine ⟨k, ?_⟩
  have hkzero := (Submodule.mem_annihilator_span_singleton (m - n) (f ^ k)).mp hk
  simpa only [smul_sub, sub_eq_zero] using hkzero

end KltDP.Geometry.AffineModuleTilde

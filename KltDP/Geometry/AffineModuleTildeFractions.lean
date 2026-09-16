/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The basic-open fraction refinement follows the generalized StructureSheaf
proof in Mathlib at 633b366493a76df88a2bff099ed0cbf711a59ec9, adapted to
the original pinned tilde sections. Its original notice is retained here:

Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Localization.Basic

/-!
# Basic-open fractions in the original affine module sheaf

Every original tilde section is locally a fraction on a basic open whose
defining function is its denominator. Scalars invertible on a basic open
act invertibly on these actual section modules. These are the elementary
inputs for proving that sections on D(f) are the localization of M at f.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineModuleTilde

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)

local instance (U : Opens (PrimeSpectrum R)) :
    Module ((Spec.structureSheaf R).val.obj (op U))
      (M.tildeInModuleCat.obj (op U)) :=
  (M.tilde.val.obj (op U)).isModule

/-- The two original scalar actions agree along the canonical section-ring map. -/
theorem toOpen_scalar_smul (U : Opens (PrimeSpectrum R)) (r : R)
    (s : M.tildeInModuleCat.obj (op U)) :
    StructureSheaf.toOpen R U r • s = r • s := by
  apply Subtype.ext
  funext x
  change algebraMap R (Localization.AtPrime x.val.asIdeal) r • s.val x = r • s.val x
  exact IsScalarTower.algebraMap_smul (Localization.AtPrime x.val.asIdeal) r (s.val x)

/-- The actual scalar endomorphism defined by f is invertible on D(f). -/
theorem isUnit_basicOpen_scalar (f : R) :
    IsUnit (algebraMap R
      (Module.End R (M.tildeInModuleCat.obj (op (PrimeSpectrum.basicOpen f)))) f) := by
  rw [Module.End.isUnit_iff]
  have h := (StructureSheaf.isUnit_to_basicOpen_self R f).smul_bijective
    (β := M.tildeInModuleCat.obj (op (PrimeSpectrum.basicOpen f)))
  have hfun : (fun s : M.tildeInModuleCat.obj (op (PrimeSpectrum.basicOpen f)) =>
      StructureSheaf.toOpen R (PrimeSpectrum.basicOpen f) f • s) = (fun s => f • s) :=
    funext (toOpen_scalar_smul M (PrimeSpectrum.basicOpen f) f)
  rw [hfun] at h
  exact h

/-- All powers of f act by units on the actual section module on D(f). -/
theorem basicOpen_map_units (f : R) (s : Submonoid.powers f) :
    IsUnit (algebraMap R
      (Module.End R (M.tildeInModuleCat.obj (op (PrimeSpectrum.basicOpen f)))) s) := by
  obtain ⟨n, hn⟩ := s.property
  rw [← hn, map_pow]
  exact (isUnit_basicOpen_scalar M f).pow n

/-- The original fractional section satisfies its actual denominator equation. -/
theorem const_smul_denominator (U : Opens (PrimeSpectrum R)) (m : M) (r : R)
    (hr : ∀ x ∈ U, r ∈ (x : PrimeSpectrum R).asIdeal.primeCompl) :
    r • ModuleCat.Tilde.const M m r U hr = ModuleCat.Tilde.toOpen M U m := by
  apply Subtype.ext
  funext x
  change r • LocalizedModule.mk m ⟨r, hr x.val x.property⟩ =
    LocalizedModule.mkLinearMap x.val.asIdeal.primeCompl M m
  rw [LocalizedModule.smul'_mk, LocalizedModule.mkLinearMap_apply]
  exact LocalizedModule.mk_eq.mpr ⟨1, by simp [Submonoid.smul_def]⟩

/-- Every actual tilde section has a fraction presentation on a basic-open neighborhood. -/
theorem exists_const_basicOpen (U : Opens (PrimeSpectrum R))
    (s : M.tildeInModuleCat.obj (op U)) (x : U) :
    ∃ (g : R) (m : M) (h : PrimeSpectrum.basicOpen g ≤ U),
      x.val ∈ PrimeSpectrum.basicOpen g ∧
        ModuleCat.Tilde.const M m g (PrimeSpectrum.basicOpen g) (fun _ hy => hy) =
          M.tildeInModuleCat.map (homOfLE h).op s := by
  obtain ⟨V, hxV, iVU, m, d, hd, hs⟩ := ModuleCat.Tilde.exists_const M U s x.val x.property
  obtain ⟨_, ⟨h, rfl⟩, hxh, hhV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxV V.isOpen
  let j : PrimeSpectrum.basicOpen (h * d) ≤ V :=
    ((PrimeSpectrum.basicOpen_mul h d).trans_le inf_le_left).trans hhV
  refine ⟨h * d, h • m, j.trans iVU.le, ?_, ?_⟩
  · rw [PrimeSpectrum.basicOpen_mul]
    exact ⟨hxh, hd x.val hxV⟩
  · apply Subtype.ext
    funext y
    have hyV : y.val ∈ V := j y.property
    have e := congrArg (fun t : M.tildeInModuleCat.obj (op V) => t.val ⟨y.val, hyV⟩) hs
    change LocalizedModule.mk m ⟨d, hd y.val hyV⟩ = s.val ⟨y.val, _⟩ at e
    change LocalizedModule.mk (h • m) ⟨h * d, y.property⟩ = s.val ⟨y.val, _⟩
    refine (LocalizedModule.mk_eq.mpr ⟨1, ?_⟩).trans e
    simp only [Submonoid.smul_def, Subtype.coe_mk, one_smul, ← mul_smul, mul_comm]

end KltDP.Geometry.AffineModuleTilde

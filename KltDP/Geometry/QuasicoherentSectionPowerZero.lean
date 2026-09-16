/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

The quasi-compact finite-cover argument adapts the structure-sheaf proof
in pinned Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b,
AlgebraicGeometry/Morphisms/QuasiCompact.lean:266-312, to original
quasicoherent module sections. The affine transport uses the project's
accepted original section equivalences and denominator theorem. The
corresponding modern Mazur affine theorem and its exact pin are recorded
in SECTION_EXTENSION_NEWER_REUSE.json; its newer restriction API is not imported.
-/
import KltDP.Geometry.AffineOpenModuleDenominators
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Uniform powers detect zero in original quasicoherent sections

An original quasicoherent module section that vanishes on the intrinsic
basic open D(f) is killed by a power of the original function f when its
domain is quasi-compact. On an affine open, the accepted original
Spec-section equivalences transport the proved localization zero law.
A finite affine cover and a maximum of the local exponents then give a
single exponent on the original quasi-compact open.

No local annihilating powers, extension sections, localization statement,
affine presentation or finite cover is an input to these conclusions.
This proves the zero-detection step used to glue extensions after clearing
denominators. It does not yet extend arbitrary sections after tensoring
with powers of a nontrivial invertible sheaf. Quasicoherence is explicit;
the project's general literal-coherence-to-quasicoherence bridge is separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.SchemeModuleRestriction KltDP.Geometry.AffineModuleTilde
open KltDP.Geometry.AffineOpenModule

universe u

namespace KltDP.Geometry.QuasicoherentSectionPowerZero

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]

local instance originalSectionModule (V : X.Opens) :
    Module Γ(X, V) (M.val.presheaf.obj (op V)) :=
  (M.val.obj (op V)).isModule

/-- The original semilinear restrictions compose on their original carriers. -/
private theorem restrict_comp {U V W : X.Opens} (hVU : V ≤ U) (hWV : W ≤ V)
    (s : M.val.obj (op U)) :
    M.val.map (homOfLE hWV).op (M.val.map (homOfLE hVU).op s) =
      M.val.map (homOfLE (hWV.trans hVU)).op s := by
  change (M.val.presheaf.map (homOfLE hVU).op ≫
    M.val.presheaf.map (homOfLE hWV).op) s = _
  rw [← CategoryTheory.Functor.map_comp]
  rfl

/-- Zero on an intrinsic basic open is detected by an actual power of
the original coefficient on the original affine open. -/
theorem exists_pow_smul_eq_zero_of_isAffineOpen
    {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) (t : M.val.obj (op U))
    (ht : M.val.map (homOfLE (X.basicOpen_le f)).op t = 0) :
    ∃ n : ℕ, f ^ n • t = 0 := by
  let N := (restriction hU.fromSpec).obj M
  let eTop := sectionsOfImageEq hU.fromSpec M ⊤ U (fromSpec_image_top hU)
  let eBasic := sectionsOfImageEq hU.fromSpec M (PrimeSpectrum.basicOpen f)
    (X.basicOpen f) (hU.fromSpec_image_basicOpen f)
  have hzero : N.val.map (homOfLE (show PrimeSpectrum.basicOpen f ≤ ⊤ from le_top)).op
      (eTop.symm t) = 0 := by
    apply eBasic.injective
    rw [map_zero]
    calc
      eBasic (N.val.map (homOfLE (show PrimeSpectrum.basicOpen f ≤ ⊤ from le_top)).op
          (eTop.symm t)) =
        M.val.map (homOfLE (X.basicOpen_le f)).op (eTop (eTop.symm t)) :=
        sectionsOfImageEq_naturality hU.fromSpec M (fromSpec_image_top hU)
          (hU.fromSpec_image_basicOpen f) le_top (X.basicOpen_le f) (eTop.symm t)
      _ = 0 := by rw [AddEquiv.apply_symm_apply, ht]
  obtain ⟨n, hn⟩ :=
    (denominatorExtension_of_isQuasicoherent N).uniqueness f le_top (eTop.symm t) hzero
  refine ⟨n, ?_⟩
  calc
    f ^ n • t = X.presheaf.map (homOfLE (show U ≤ U from le_rfl)).op (f ^ n) •
        eTop (eTop.symm t) := by
      rw [AddEquiv.apply_symm_apply]
      change f ^ n • t = X.presheaf.map (𝟙 (op U)) (f ^ n) • t
      rw [CategoryTheory.Functor.map_id]
      rfl
    _ = eTop (f ^ n • (show sectionModule N ⊤ from eTop.symm t)) :=
      (sectionsOfImageEq_base_smul hU M ⊤ U (fromSpec_image_top hU) le_rfl
        (f ^ n) (eTop.symm t)).symm
    _ = eTop 0 := congrArg eTop hn
    _ = 0 := map_zero eTop

/-- A single power detects zero over any original quasi-compact open.
The finite affine cover and all local powers are derived. -/
theorem exists_pow_smul_eq_zero_of_isCompact
    {U : X.Opens} (hU : IsCompact (U : Set X)) (f : Γ(X, U))
    (t : M.val.obj (op U))
    (ht : M.val.map (homOfLE (X.basicOpen_le f)).op t = 0) :
    ∃ n : ℕ, f ^ n • t = 0 := by
  classical
  obtain ⟨S, hS, hcover⟩ :=
    (isCompactOpen_iff_eq_finset_affine_union (U : Set X)).mp ⟨hU, U.2⟩
  replace hcover : U = ⨆ i : S, (i : X.Opens) := by
    ext1
    simpa using hcover
  have hle (i : S) : (i : X.Opens) ≤ U := by
    rw [hcover]
    exact le_iSup (fun j : S => (j : X.Opens)) i
  have hlocal (i : S) : ∃ n : ℕ,
      (X.presheaf.map (homOfLE (hle i)).op f) ^ n •
        M.val.map (homOfLE (hle i)).op t = 0 := by
    apply exists_pow_smul_eq_zero_of_isAffineOpen M i.1.2
    have hb : X.basicOpen (X.presheaf.map (homOfLE (hle i)).op f) ≤ X.basicOpen f := by
      rw [Scheme.basicOpen_res]
      exact inf_le_right
    calc
      M.val.map (homOfLE (X.basicOpen_le (X.presheaf.map (homOfLE (hle i)).op f))).op
          (M.val.map (homOfLE (hle i)).op t) =
        M.val.map (homOfLE hb).op (M.val.map (homOfLE (X.basicOpen_le f)).op t) := by
        rw [restrict_comp, restrict_comp]
      _ = 0 := by rw [ht, map_zero]
  choose n hn using hlocal
  letI : Finite S := hS.to_subtype
  letI : Fintype S := Fintype.ofFinite S
  let N := Finset.univ.sup n
  refine ⟨N, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq'
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M)
    (fun i : S => (i : X.Opens)) U (fun i => homOfLE (hle i)) (le_of_eq hcover)
  intro i
  change M.val.map (homOfLE (hle i)).op (f ^ N • t) =
    M.val.map (homOfLE (hle i)).op 0
  rw [M.val.map_smul, map_zero, map_pow]
  change (X.presheaf.map (homOfLE (hle i)).op f) ^ N •
    M.val.map (homOfLE (hle i)).op t = 0
  have hnN : n i ≤ N := Finset.le_sup (f := n) (Finset.mem_univ i)
  have hN : N = (N - n i) + n i := (Nat.sub_add_cancel hnN).symm
  rw [hN, pow_add, mul_smul, hn i, smul_zero]

/-- Equality after restriction to D(f) becomes equality after one power
on the original quasi-compact domain; this is the overlap gluing form. -/
theorem exists_pow_smul_eq_of_isCompact
    {U : X.Opens} (hU : IsCompact (U : Set X)) (f : Γ(X, U))
    (s t : M.val.obj (op U))
    (hst : M.val.map (homOfLE (X.basicOpen_le f)).op s =
      M.val.map (homOfLE (X.basicOpen_le f)).op t) :
    ∃ n : ℕ, f ^ n • s = f ^ n • t := by
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isCompact M hU f (s - t)
    (by rw [map_sub, hst, sub_self])
  exact ⟨n, sub_eq_zero.mp (by simpa only [smul_sub] using hn)⟩

end KltDP.Geometry.QuasicoherentSectionPowerZero

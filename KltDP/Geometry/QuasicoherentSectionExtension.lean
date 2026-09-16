/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel,
  Jujian Zhang, Weihong Xu, Andrew Yang, Brian Nugent

The finite-maxima and original-sheaf gluing argument adapts the accepted
AffineModuleDenominatorDescent.lean proof to intrinsic affine opens.
Pinned Mathlib QuasiSeparated.lean supplies the structure-sheaf QCQS
extension model. Exact reuse pins and source hashes are recorded in
SECTION_EXTENSION_REUSE.md; no newer restriction API is imported.
-/
import KltDP.Geometry.QuasicoherentSectionPowerZero
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Extension of original quasicoherent sections on a QCQS open

An actual section over the intrinsic nonvanishing open D(f) of a function
on a quasi-compact, quasi-separated open extends to the original module
after multiplication by a power of f. The finite affine cover, local
extensions, uniform exponents and gluing section are all constructed.

This is the global-function case of section extension. Quasicoherence
is explicit. The literal-coherent-to-quasicoherent bridge, extension
after powers of a nontrivial invertible sheaf, and construction of a
Serre-ample sheaf from projectivity remain separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.AffineOpenModule
open KltDP.Geometry.QuasicoherentSectionPowerZero

universe u

namespace KltDP.Geometry.QuasicoherentSectionExtension

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} (M : X.Modules)

local instance originalSectionModule (V : X.Opens) :
    Module Γ(X, V) (M.val.presheaf.obj (op V)) :=
  (M.val.obj (op V)).isModule

private abbrev res {U V : X.Opens} (hVU : V ≤ U) :=
  M.val.map (homOfLE hVU).op

private abbrev scalar {U V : X.Opens} (hVU : V ≤ U) (f : Γ(X, U))
    (s : M.val.obj (op V)) :=
  X.presheaf.map (homOfLE hVU).op f • s

private theorem res_comp {U V W : X.Opens} (hVU : V ≤ U) (hWV : W ≤ V)
    (s : M.val.obj (op U)) :
    res M hWV (res M hVU s) = res M (hWV.trans hVU) s := by
  change (M.val.presheaf.map (homOfLE hVU).op ≫
    M.val.presheaf.map (homOfLE hWV).op) s = _
  rw [← CategoryTheory.Functor.map_comp]
  rfl

private theorem ring_res_comp {U V W : X.Opens} (hVU : V ≤ U) (hWV : W ≤ V)
    (f : Γ(X, U)) :
    X.presheaf.map (homOfLE hWV).op (X.presheaf.map (homOfLE hVU).op f) =
      X.presheaf.map (homOfLE (hWV.trans hVU)).op f := by
  change (X.presheaf.map (homOfLE hVU).op ≫
    X.presheaf.map (homOfLE hWV).op) f = _
  rw [← CategoryTheory.Functor.map_comp]
  rfl

private theorem res_scalar {U V W : X.Opens} (hVU : V ≤ U) (hWV : W ≤ V)
    (f : Γ(X, U)) (s : M.val.obj (op V)) :
    res M hWV (scalar M hVU f s) =
      scalar M (hWV.trans hVU) f (res M hWV s) := by
  rw [scalar, res, M.val.map_smul]
  change X.presheaf.map (homOfLE hWV).op
      (X.presheaf.map (homOfLE hVU).op f) • res M hWV s = _
  rw [ring_res_comp]

private theorem scalar_pow_add {U V : X.Opens} (hVU : V ≤ U)
    (f : Γ(X, U)) (a b : ℕ) (s : M.val.obj (op V)) :
    scalar M hVU (f ^ a) (scalar M hVU (f ^ b) s) =
      scalar M hVU (f ^ (a + b)) s := by
  dsimp only [scalar]
  rw [pow_add, map_mul, mul_smul]

set_option maxHeartbeats 800000 in
/-- An original section on D(f) extends after an actual power of f over
any quasi-compact, quasi-separated original open. All local extension
and overlap data are derived from quasicoherence and the sheaf condition. -/
theorem exists_restrict_eq_pow_smul_of_qcqs [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsCompact (U : Set X))
    (hUqs : IsQuasiSeparated (U : Set X)) (f : Γ(X, U))
    (s : M.val.obj (op (X.basicOpen f))) :
    ∃ (n : ℕ) (t : M.val.obj (op U)),
      M.val.map (homOfLE (X.basicOpen_le f)).op t =
        X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • s := by
  classical
  obtain ⟨S, hS, hcover⟩ :=
    (isCompactOpen_iff_eq_finset_affine_union (U : Set X)).mp ⟨hU, U.2⟩
  replace hcover : U = ⨆ i : S, (i : X.Opens) := by
    ext1
    simpa using hcover
  letI : Finite S := hS.to_subtype
  letI : Fintype S := Fintype.ofFinite S
  have hle (i : S) : (i : X.Opens) ≤ U := by
    rw [hcover]
    exact le_iSup (fun j : S => (j : X.Opens)) i
  let fi (i : S) : Γ(X, (i : X.Opens)) :=
    X.presheaf.map (homOfLE (hle i)).op f
  let Di (i : S) : X.Opens := X.basicOpen (fi i)
  have hDi (i : S) : Di i ≤ (i : X.Opens) := X.basicOpen_le (fi i)
  have hDiD (i : S) : Di i ≤ X.basicOpen f := by
    dsimp only [Di, fi]
    rw [Scheme.basicOpen_res]
    exact inf_le_right
  let si (i : S) : M.val.obj (op (Di i)) := res M (hDiD i) s
  have hlocal (i : S) : ∃ (n : ℕ) (t : M.val.obj (op (i : X.Opens))),
      res M (hDi i) t = scalar M ((hDi i).trans (hle i)) (f ^ n) (si i) := by
    obtain ⟨n, t, ht⟩ := exists_restrict_eq_pow_smul i.1.2 M (fi i) (si i)
    refine ⟨n, t, ?_⟩
    calc
      res M (hDi i) t = X.presheaf.map (homOfLE (hDi i)).op ((fi i) ^ n) •
          si i := ht
      _ = scalar M ((hDi i).trans (hle i)) (f ^ n) (si i) := by
        dsimp only [fi, scalar]
        rw [← map_pow, ring_res_comp]
  choose n y hy using hlocal
  let N : ℕ := Finset.univ.sup n
  have hnN (i : S) : n i ≤ N := Finset.le_sup (f := n) (Finset.mem_univ i)
  let t (i : S) : M.val.obj (op (i : X.Opens)) :=
    scalar M (hle i) (f ^ (N - n i)) (y i)
  have ht (i : S) : res M (hDi i) (t i) =
      scalar M ((hDi i).trans (hle i)) (f ^ N) (si i) := by
    dsimp only [t]
    rw [res_scalar, hy, scalar_pow_add, Nat.sub_add_cancel (hnN i)]
  have hpairs (i j : S) : ∃ m : ℕ,
      res M (show (i : X.Opens) ⊓ (j : X.Opens) ≤ (i : X.Opens) from inf_le_left)
          (scalar M (hle i) (f ^ m) (t i)) =
        res M (show (i : X.Opens) ⊓ (j : X.Opens) ≤ (j : X.Opens) from inf_le_right)
          (scalar M (hle j) (f ^ m) (t j)) := by
    let V : X.Opens := (i : X.Opens) ⊓ (j : X.Opens)
    have hVi : V ≤ (i : X.Opens) := inf_le_left
    have hVj : V ≤ (j : X.Opens) := inf_le_right
    have hVU : V ≤ U := hVi.trans (hle i)
    have hVcompact : IsCompact (V : Set X) :=
      hUqs _ _ (hle i) i.1.1.2 i.1.2.isCompact
        (hle j) j.1.1.2 j.1.2.isCompact
    let fV : Γ(X, V) := X.presheaf.map (homOfLE hVU).op f
    have hBi : X.basicOpen fV ≤ Di i := by
      dsimp only [fV, Di, fi]
      rw [Scheme.basicOpen_res, Scheme.basicOpen_res]
      exact inf_le_inf hVi le_rfl
    have hBj : X.basicOpen fV ≤ Di j := by
      dsimp only [fV, Di, fi]
      rw [Scheme.basicOpen_res, Scheme.basicOpen_res]
      exact inf_le_inf hVj le_rfl
    let ui : M.val.obj (op V) := res M hVi (t i)
    let uj : M.val.obj (op V) := res M hVj (t j)
    have heq : res M (X.basicOpen_le fV) ui = res M (X.basicOpen_le fV) uj := by
      calc
        res M (X.basicOpen_le fV) ui = res M hBi (res M (hDi i) (t i)) := by
          dsimp only [ui]
          rw [res_comp, res_comp]
        _ = scalar M ((X.basicOpen_le fV).trans hVU) (f ^ N)
            (res M hBi (si i)) := by rw [ht, res_scalar]
        _ = scalar M ((X.basicOpen_le fV).trans hVU) (f ^ N)
            (res M hBj (si j)) := by
          dsimp only [si]
          rw [res_comp, res_comp]
        _ = res M hBj (res M (hDi j) (t j)) := by rw [ht, res_scalar]
        _ = res M (X.basicOpen_le fV) uj := by
          dsimp only [uj]
          rw [res_comp, res_comp]
    obtain ⟨m, hm⟩ := exists_pow_smul_eq_of_isCompact M hVcompact fV ui uj heq
    refine ⟨m, ?_⟩
    calc
      res M hVi (scalar M (hle i) (f ^ m) (t i)) =
          scalar M hVU (f ^ m) ui := res_scalar M (hle i) hVi (f ^ m) (t i)
      _ = scalar M hVU (f ^ m) uj := by
        dsimp only [scalar]
        rw [map_pow]
        exact hm
      _ = res M hVj (scalar M (hle j) (f ^ m) (t j)) :=
        (res_scalar M (hle j) hVj (f ^ m) (t j)).symm
  choose k hk using hpairs
  let K : ℕ := Finset.univ.sup (fun q : S × S => k q.1 q.2)
  have hkK (i j : S) : k i j ≤ K :=
    Finset.le_sup (f := fun q : S × S => k q.1 q.2) (Finset.mem_univ (i, j))
  have hK (i j : S) :
      res M (show (i : X.Opens) ⊓ (j : X.Opens) ≤ (i : X.Opens) from inf_le_left)
          (scalar M (hle i) (f ^ K) (t i)) =
        res M (show (i : X.Opens) ⊓ (j : X.Opens) ≤ (j : X.Opens) from inf_le_right)
          (scalar M (hle j) (f ^ K) (t j)) := by
    have h := congrArg
      (fun z : M.val.obj (op ((i : X.Opens) ⊓ (j : X.Opens))) =>
        scalar M (inf_le_left.trans (hle i)) (f ^ (K - k i j)) z) (hk i j)
    simpa only [res_scalar, scalar_pow_add, Nat.sub_add_cancel (hkK i j)] using h
  obtain ⟨a, ha, _⟩ := TopCat.Sheaf.existsUnique_gluing'
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M)
    (fun i : S => (i : X.Opens)) U (fun i => homOfLE (hle i)) (le_of_eq hcover)
    (fun i => scalar M (hle i) (f ^ K) (t i)) (by
      intro i j
      exact hK i j)
  refine ⟨K + N, a, ?_⟩
  have hcoverD : X.basicOpen f ≤ ⨆ i : S, Di i := by
    intro x hx
    have hxU : x ∈ U := X.basicOpen_le f hx
    rw [hcover] at hxU
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxU
    refine Opens.mem_iSup.mpr ⟨i, ?_⟩
    dsimp only [Di, fi]
    rw [Scheme.basicOpen_res]
    exact ⟨hi, hx⟩
  apply TopCat.Sheaf.eq_of_locally_eq'
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M)
    Di (X.basicOpen f) (fun i => homOfLE (hDiD i)) hcoverD
  intro i
  change res M (hDiD i) (res M (X.basicOpen_le f) a) =
    res M (hDiD i) (scalar M (X.basicOpen_le f) (f ^ (K + N)) s)
  have hai : res M (hle i) a = scalar M (hle i) (f ^ K) (t i) := ha i
  calc
    res M (hDiD i) (res M (X.basicOpen_le f) a) =
        res M (hDi i) (res M (hle i) a) := by rw [res_comp, res_comp]
    _ = res M (hDi i) (scalar M (hle i) (f ^ K) (t i)) :=
      congrArg (res M (hDi i)) hai
    _ = scalar M ((hDi i).trans (hle i)) (f ^ K) (res M (hDi i) (t i)) :=
      res_scalar M (hle i) (hDi i) (f ^ K) (t i)
    _ = scalar M ((hDi i).trans (hle i)) (f ^ (K + N)) (si i) := by
      rw [ht, scalar_pow_add]
    _ = res M (hDiD i) (scalar M (X.basicOpen_le f) (f ^ (K + N)) s) :=
      (res_scalar M (X.basicOpen_le f) (hDiD i) (f ^ (K + N)) s).symm

end KltDP.Geometry.QuasicoherentSectionExtension

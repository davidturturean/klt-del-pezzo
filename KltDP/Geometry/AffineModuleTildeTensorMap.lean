/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

Adapted from the proved fractional-section tensor construction in
MazurTorsion/Upstream/DivisorLineBundle.lean, revision
9327963d4ec14fba49c7b14b004fd00707ffc2e9, lines 292–479.
The pinned tilde uses denominator equations rather than fraction equalities;
the existing KltDP principal-open localization theorem supplies that part.
-/
import KltDP.RingTheory.LocalizedTensorProduct
import KltDP.Geometry.AffineModuleTildeLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# The canonical tensor map on the original affine tilde presheaves

Pointwise tensoring the actual localized module fibers preserves the
original locally fractional sections. The resulting natural presheaf map
is bijective on every principal open. This file does not assert that the
pointwise presheaf tensor is already a sheaf.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace KltDP.Geometry.AffineModuleTildeTensor

variable {R : Type u} [CommRing R] (M N : ModuleCat.{u} R)

/-- The original module tensor, bundled only for the pinned tilde functor. -/
abbrev tensorModule : ModuleCat.{u} R := ModuleCat.of R (_root_.TensorProduct R M N)

/-- The actual sectionwise tensor of the two original tilde presheaves. -/
abbrev tensorPresheaf : PresheafOfModules (Spec (CommRingCat.of R)).ringCatSheaf.val :=
  PresheafOfModules.Monoidal.tensorObj (R := (Spec (CommRingCat.of R)).sheaf.val)
    M.tilde.val N.tilde.val

local instance sectionAlgebra (U : (Spec (CommRingCat.of R)).Opens) :
    Algebra R Γ(Spec (CommRingCat.of R), U) :=
  StructureSheaf.openAlgebra R (op U)

local instance sectionBaseModule (P : ModuleCat.{u} R)
    (U : (Spec (CommRingCat.of R)).Opens) : Module R (P.tilde.val.obj (op U)) :=
  (P.tildeInModuleCat.obj (op U)).isModule

local instance sectionRingModule (P : ModuleCat.{u} R)
    (U : (Spec (CommRingCat.of R)).Opens) :
    Module ((Spec.structureSheaf R).val.obj (op U)) (P.tildeInModuleCat.obj (op U)) :=
  (P.tilde.val.obj (op U)).isModule

local instance sectionScalarTower (P : ModuleCat.{u} R)
    (U : (Spec (CommRingCat.of R)).Opens) :
    IsScalarTower R Γ(Spec (CommRingCat.of R), U) (P.tilde.val.obj (op U)) :=
  IsScalarTower.of_algebraMap_smul (fun r s => AffineModuleTilde.toOpen_scalar_smul P U r s)

local instance basicOpenLocalization (f : R) :
    IsLocalization (Submonoid.powers f)
      Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f) :=
  StructureSheaf.IsLocalization.to_basicOpen R f

/-- The tensor of actual fractional sections, with their original localized fibers. -/
def sectionsPure (U : (Spec (CommRingCat.of R)).Opens)
    (a : M.tilde.val.obj (op U)) (b : N.tilde.val.obj (op U)) :
    (tensorModule M N).tilde.val.obj (op U) :=
  ⟨fun x => KltDP.RingTheory.LocalizedTensorProduct.equiv x.val.asIdeal.primeCompl M N
      (Localization.AtPrime x.val.asIdeal)
      (a.val x ⊗ₜ[Localization.AtPrime x.val.asIdeal] b.val x), by
    intro x
    obtain ⟨Va, hxa, ia, ma, sa, wa⟩ := a.property x
    obtain ⟨Vb, hxb, ib, mb, sb, wb⟩ := b.property x
    refine ⟨Va ⊓ Vb, ⟨hxa, hxb⟩, Opens.infLELeft _ _ ≫ ia,
      ma ⊗ₜ[R] mb, sa * sb, fun y => ?_⟩
    obtain ⟨hsa, ha⟩ := wa (Opens.infLELeft _ _ y : Va)
    obtain ⟨hsb, hb⟩ := wb (Opens.infLERight _ _ y : Vb)
    refine ⟨y.val.asIdeal.primeCompl.mul_mem hsa hsb, ?_⟩
    have hpair :
        (sa * sb) • (a.val (ia (Opens.infLELeft _ _ y))
          ⊗ₜ[Localization.AtPrime y.val.asIdeal] b.val (ib (Opens.infLERight _ _ y))) =
        (sa • a.val (ia (Opens.infLELeft _ _ y)))
          ⊗ₜ[Localization.AtPrime y.val.asIdeal]
            (sb • b.val (ib (Opens.infLERight _ _ y))) := by
      change ((sa * sb) • a.val (ia (Opens.infLELeft _ _ y)))
        ⊗ₜ[Localization.AtPrime y.val.asIdeal] b.val (ib (Opens.infLERight _ _ y)) = _
      rw [mul_smul, smul_comm sa sb, TensorProduct.smul_tmul]
    change (sa * sb) • KltDP.RingTheory.LocalizedTensorProduct.equiv
      y.val.asIdeal.primeCompl M N (Localization.AtPrime y.val.asIdeal)
      (a.val (ia (Opens.infLELeft _ _ y))
        ⊗ₜ[Localization.AtPrime y.val.asIdeal] b.val (ib (Opens.infLERight _ _ y))) = _
    rw [← KltDP.RingTheory.LocalizedTensorProduct.equiv_smul, hpair, ha, hb]
    exact KltDP.RingTheory.LocalizedTensorProduct.equiv_mk_one
      y.val.asIdeal.primeCompl M N (Localization.AtPrime y.val.asIdeal) ma mb⟩

/-- The canonical bilinear map on the original open-section modules. -/
def sectionsMap (U : (Spec (CommRingCat.of R)).Opens) :
    (tensorPresheaf M N).obj (op U) ⟶ (tensorModule M N).tilde.val.obj (op U) :=
  ModuleCat.MonoidalCategory.tensorLift (sectionsPure M N U)
    (by
      intro a a' b
      apply Subtype.ext
      funext x
      change KltDP.RingTheory.LocalizedTensorProduct.equiv x.val.asIdeal.primeCompl M N
        (Localization.AtPrime x.val.asIdeal)
        ((a.val x + a'.val x) ⊗ₜ[Localization.AtPrime x.val.asIdeal] b.val x) = _
      rw [TensorProduct.add_tmul, map_add]
      rfl)
    (by
      intro r a b
      apply Subtype.ext
      funext x
      let q : Localization.AtPrime x.val.asIdeal := r.val x
      change KltDP.RingTheory.LocalizedTensorProduct.equiv x.val.asIdeal.primeCompl M N
        (Localization.AtPrime x.val.asIdeal)
        ((q • a.val x) ⊗ₜ[Localization.AtPrime x.val.asIdeal] b.val x) =
          q • KltDP.RingTheory.LocalizedTensorProduct.equiv x.val.asIdeal.primeCompl M N
            (Localization.AtPrime x.val.asIdeal)
            (a.val x ⊗ₜ[Localization.AtPrime x.val.asIdeal] b.val x)
      rw [← TensorProduct.smul_tmul']
      exact (KltDP.RingTheory.LocalizedTensorProduct.equiv x.val.asIdeal.primeCompl M N
        (Localization.AtPrime x.val.asIdeal)).map_smul q _)
    (by
      intro a b b'
      apply Subtype.ext
      funext x
      change KltDP.RingTheory.LocalizedTensorProduct.equiv x.val.asIdeal.primeCompl M N
        (Localization.AtPrime x.val.asIdeal)
        (a.val x ⊗ₜ[Localization.AtPrime x.val.asIdeal] (b.val x + b'.val x)) = _
      rw [TensorProduct.tmul_add, map_add]
      rfl)
    (by
      intro r a b
      apply Subtype.ext
      funext x
      let q : Localization.AtPrime x.val.asIdeal := r.val x
      change KltDP.RingTheory.LocalizedTensorProduct.equiv x.val.asIdeal.primeCompl M N
        (Localization.AtPrime x.val.asIdeal)
        (a.val x ⊗ₜ[Localization.AtPrime x.val.asIdeal] (q • b.val x)) =
          q • KltDP.RingTheory.LocalizedTensorProduct.equiv x.val.asIdeal.primeCompl M N
            (Localization.AtPrime x.val.asIdeal)
            (a.val x ⊗ₜ[Localization.AtPrime x.val.asIdeal] b.val x)
      rw [TensorProduct.tmul_smul]
      exact (KltDP.RingTheory.LocalizedTensorProduct.equiv x.val.asIdeal.primeCompl M N
        (Localization.AtPrime x.val.asIdeal)).map_smul q _)

/-- The original restrictions commute with the pointwise tensor map. -/
def presheafMap : tensorPresheaf M N ⟶ (tensorModule M N).tilde.val where
  app U := sectionsMap M N U.unop
  naturality {U V} i := ModuleCat.MonoidalCategory.tensor_ext (by
    intro a b
    apply Subtype.ext
    funext x
    rfl)

/-- The canonical tensor localization equivalence on an original principal open. -/
def basicOpenEquiv (f : R) :
    (M.tilde.val.obj (op (PrimeSpectrum.basicOpen f)))
        ⊗[Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f)]
      (N.tilde.val.obj (op (PrimeSpectrum.basicOpen f))) ≃ₗ[
        Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f)]
      (tensorModule M N).tilde.val.obj (op (PrimeSpectrum.basicOpen f)) := by
  letI := AffineModuleTilde.toOpen_isLocalizedModule M f
  letI := AffineModuleTilde.toOpen_isLocalizedModule N f
  letI := AffineModuleTilde.toOpen_isLocalizedModule (tensorModule M N) f
  exact (IsLocalization.moduleTensorEquiv (Submonoid.powers f)
      Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f)
      (M.tilde.val.obj (op (PrimeSpectrum.basicOpen f)))
      (N.tilde.val.obj (op (PrimeSpectrum.basicOpen f)))).trans
    (LinearEquiv.extendScalarsOfIsLocalization (Submonoid.powers f)
      Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f)
      (IsLocalizedModule.linearEquiv (Submonoid.powers f)
        (TensorProduct.map (ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom
          (ModuleCat.Tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom)
        (ModuleCat.Tilde.toOpen (tensorModule M N) (PrimeSpectrum.basicOpen f)).hom))

theorem basicOpenEquiv_toOpen (f : R) (m : M) (n : N) :
    basicOpenEquiv M N f
      (ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen f) m
        ⊗ₜ[Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f)]
          ModuleCat.Tilde.toOpen N (PrimeSpectrum.basicOpen f) n) =
      ModuleCat.Tilde.toOpen (tensorModule M N) (PrimeSpectrum.basicOpen f) (m ⊗ₜ[R] n) := by
  letI := AffineModuleTilde.toOpen_isLocalizedModule M f
  letI := AffineModuleTilde.toOpen_isLocalizedModule N f
  letI := AffineModuleTilde.toOpen_isLocalizedModule (tensorModule M N) f
  change (IsLocalizedModule.linearEquiv (Submonoid.powers f)
      (TensorProduct.map (ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom
        (ModuleCat.Tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom)
      (ModuleCat.Tilde.toOpen (tensorModule M N) (PrimeSpectrum.basicOpen f)).hom)
      ((TensorProduct.map (ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom
        (ModuleCat.Tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom) (m ⊗ₜ[R] n)) = _
  exact IsLocalizedModule.linearEquiv_apply (Submonoid.powers f) _ _ _

/-- Tensoring denominator-one sections retains their actual tensor numerator. -/
theorem sectionsPure_toOpen (U : (Spec (CommRingCat.of R)).Opens) (m : M) (n : N) :
    sectionsPure M N U (ModuleCat.Tilde.toOpen M U m) (ModuleCat.Tilde.toOpen N U n) =
      ModuleCat.Tilde.toOpen (tensorModule M N) U (m ⊗ₜ[R] n) := by
  apply Subtype.ext
  funext x
  exact KltDP.RingTheory.LocalizedTensorProduct.equiv_mk_one
    x.val.asIdeal.primeCompl M N (Localization.AtPrime x.val.asIdeal) m n

/-- The actual principal-open tensor map is the canonical localization equivalence. -/
theorem sectionsMap_basicOpen (f : R) :
    sectionsMap M N (PrimeSpectrum.basicOpen f) =
      ModuleCat.ofHom (basicOpenEquiv M N f).toLinearMap := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a b
  let A : Type u := Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f)
  letI : Module A (M.tildeInModuleCat.obj (op (PrimeSpectrum.basicOpen f))) :=
    (M.tilde.val.obj (op (PrimeSpectrum.basicOpen f))).isModule
  letI : Module A (N.tildeInModuleCat.obj (op (PrimeSpectrum.basicOpen f))) :=
    (N.tilde.val.obj (op (PrimeSpectrum.basicOpen f))).isModule
  letI : IsScalarTower R A (M.tildeInModuleCat.obj (op (PrimeSpectrum.basicOpen f))) :=
    sectionScalarTower M (PrimeSpectrum.basicOpen f)
  letI : IsScalarTower R A (N.tildeInModuleCat.obj (op (PrimeSpectrum.basicOpen f))) :=
    sectionScalarTower N (PrimeSpectrum.basicOpen f)
  let fM := (ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom
  let fN := (ModuleCat.Tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom
  obtain ⟨⟨m, s⟩, hm⟩ := IsLocalizedModule.mk'_surjective (Submonoid.powers f) fM a
  obtain ⟨⟨n, t⟩, hn⟩ := IsLocalizedModule.mk'_surjective (Submonoid.powers f) fN b
  have hm' : IsLocalizedModule.mk' fM m s = IsLocalization.mk' A 1 s • fM m := by
    rw [← IsLocalizedModule.mk'_one (Submonoid.powers f) fM m]
    symm
    simpa using IsLocalizedModule.mk'_smul_mk' A fM 1 m s 1
  have hn' : IsLocalizedModule.mk' fN n t = IsLocalization.mk' A 1 t • fN n := by
    rw [← IsLocalizedModule.mk'_one (Submonoid.powers f) fN n]
    symm
    simpa using IsLocalizedModule.mk'_smul_mk' A fN 1 n t 1
  let AS : Type u := ↑((Spec (CommRingCat.of R)).ringCatSheaf.val.obj
    (op (PrimeSpectrum.basicOpen f)))
  letI : CommRing AS := inferInstanceAs (CommRing A)
  let fm : M.tilde.val.obj (op (PrimeSpectrum.basicOpen f)) := fM m
  let fn : N.tilde.val.obj (op (PrimeSpectrum.basicOpen f)) := fN n
  let rs : AS := IsLocalization.mk' A 1 s
  let rt : AS := IsLocalization.mk' A 1 t
  have hm'' : Function.uncurry (IsLocalizedModule.mk' fM) (m, s) = rs • fm := hm'
  have hn'' : Function.uncurry (IsLocalizedModule.mk' fN) (n, t) = rt • fn := hn'
  rw [← hm, ← hn, hm'', hn'']
  have hTensor : (rs • fm) ⊗ₜ[AS] (rt • fn) =
      (rs * rt) • (fm ⊗ₜ[AS] fn) := by
    exact TensorProduct.smul_tmul_smul _ _ _ _
  erw [hTensor, map_smul, map_smul]
  have hbase : (sectionsMap M N (PrimeSpectrum.basicOpen f)).hom (fm ⊗ₜ[AS] fn) =
      basicOpenEquiv M N f (fM m ⊗ₜ[A] fN n) := by
    change sectionsPure M N (PrimeSpectrum.basicOpen f) (fM m) (fN n) =
      basicOpenEquiv M N f (fM m ⊗ₜ[A] fN n)
    rw [sectionsPure_toOpen, basicOpenEquiv_toOpen]
  exact congrArg ((rs * rt) • ·) hbase

/-- Every original principal-open component is bijective. -/
theorem sectionsMap_basicOpen_bijective (f : R) :
    Function.Bijective (sectionsMap M N (PrimeSpectrum.basicOpen f)) := by
  rw [sectionsMap_basicOpen]
  exact (basicOpenEquiv M N f).bijective

end KltDP.Geometry.AffineModuleTildeTensor

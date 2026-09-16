import KltDP.RingTheory.ConormalRestriction
import KltDP.Geometry.AffineModuleTildePullback
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Actual principal conormal and normal modules after principal localization

The regular equation remains regular and generates the actual mapped ideal.
Its existing principal frames identify the original quotient-module scalar
extensions with the actual localized conormal and normal modules. The
conormal map is the original ideal cotangent map; the normal map preserves
the original functional evaluation on every pure tensor.

The module comparisons induce isomorphisms for the actual sheaf pullback
through the existing affine tilde/pullback comparison. Equation independence
is proved from the original maps and evaluation, rather than chosen frames.

This is the module and affine-pullback part of refinement compatibility.
Matching the transported sheaf tensor/unit evaluation with these maps,
the resulting dual-comparison square, and global adjunction remain separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

namespace KltDP.Geometry.PrincipalConormalLocalization

section ScalarFrame

variable {R S : Type u} [CommRing R] [CommRing S]

private def scalarFrameIso (φ : R →+* S) (M : ModuleCat.{u} R) (e : M ≃ₗ[R] R) :
    (ModuleCat.extendScalars φ).obj M ≅ ModuleCat.of S S := by
  letI : Algebra R S := φ.toAlgebra
  exact ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) e).trans
    (TensorProduct.AlgebraTensorModule.rid R S S)).toModuleIso

private theorem scalarFrameIso_tmul (φ : R →+* S) (M : ModuleCat.{u} R)
    (e : M ≃ₗ[R] R) (s : S) (m : M) :
    (scalarFrameIso φ M e).hom (s ⊗ₜ[R,φ] m) = φ (e m) * s := rfl

end ScalarFrame

variable {A : Type u} [CommRing A] (J : Ideal A) (r : A)

/-- The original extension of the ideal to the actual principal localization. -/
abbrev localizedIdeal : Ideal (Localization.Away r) :=
  J.map (algebraMap A (Localization.Away r))

/-- The original quotient of the localization by the mapped ideal. -/
abbrev quotientRing := Localization.Away r ⧸ localizedIdeal J r

/-- The actual quotient map induced by the principal localization. -/
def quotientMap : A ⧸ J →+* quotientRing J r :=
  Ideal.quotientMap (localizedIdeal J r) (algebraMap A (Localization.Away r))
    (fun _ hx => Ideal.mem_map_of_mem _ hx)

/-- The original ideal cotangent map with its original quotient semilinearity. -/
def conormalRestriction : J.Cotangent →ₛₗ[quotientMap J r] (localizedIdeal J r).Cotangent :=
  KltDP.RingTheory.conormalMap J (localizedIdeal J r)
    (algebraMap A (Localization.Away r)) (fun _ hx => Ideal.mem_map_of_mem _ hx)

variable (d : J)

/-- The image of the original equation, as an element of the actual mapped ideal. -/
def localizedEquation : localizedIdeal J r :=
  ⟨algebraMap A (Localization.Away r) (d : A), Ideal.mem_map_of_mem _ d.property⟩

variable (hJ : Ideal.span {(d : A)} = J) (hd : (d : A) ∈ nonZeroDivisors A)

include hJ in
/-- The image equation generates the original mapped ideal. -/
theorem localizedEquation_span :
    Ideal.span {(localizedEquation J r d : Localization.Away r)} = localizedIdeal J r := by
  have h := congrArg (Ideal.map (algebraMap A (Localization.Away r))) hJ
  simpa only [Ideal.map_span, Set.image_singleton] using h

include hd in
/-- Localization preserves regularity of the original equation. -/
theorem localizedEquation_regular :
    (localizedEquation J r d : Localization.Away r) ∈ nonZeroDivisors (Localization.Away r) :=
  IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers r) (Localization.Away r) hd

private def targetConormalFrame :
    quotientRing J r ≃ₗ[quotientRing J r] (localizedIdeal J r).Cotangent :=
  KltDP.RingTheory.principalConormalEquiv (localizedIdeal J r) (localizedEquation J r d)
    (localizedEquation_span J r d hJ) (localizedEquation_regular J r d hd)

private def targetNormalFrame :
    Module.Dual (quotientRing J r) (localizedIdeal J r).Cotangent ≃ₗ[quotientRing J r]
      quotientRing J r :=
  KltDP.RingTheory.principalNormalEquiv (localizedIdeal J r) (localizedEquation J r d)
    (localizedEquation_span J r d hJ) (localizedEquation_regular J r d hd)

include d hJ hd in
private theorem conormalRestriction_coordinates (m : J.Cotangent) :
    conormalRestriction J r m = targetConormalFrame J r d hJ hd
      (quotientMap J r ((KltDP.RingTheory.principalConormalEquiv J d hJ hd).symm m)) := by
  have h := KltDP.RingTheory.conormalMap_principalConormalEquiv J (localizedIdeal J r)
    (algebraMap A (Localization.Away r)) (fun _ hx => Ideal.mem_map_of_mem _ hx)
    d hJ hd (localizedEquation J r d) (localizedEquation_span J r d hJ)
    (localizedEquation_regular J r d hd) 1 (by simp only [localizedEquation, one_mul])
    ((KltDP.RingTheory.principalConormalEquiv J d hJ hd).symm m)
  simpa only [LinearEquiv.apply_symm_apply, map_one, mul_one] using h

private theorem principalFrame_evaluation (m : J.Cotangent)
    (ℓ : Module.Dual (A ⧸ J) J.Cotangent) :
    ℓ m = (KltDP.RingTheory.principalConormalEquiv J d hJ hd).symm m *
      KltDP.RingTheory.principalNormalEquiv J d hJ hd ℓ := by
  let e := KltDP.RingTheory.principalConormalEquiv J d hJ hd
  calc
    ℓ m = ℓ (e (e.symm m)) := congrArg ℓ (e.apply_symm_apply m).symm
    _ = e.symm m * KltDP.RingTheory.principalNormalEquiv J d hJ hd ℓ := by
      have he1 : e 1 = J.toCotangent d :=
        KltDP.RingTheory.principalConormalEquiv_one J d hJ hd
      have heq : e (e.symm m) = e.symm m • J.toCotangent d := by
        simpa only [smul_eq_mul, mul_one, he1] using e.map_smul (e.symm m) (1 : A ⧸ J)
      simp only [heq, map_smul, KltDP.RingTheory.principalNormalEquiv_apply, smul_eq_mul]

private theorem normalFrame_symm_evaluation (q c : A ⧸ J) :
    (KltDP.RingTheory.principalNormalEquiv J d hJ hd).symm c
        (KltDP.RingTheory.principalConormalEquiv J d hJ hd q) = q * c := by
  have h := principalFrame_evaluation J d hJ hd
    (KltDP.RingTheory.principalConormalEquiv J d hJ hd q)
    ((KltDP.RingTheory.principalNormalEquiv J d hJ hd).symm c)
  simpa only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply] using h

/-- Original scalar extension of the conormal is the actual localized conormal module. -/
def conormalModuleIso :
    (ModuleCat.extendScalars (quotientMap J r)).obj (ModuleCat.of (A ⧸ J) J.Cotangent) ≅
      ModuleCat.of (quotientRing J r) (localizedIdeal J r).Cotangent :=
  scalarFrameIso (quotientMap J r) (ModuleCat.of (A ⧸ J) J.Cotangent)
    (KltDP.RingTheory.principalConormalEquiv J d hJ hd).symm ≪≫
      (targetConormalFrame J r d hJ hd).toModuleIso

/-- The produced comparison is the scalar extension of the original ideal cotangent map. -/
theorem conormalModuleIso_tmul (s : quotientRing J r) (m : J.Cotangent) :
    (conormalModuleIso J r d hJ hd).hom (s ⊗ₜ[A ⧸ J,quotientMap J r] m) =
      s • conormalRestriction J r m := by
  change targetConormalFrame J r d hJ hd
    ((scalarFrameIso (quotientMap J r) (ModuleCat.of (A ⧸ J) J.Cotangent)
      (KltDP.RingTheory.principalConormalEquiv J d hJ hd).symm).hom _) = _
  rw [scalarFrameIso_tmul, conormalRestriction_coordinates J r d hJ hd, ← map_smul]
  exact congrArg (targetConormalFrame J r d hJ hd) (mul_comm _ _)

/-- Original scalar extension of the normal module is the actual localized module dual. -/
def normalModuleIso :
    (ModuleCat.extendScalars (quotientMap J r)).obj
        (ModuleCat.of (A ⧸ J) (Module.Dual (A ⧸ J) J.Cotangent)) ≅
      ModuleCat.of (quotientRing J r)
        (Module.Dual (quotientRing J r) (localizedIdeal J r).Cotangent) :=
  scalarFrameIso (quotientMap J r)
    (ModuleCat.of (A ⧸ J) (Module.Dual (A ⧸ J) J.Cotangent))
    (KltDP.RingTheory.principalNormalEquiv J d hJ hd) ≪≫
      (targetNormalFrame J r d hJ hd).symm.toModuleIso

/-- Original evaluation is preserved under principal localization, including every scalar. -/
theorem normalModuleIso_evaluation (s : quotientRing J r)
    (ℓ : Module.Dual (A ⧸ J) J.Cotangent) (m : J.Cotangent) :
    (normalModuleIso J r d hJ hd).hom (s ⊗ₜ[A ⧸ J,quotientMap J r] ℓ)
        (conormalRestriction J r m) = s * quotientMap J r (ℓ m) := by
  change (targetNormalFrame J r d hJ hd).symm
    ((scalarFrameIso (quotientMap J r)
      (ModuleCat.of (A ⧸ J) (Module.Dual (A ⧸ J) J.Cotangent))
      (KltDP.RingTheory.principalNormalEquiv J d hJ hd)).hom _)
    (conormalRestriction J r m) = _
  rw [scalarFrameIso_tmul, conormalRestriction_coordinates J r d hJ hd]
  unfold targetNormalFrame targetConormalFrame
  rw [normalFrame_symm_evaluation, principalFrame_evaluation J d hJ hd m ℓ, map_mul]
  exact (mul_assoc _ _ _).symm.trans (mul_comm _ _)

/-- The conormal scalar-extension map is independent of the regular equation. -/
theorem conormalModuleIso_eq (e : J) (hE : Ideal.span {(e : A)} = J)
    (he : (e : A) ∈ nonZeroDivisors A) :
    conormalModuleIso J r e hE he = conormalModuleIso J r d hJ hd := by
  apply Iso.ext
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  rw [conormalModuleIso_tmul, conormalModuleIso_tmul]

/-- Original evaluation determines the normal scalar-extension map independently of the equation. -/
theorem normalModuleIso_eq (e : J) (hE : Ideal.span {(e : A)} = J)
    (he : (e : A) ∈ nonZeroDivisors A) :
    normalModuleIso J r e hE he = normalModuleIso J r d hJ hd := by
  apply Iso.ext
  apply ModuleCat.ExtendScalars.hom_ext
  intro ℓ
  apply (targetNormalFrame J r d hJ hd).injective
  simp only [targetNormalFrame, KltDP.RingTheory.principalNormalEquiv_apply]
  change (normalModuleIso J r e hE he).hom
      ((1 : quotientRing J r) ⊗ₜ[A ⧸ J,quotientMap J r] ℓ)
      (conormalRestriction J r (J.toCotangent d)) =
    (normalModuleIso J r d hJ hd).hom
      ((1 : quotientRing J r) ⊗ₜ[A ⧸ J,quotientMap J r] ℓ)
      (conormalRestriction J r (J.toCotangent d))
  rw [normalModuleIso_evaluation, normalModuleIso_evaluation]

/-- Actual sheaf pullback of the original conormal tilde is the localized conormal tilde. -/
def conormalTildePullbackIso :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom (quotientMap J r)))).obj
        (ModuleCat.of (A ⧸ J) J.Cotangent).tilde ≅
      (ModuleCat.of (quotientRing J r) (localizedIdeal J r).Cotangent).tilde :=
  AffineModuleTilde.pullbackIso (quotientMap J r) (ModuleCat.of (A ⧸ J) J.Cotangent) ≪≫
    AffineModuleTilde.mapIso (conormalModuleIso J r d hJ hd)

/-- Actual sheaf pullback of the original normal tilde is the localized normal tilde. -/
def normalTildePullbackIso :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom (quotientMap J r)))).obj
        (ModuleCat.of (A ⧸ J) (Module.Dual (A ⧸ J) J.Cotangent)).tilde ≅
      (ModuleCat.of (quotientRing J r)
        (Module.Dual (quotientRing J r) (localizedIdeal J r).Cotangent)).tilde :=
  AffineModuleTilde.pullbackIso (quotientMap J r)
      (ModuleCat.of (A ⧸ J) (Module.Dual (A ⧸ J) J.Cotangent)) ≪≫
    AffineModuleTilde.mapIso (normalModuleIso J r d hJ hd)

/-- Equation independence persists for the actual conormal sheaf pullback. -/
theorem conormalTildePullbackIso_eq (e : J) (hE : Ideal.span {(e : A)} = J)
    (he : (e : A) ∈ nonZeroDivisors A) :
    conormalTildePullbackIso J r e hE he = conormalTildePullbackIso J r d hJ hd := by
  unfold conormalTildePullbackIso
  rw [conormalModuleIso_eq J r d hJ hd e hE he]

/-- Equation independence persists for the actual normal sheaf pullback. -/
theorem normalTildePullbackIso_eq (e : J) (hE : Ideal.span {(e : A)} = J)
    (he : (e : A) ∈ nonZeroDivisors A) :
    normalTildePullbackIso J r e hE he = normalTildePullbackIso J r d hJ hd := by
  unfold normalTildePullbackIso
  rw [normalModuleIso_eq J r d hJ hd e hE he]

end KltDP.Geometry.PrincipalConormalLocalization

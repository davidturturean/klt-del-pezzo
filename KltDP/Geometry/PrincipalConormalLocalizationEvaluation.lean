import KltDP.Geometry.PrincipalConormalLocalization
import KltDP.Geometry.PrincipalConormalTildeEvaluation
import KltDP.Geometry.AffineModuleTildePullbackUnit
import KltDP.Geometry.SchemeModulePullbackTensorMultiplication

/-!
# Original conormal evaluation under principal localization

The actual scalar-extension maps preserve the original principal coordinates.
Consequently the produced conormal/normal tilde pullback maps preserve the
original transported evaluation through the actual scheme tensor and unit
comparisons. Every map is the existing map on the original objects; no
comparison or compatibility equality is assumed.

The global kernel-conormal identification and gluing of adjunction remain separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped TensorProduct ChangeOfRings

universe u

namespace KltDP.Geometry.PrincipalConormalLocalizationEvaluation

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

open PrincipalConormalLocalization PrincipalConormalTildeEvaluation

variable {A : Type u} [CommRing A] (J : Ideal A) (r : A) (d : J)
  (hJ : Ideal.span {(d : A)} = J) (hd : (d : A) ∈ nonZeroDivisors A)

private abbrev localizedConormalCoframe :=
  conormalCoframe (localizedIdeal J r) (localizedEquation J r d)
    (localizedEquation_span J r d hJ) (localizedEquation_regular J r d hd)

private abbrev localizedNormalCoframe :=
  normalCoframe (localizedIdeal J r) (localizedEquation J r d)
    (localizedEquation_span J r d hJ) (localizedEquation_regular J r d hd)

private theorem conormal_coordinate_restriction (m : J.Cotangent) :
    (localizedConormalCoframe J r d hJ hd).hom (conormalRestriction J r m) =
      quotientMap J r ((conormalCoframe J d hJ hd).hom m) := by
  have h := KltDP.RingTheory.principalConormalEquiv_symm_conormalMap
    J (localizedIdeal J r) (algebraMap A (Localization.Away r))
    (fun _ hx => Ideal.mem_map_of_mem _ hx) d hJ hd
    (localizedEquation J r d) (localizedEquation_span J r d hJ)
    (localizedEquation_regular J r d hd) 1 (by simp only [localizedEquation, one_mul])
    ((KltDP.RingTheory.principalConormalEquiv J d hJ hd).symm m)
  simpa only [LinearEquiv.apply_symm_apply, map_one, mul_one] using h

/-- The produced conormal scalar-extension map preserves the original
principal coordinate under the actual quotient localization map. -/
theorem conormalModuleIso_coordinate :
    (conormalModuleIso J r d hJ hd).hom ≫ (localizedConormalCoframe J r d hJ hd).hom =
      AffineModuleTildePullbackUnit.extendedCoordinate
        (quotientMap J r) (conormalCoframe J d hJ hd).hom := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (localizedConormalCoframe J r d hJ hd).hom
      ((conormalModuleIso J r d hJ hd).hom
        ((1 : quotientRing J r) ⊗ₜ[A ⧸ J,quotientMap J r] m)) =
    (AffineModuleTildePullbackUnit.scalarUnitIso (quotientMap J r)).hom
      ((ModuleCat.extendScalars (quotientMap J r)).map (conormalCoframe J d hJ hd).hom
        ((1 : quotientRing J r) ⊗ₜ[A ⧸ J,quotientMap J r] m))
  rw [conormalModuleIso_tmul, one_smul, ModuleCat.ExtendScalars.map_tmul,
    AffineModuleTildePullbackUnit.scalarUnitIso_tmul, mul_one]
  exact conormal_coordinate_restriction J r d hJ hd m

/-- The produced normal scalar-extension map preserves its original
dual coordinate, determined by evaluation at the original equation class. -/
theorem normalModuleIso_coordinate :
    (normalModuleIso J r d hJ hd).hom ≫ (localizedNormalCoframe J r d hJ hd).hom =
      AffineModuleTildePullbackUnit.extendedCoordinate
        (quotientMap J r) (normalCoframe J d hJ hd).hom := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro ℓ
  change KltDP.RingTheory.principalNormalEquiv (localizedIdeal J r)
      (localizedEquation J r d) (localizedEquation_span J r d hJ)
      (localizedEquation_regular J r d hd)
      ((normalModuleIso J r d hJ hd).hom
        ((1 : quotientRing J r) ⊗ₜ[A ⧸ J,quotientMap J r] ℓ)) =
    (AffineModuleTildePullbackUnit.scalarUnitIso (quotientMap J r)).hom
      ((ModuleCat.extendScalars (quotientMap J r)).map (normalCoframe J d hJ hd).hom
        ((1 : quotientRing J r) ⊗ₜ[A ⧸ J,quotientMap J r] ℓ))
  rw [ModuleCat.ExtendScalars.map_tmul, AffineModuleTildePullbackUnit.scalarUnitIso_tmul, mul_one]
  change KltDP.RingTheory.principalNormalEquiv (localizedIdeal J r)
      (localizedEquation J r d) (localizedEquation_span J r d hJ)
      (localizedEquation_regular J r d hd)
      ((normalModuleIso J r d hJ hd).hom
        ((1 : quotientRing J r) ⊗ₜ[A ⧸ J,quotientMap J r] ℓ)) =
    quotientMap J r (KltDP.RingTheory.principalNormalEquiv J d hJ hd ℓ)
  simp only [KltDP.RingTheory.principalNormalEquiv_apply]
  change (normalModuleIso J r d hJ hd).hom
      ((1 : quotientRing J r) ⊗ₜ[A ⧸ J,quotientMap J r] ℓ)
      (conormalRestriction J r (J.toCotangent d)) = quotientMap J r (ℓ (J.toCotangent d))
  simpa only [one_mul] using normalModuleIso_evaluation J r d hJ hd
    (1 : quotientRing J r) ℓ (J.toCotangent d)

/-- The actual conormal tilde pullback comparison preserves the actual
coordinate after the original scheme pullback-unit map. -/
theorem conormalTildePullbackIso_coordinate :
    (conormalTildePullbackIso J r d hJ hd).hom ≫
        conormalCoordinate (localizedIdeal J r) (localizedEquation J r d)
          (localizedEquation_span J r d hJ) (localizedEquation_regular J r d hd) =
      (schemeModulePullback (Spec.map (CommRingCat.ofHom (quotientMap J r)))).map
          (conormalCoordinate J d hJ hd) ≫
        (schemeModulePullbackUnitIso
          (Spec.map (CommRingCat.ofHom (quotientMap J r)))).hom := by
  change ((AffineModuleTilde.pullbackIso (quotientMap J r)
      (PrincipalConormalTildeDual.conormalModule J)).hom ≫
      AffineModuleTilde.map (conormalModuleIso J r d hJ hd).hom) ≫
    (AffineModuleTilde.map (localizedConormalCoframe J r d hJ hd).hom ≫
      (AffineModuleTilde.unitIso (quotientRing J r)).hom) = _
  rw [Category.assoc, ← Category.assoc
    (AffineModuleTilde.map (conormalModuleIso J r d hJ hd).hom)
    (AffineModuleTilde.map (localizedConormalCoframe J r d hJ hd).hom),
    ← AffineModuleTilde.map_comp, conormalModuleIso_coordinate]
  exact AffineModuleTildePullbackUnit.pullback_coordinate
    (quotientMap J r) (conormalCoframe J d hJ hd).hom

/-- The actual normal tilde pullback comparison preserves the actual
dual coordinate after the same original pullback-unit map. -/
theorem normalTildePullbackIso_coordinate :
    (normalTildePullbackIso J r d hJ hd).hom ≫
        normalCoordinate (localizedIdeal J r) (localizedEquation J r d)
          (localizedEquation_span J r d hJ) (localizedEquation_regular J r d hd) =
      (schemeModulePullback (Spec.map (CommRingCat.ofHom (quotientMap J r)))).map
          (normalCoordinate J d hJ hd) ≫
        (schemeModulePullbackUnitIso
          (Spec.map (CommRingCat.ofHom (quotientMap J r)))).hom := by
  change ((AffineModuleTilde.pullbackIso (quotientMap J r)
      (PrincipalConormalTildeDual.normalModule J)).hom ≫
      AffineModuleTilde.map (normalModuleIso J r d hJ hd).hom) ≫
    (AffineModuleTilde.map (localizedNormalCoframe J r d hJ hd).hom ≫
      (AffineModuleTilde.unitIso (quotientRing J r)).hom) = _
  rw [Category.assoc, ← Category.assoc
    (AffineModuleTilde.map (normalModuleIso J r d hJ hd).hom)
    (AffineModuleTilde.map (localizedNormalCoframe J r d hJ hd).hom),
    ← AffineModuleTilde.map_comp, normalModuleIso_coordinate]
  exact AffineModuleTildePullbackUnit.pullback_coordinate
    (quotientMap J r) (normalCoframe J d hJ hd).hom

/-- The original conormal/normal evaluation commutes with principal
localization through the original scheme tensor and unit comparisons. -/
theorem tensor_evaluation :
    (tensorIso (conormalTildePullbackIso J r d hJ hd)
      (normalTildePullbackIso J r d hJ hd)).hom ≫
        (PrincipalConormalTildeDual.transportedEvaluationIso (localizedIdeal J r)
          (localizedEquation J r d) (localizedEquation_span J r d hJ)
          (localizedEquation_regular J r d hd)).hom =
      (schemeModulePullbackTensorIso
        (Spec.map (CommRingCat.ofHom (quotientMap J r)))
        (PrincipalConormalTildeDual.conormalModule J).tilde
        (PrincipalConormalTildeDual.normalModule J).tilde).inv ≫
      (schemeModulePullback (Spec.map (CommRingCat.ofHom (quotientMap J r)))).map
        (PrincipalConormalTildeDual.transportedEvaluationIso J d hJ hd).hom ≫
      (schemeModulePullbackUnitIso
        (Spec.map (CommRingCat.ofHom (quotientMap J r)))).hom := by
  apply (cancel_epi (schemeModulePullbackTensorIso
    (Spec.map (CommRingCat.ofHom (quotientMap J r)))
    (PrincipalConormalTildeDual.conormalModule J).tilde
    (PrincipalConormalTildeDual.normalModule J).tilde).hom).1
  rw [Iso.hom_inv_id_assoc]
  rw [transportedEvaluation_product, transportedEvaluation_product]
  simp only [tensorIso_hom, Category.assoc]
  rw [← tensor_comp_assoc, conormalTildePullbackIso_coordinate,
    normalTildePullbackIso_coordinate]
  exact schemeModulePullbackTensorIso_product
    (Spec.map (CommRingCat.ofHom (quotientMap J r)))
    (conormalCoordinate J d hJ hd) (normalCoordinate J d hJ hd)

end KltDP.Geometry.PrincipalConormalLocalizationEvaluation

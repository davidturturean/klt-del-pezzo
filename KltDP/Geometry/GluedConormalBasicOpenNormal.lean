import KltDP.Geometry.GluedConormalBasicOpenLocalization
import KltDP.Geometry.PrincipalConormalTildeDual

/-!
# Original normal modules on actual basic-open quotient charts

The original regular principal frames produce scalar extension of the
actual module dual of the ideal cotangent. Evaluation on the original
restricted cotangent is the original quotient-ring map applied to source
evaluation, including every scalar. This determines the map independently
of the regular equation and gives its actual tilde pullback isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

namespace KltDP.Geometry.GluedConormalBasicOpenNormal

open GluedConormalBasicOpenLocalization

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
  (r d : Γ(X, U.1)) (hI : I.ideal U = Ideal.span {d})
  (hd : d ∈ nonZeroDivisors Γ(X, U.1))

private def sourceCoordinate := KltDP.RingTheory.principalNormalEquiv (I.ideal U)
  (gluedAffineIdealEquation I U d hI) hI.symm hd

private def targetCoordinate := KltDP.RingTheory.principalNormalEquiv (I.ideal (X.affineBasicOpen r))
  (gluedAffineIdealEquation I (X.affineBasicOpen r) (sectionMap U r d)
    (equation_span I U r d hI))
  (equation_span I U r d hI).symm (equation_regular U r d hd)

/-- Scalar extension of the original normal module is the original normal module on the basic open. -/
def normalModuleIso :
    (ModuleCat.extendScalars (quotientMap I U r)).obj
        (PrincipalConormalTildeDual.normalModule (I.ideal U)) ≅
      PrincipalConormalTildeDual.normalModule (I.ideal (X.affineBasicOpen r)) :=
  (ModuleCat.extendScalars (quotientMap I U r)).mapIso
      (sourceCoordinate I U d hI hd).toModuleIso ≪≫
    AffineModuleTildePullbackUnit.scalarUnitIso (quotientMap I U r) ≪≫
      (targetCoordinate I U r d hI hd).symm.toModuleIso

private theorem generator_evaluation
    (s : Γ(X, (X.affineBasicOpen r).1) ⧸ I.ideal (X.affineBasicOpen r))
    (ℓ : Module.Dual (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent) :
    (normalModuleIso I U r d hI hd).hom
        (s ⊗ₜ[Γ(X, U.1) ⧸ I.ideal U,quotientMap I U r] ℓ)
        (conormalRestriction I U r ((I.ideal U).toCotangent
          (gluedAffineIdealEquation I U d hI))) =
      s * quotientMap I U r (ℓ ((I.ideal U).toCotangent (gluedAffineIdealEquation I U d hI))) := by
  change (targetCoordinate I U r d hI hd).symm
      ((AffineModuleTildePullbackUnit.scalarUnitIso (quotientMap I U r)).hom
        ((ModuleCat.extendScalars (quotientMap I U r)).map
          (sourceCoordinate I U d hI hd).toModuleIso.hom
          (s ⊗ₜ[Γ(X, U.1) ⧸ I.ideal U,quotientMap I U r] ℓ)))
      (conormalRestriction I U r ((I.ideal U).toCotangent
        (gluedAffineIdealEquation I U d hI))) = _
  rw [ModuleCat.ExtendScalars.map_tmul, AffineModuleTildePullbackUnit.scalarUnitIso_tmul]
  change (targetCoordinate I U r d hI hd).symm
      (quotientMap I U r (sourceCoordinate I U d hI hd ℓ) * s)
      ((I.ideal (X.affineBasicOpen r)).toCotangent
        (gluedAffineIdealEquation I (X.affineBasicOpen r) (sectionMap U r d)
          (equation_span I U r d hI))) = _
  have he := (targetCoordinate I U r d hI hd).apply_symm_apply
    (quotientMap I U r (sourceCoordinate I U d hI hd ℓ) * s)
  simpa only [targetCoordinate, sourceCoordinate,
    KltDP.RingTheory.principalNormalEquiv_apply, mul_comm] using he

/-- Every original evaluation is preserved by the actual quotient restriction, with its scalar. -/
theorem normalModuleIso_evaluation
    (s : Γ(X, (X.affineBasicOpen r).1) ⧸ I.ideal (X.affineBasicOpen r))
    (ℓ : Module.Dual (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent)
    (m : (I.ideal U).Cotangent) :
    (normalModuleIso I U r d hI hd).hom
        (s ⊗ₜ[Γ(X, U.1) ⧸ I.ideal U,quotientMap I U r] ℓ)
        (conormalRestriction I U r m) = s * quotientMap I U r (ℓ m) := by
  let e := gluedAffineCotangentEquiv I U d hI hd
  obtain ⟨q, rfl⟩ := e.surjective m
  have he1 : e 1 = (I.ideal U).toCotangent (gluedAffineIdealEquation I U d hI) :=
    gluedAffineCotangentEquiv_one I U d hI hd
  have heq : e q = q • (I.ideal U).toCotangent (gluedAffineIdealEquation I U d hI) := by
    simpa only [smul_eq_mul, mul_one, he1] using e.map_smul q (1 : Γ(X, U.1) ⧸ I.ideal U)
  rw [heq, (conormalRestriction I U r).map_smulₛₗ]
  simp only [map_smul, smul_eq_mul]
  rw [generator_evaluation, map_mul]
  ac_rfl

/-- Original evaluation fixes the scalar-extension map independently of the regular equation. -/
theorem normalModuleIso_eq (e : Γ(X, U.1)) (hE : I.ideal U = Ideal.span {e})
    (he : e ∈ nonZeroDivisors Γ(X, U.1)) :
    normalModuleIso I U r d hI hd = normalModuleIso I U r e hE he := by
  apply Iso.ext
  apply ModuleCat.ExtendScalars.hom_ext
  intro ℓ
  apply (targetCoordinate I U r d hI hd).injective
  simp only [targetCoordinate, KltDP.RingTheory.principalNormalEquiv_apply]
  change (normalModuleIso I U r d hI hd).hom
      ((1 : Γ(X, (X.affineBasicOpen r).1) ⧸ I.ideal (X.affineBasicOpen r))
        ⊗ₜ[Γ(X, U.1) ⧸ I.ideal U,quotientMap I U r] ℓ)
      (conormalRestriction I U r ((I.ideal U).toCotangent (gluedAffineIdealEquation I U d hI))) =
    (normalModuleIso I U r e hE he).hom
      ((1 : Γ(X, (X.affineBasicOpen r).1) ⧸ I.ideal (X.affineBasicOpen r))
        ⊗ₜ[Γ(X, U.1) ⧸ I.ideal U,quotientMap I U r] ℓ)
      (conormalRestriction I U r ((I.ideal U).toCotangent (gluedAffineIdealEquation I U d hI)))
  rw [normalModuleIso_evaluation, normalModuleIso_evaluation]

/-- Actual sheaf pullback along the original quotient-chart inclusion gives the smaller normal tilde. -/
def normalTildeRefinementIso :
    (schemeModulePullback (I.glueDataObjMap (X.affineBasicOpen_le r))).obj
        (PrincipalConormalTildeDual.normalModule (I.ideal U)).tilde ≅
      (PrincipalConormalTildeDual.normalModule (I.ideal (X.affineBasicOpen r))).tilde :=
  AffineModuleTilde.pullbackIso (quotientMap I U r)
      (PrincipalConormalTildeDual.normalModule (I.ideal U)) ≪≫
    AffineModuleTilde.mapIso (normalModuleIso I U r d hI hd)

/-- The actual normal tilde refinement also retains equation independence. -/
theorem normalTildeRefinementIso_eq (e : Γ(X, U.1)) (hE : I.ideal U = Ideal.span {e})
    (he : e ∈ nonZeroDivisors Γ(X, U.1)) :
    normalTildeRefinementIso I U r d hI hd = normalTildeRefinementIso I U r e hE he := by
  unfold normalTildeRefinementIso
  rw [normalModuleIso_eq I U r d hI hd e hE he]

end KltDP.Geometry.GluedConormalBasicOpenNormal

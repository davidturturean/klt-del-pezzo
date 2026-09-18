import KltDP.Geometry.GluedConormalBasicOpenNormal
import KltDP.Geometry.AffineModuleTildeSemilinearMap
import KltDP.RingTheory.NormalTwistedAdjunctionRestriction

/-!
# The original normal chart refinement is the original semilinear normal map

Both normal-module maps preserve evaluation on the original restricted
equation. The actual principal normal coordinate and scalar-extension
universal property therefore identify the entire original maps. The tilde
comparison gives the same equality on the actual quotient-chart pullback.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct ChangeOfRings
universe u
namespace KltDP.Geometry.GluedConormalNormalSemilinear

open GluedConormalBasicOpenLocalization GluedConormalBasicOpenNormal
open AffineModuleTildeSemilinearMap

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
  (r d : Γ(X, U.1)) (hU : I.ideal U = Ideal.span {d})
  (hd : d ∈ nonZeroDivisors Γ(X, U.1))

/-- The original normal restriction used by the original normal-twisted adjunction. -/
def nativeNormalMap :
    PrincipalConormalTildeDual.normalModule (I.ideal U) →ₛₗ[quotientMap I U r]
      PrincipalConormalTildeDual.normalModule (I.ideal (X.affineBasicOpen r)) := by
  letI : Algebra Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1) := (sectionMap U r).toAlgebra
  exact KltDP.RingTheory.NormalTwistedAdjunctionRestriction.normalRestriction
    Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1) (I.ideal U) (I.ideal (X.affineBasicOpen r))
    (I.ideal_le_comap_ideal (X.affineBasicOpen_le r)) (gluedAffineIdealEquation I U d hU)
    hU.symm hd (equation_span I U r d hU).symm (equation_regular U r d hd)

/-- The actual basic-open normal module isomorphism is scalar extension of that same map. -/
theorem normalModuleIso_hom_eq :
    (normalModuleIso I U r d hU hd).hom = extendHom (quotientMap I U r)
      (nativeNormalMap I U r d hU hd) := by
  letI : Algebra Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1) := (sectionMap U r).toAlgebra
  let e := KltDP.RingTheory.principalNormalEquiv (I.ideal (X.affineBasicOpen r))
    (gluedAffineIdealEquation I (X.affineBasicOpen r) (sectionMap U r d)
      (equation_span I U r d hU))
    (equation_span I U r d hU).symm (equation_regular U r d hd)
  apply ModuleCat.ExtendScalars.hom_ext
  intro ℓ
  rw [extendHom_one_tmul]
  apply e.injective
  simp only [e, KltDP.RingTheory.principalNormalEquiv_apply]
  change (normalModuleIso I U r d hU hd).hom
      ((1 : Γ(X, (X.affineBasicOpen r).1) ⧸ I.ideal (X.affineBasicOpen r))
        ⊗ₜ[Γ(X, U.1) ⧸ I.ideal U,quotientMap I U r] ℓ)
        (conormalRestriction I U r ((I.ideal U).toCotangent (gluedAffineIdealEquation I U d hU))) =
    nativeNormalMap I U r d hU hd ℓ
      ((I.ideal (X.affineBasicOpen r)).toCotangent
        (gluedAffineIdealEquation I (X.affineBasicOpen r) (sectionMap U r d)
          (equation_span I U r d hU)))
  have h := normalModuleIso_evaluation I U r d hU hd 1 ℓ
    ((I.ideal U).toCotangent (gluedAffineIdealEquation I U d hU))
  rw [one_mul] at h
  exact h.trans (KltDP.RingTheory.NormalTwistedAdjunctionRestriction.normalRestriction_generator
    Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1) (I.ideal U) (I.ideal (X.affineBasicOpen r))
    (I.ideal_le_comap_ideal (X.affineBasicOpen_le r)) (gluedAffineIdealEquation I U d hU)
    hU.symm hd (equation_span I U r d hU).symm (equation_regular U r d hd) ℓ).symm

/-- The actual normal tilde refinement is the original semilinear pullback map. -/
theorem normalTildeRefinementIso_hom_eq :
    (normalTildeRefinementIso I U r d hU hd).hom =
      pullbackMap (quotientMap I U r) (nativeNormalMap I U r d hU hd) := by
  change (AffineModuleTilde.pullbackIso (quotientMap I U r)
      (PrincipalConormalTildeDual.normalModule (I.ideal U))).hom ≫
        AffineModuleTilde.map (normalModuleIso I U r d hU hd).hom =
    (AffineModuleTilde.pullbackIso (quotientMap I U r)
      (PrincipalConormalTildeDual.normalModule (I.ideal U))).hom ≫
        AffineModuleTilde.map (extendHom (quotientMap I U r) (nativeNormalMap I U r d hU hd))
  rw [normalModuleIso_hom_eq]

end KltDP.Geometry.GluedConormalNormalSemilinear

import KltDP.Geometry.GluedConormalPullbackFrame
import KltDP.Geometry.AffineModuleTildePullbackUnit
import KltDP.RingTheory.ConormalRestriction

/-!
# Original cotangent modules on actual basic-open quotient charts

The actual ideal on a basic open is its proved image ideal. The original
regular equation remains regular under the pinned
localization theorem. Its two principal frames give scalar extension of
the original ideal cotangent map, with the formula on every pure tensor.

The resulting sheaf isomorphism uses the actual `glueDataObjMap`, not a
replacement chart. Agreement with the global conormal chart comparison
on this refinement remains a separate square.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

namespace KltDP.Geometry.GluedConormalBasicOpenLocalization

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
  (r : Γ(X, U.1))

/-- The original restriction map to the actual basic-open section ring. -/
def sectionMap : Γ(X, U.1) →+* Γ(X, (X.affineBasicOpen r).1) :=
  (X.presheaf.map (homOfLE (X.affineBasicOpen_le r)).op).hom

/-- The original quotient map used to define the actual quotient-chart inclusion. -/
def quotientMap : Γ(X, U.1) ⧸ I.ideal U →+*
    Γ(X, (X.affineBasicOpen r).1) ⧸ I.ideal (X.affineBasicOpen r) :=
  Ideal.quotientMap _ (sectionMap U r) (I.ideal_le_comap_ideal (X.affineBasicOpen_le r))

/-- The original ideal cotangent map on the actual basic-open section rings. -/
def conormalRestriction : (I.ideal U).Cotangent →ₛₗ[quotientMap I U r]
    (I.ideal (X.affineBasicOpen r)).Cotangent :=
  KltDP.RingTheory.conormalMap (I.ideal U) (I.ideal (X.affineBasicOpen r))
    (sectionMap U r) (I.ideal_le_comap_ideal (X.affineBasicOpen_le r))

/-- No chart map is replaced: this is the original map in the ideal-sheaf gluing. -/
theorem specMap_eq :
    Spec.map (CommRingCat.ofHom (quotientMap I U r)) =
      I.glueDataObjMap (X.affineBasicOpen_le r) := rfl

variable (d : Γ(X, U.1)) (hI : I.ideal U = Ideal.span {d})
  (hd : d ∈ nonZeroDivisors Γ(X, U.1))

include hI in
/-- The original restricted equation generates the original ideal on the basic open. -/
theorem equation_span : I.ideal (X.affineBasicOpen r) = Ideal.span {sectionMap U r d} := by
  rw [← I.map_ideal (X.affineBasicOpen_le r), hI, Ideal.map_span, Set.image_singleton]
  rfl

include hd in
/-- The same original restricted equation is regular, by the existing localization theorem. -/
theorem equation_regular : sectionMap U r d ∈ nonZeroDivisors Γ(X, (X.affineBasicOpen r).1) := by
  letI : Algebra Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1) := (sectionMap U r).toAlgebra
  letI : IsLocalization.Away r Γ(X, (X.affineBasicOpen r).1) := U.2.isLocalization_basicOpen r
  exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers r)
    Γ(X, (X.affineBasicOpen r).1) hd

private def sourceFrame := gluedAffineCotangentEquiv I U d hI hd

private def targetFrame := gluedAffineCotangentEquiv I (X.affineBasicOpen r)
  (sectionMap U r d) (equation_span I U r d hI) (equation_regular U r d hd)

include d hI hd in
private theorem conormalRestriction_coordinates (m : (I.ideal U).Cotangent) :
    conormalRestriction I U r m = targetFrame I U r d hI hd
      (quotientMap I U r ((sourceFrame I U d hI hd).symm m)) := by
  have h := KltDP.RingTheory.conormalMap_principalConormalEquiv
    (I.ideal U) (I.ideal (X.affineBasicOpen r)) (sectionMap U r)
    (I.ideal_le_comap_ideal (X.affineBasicOpen_le r))
    (gluedAffineIdealEquation I U d hI) hI.symm hd
    (gluedAffineIdealEquation I (X.affineBasicOpen r) (sectionMap U r d)
      (equation_span I U r d hI)) (equation_span I U r d hI).symm
    (equation_regular U r d hd) 1 (by simp only [gluedAffineIdealEquation, one_mul])
    ((sourceFrame I U d hI hd).symm m)
  change conormalRestriction I U r
      ((sourceFrame I U d hI hd) ((sourceFrame I U d hI hd).symm m)) =
    targetFrame I U r d hI hd
      (quotientMap I U r ((sourceFrame I U d hI hd).symm m) *
        Ideal.Quotient.mk (I.ideal (X.affineBasicOpen r)) 1) at h
  simpa only [LinearEquiv.apply_symm_apply, map_one, mul_one] using h

/-- Original scalar extension is the actual basic-open cotangent module. -/
def moduleIso :
    (ModuleCat.extendScalars (quotientMap I U r)).obj
        (ModuleCat.of (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent) ≅
      ModuleCat.of (Γ(X, (X.affineBasicOpen r).1) ⧸ I.ideal (X.affineBasicOpen r))
        (I.ideal (X.affineBasicOpen r)).Cotangent :=
  (ModuleCat.extendScalars (quotientMap I U r)).mapIso
      (sourceFrame I U d hI hd).symm.toModuleIso ≪≫
    AffineModuleTildePullbackUnit.scalarUnitIso (quotientMap I U r) ≪≫
      (targetFrame I U r d hI hd).toModuleIso

/-- This comparison is the scalar extension of the original ideal cotangent map. -/
theorem moduleIso_tmul
    (s : Γ(X, (X.affineBasicOpen r).1) ⧸ I.ideal (X.affineBasicOpen r))
    (m : (I.ideal U).Cotangent) :
    (moduleIso I U r d hI hd).hom (s ⊗ₜ[Γ(X, U.1) ⧸ I.ideal U,quotientMap I U r] m) =
      s • conormalRestriction I U r m := by
  change targetFrame I U r d hI hd
      ((AffineModuleTildePullbackUnit.scalarUnitIso (quotientMap I U r)).hom
        ((ModuleCat.extendScalars (quotientMap I U r)).map
          (sourceFrame I U d hI hd).symm.toModuleIso.hom
          (s ⊗ₜ[Γ(X, U.1) ⧸ I.ideal U,quotientMap I U r] m))) = _
  rw [ModuleCat.ExtendScalars.map_tmul, AffineModuleTildePullbackUnit.scalarUnitIso_tmul,
    conormalRestriction_coordinates I U r d hI hd, ← map_smul]
  exact congrArg (targetFrame I U r d hI hd) (mul_comm _ _)

/-- The actual scalar-extension comparison is independent of the regular equation. -/
theorem moduleIso_eq (e : Γ(X, U.1)) (hE : I.ideal U = Ideal.span {e})
    (he : e ∈ nonZeroDivisors Γ(X, U.1)) :
    moduleIso I U r d hI hd = moduleIso I U r e hE he := by
  apply Iso.ext
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  rw [moduleIso_tmul, moduleIso_tmul]

/-- Actual pullback along the original quotient-chart inclusion gives the smaller cotangent tilde. -/
def tildeRefinementIso :
    (schemeModulePullback (I.glueDataObjMap (X.affineBasicOpen_le r))).obj
        (ModuleCat.of (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent).tilde ≅
      (ModuleCat.of (Γ(X, (X.affineBasicOpen r).1) ⧸ I.ideal (X.affineBasicOpen r))
        (I.ideal (X.affineBasicOpen r)).Cotangent).tilde :=
  AffineModuleTilde.pullbackIso (quotientMap I U r)
      (ModuleCat.of (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent) ≪≫
    AffineModuleTilde.mapIso (moduleIso I U r d hI hd)

/-- Equation independence holds for this original chart pullback too. -/
theorem tildeRefinementIso_eq (e : Γ(X, U.1)) (hE : I.ideal U = Ideal.span {e})
    (he : e ∈ nonZeroDivisors Γ(X, U.1)) :
    tildeRefinementIso I U r d hI hd = tildeRefinementIso I U r e hE he := by
  unfold tildeRefinementIso
  rw [moduleIso_eq I U r d hI hd e hE he]

end KltDP.Geometry.GluedConormalBasicOpenLocalization

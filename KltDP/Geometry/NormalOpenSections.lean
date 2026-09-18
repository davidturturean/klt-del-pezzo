import KltDP.Geometry.CartierPrincipalModuleLocal
import KltDP.Geometry.ProjectiveChartNormal
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
Normality of the original section ring on every nonempty open of an
integral normal scheme. The local-to-global step reuses the proved local
membership theorem for the original principal fractional module with
equation 1. No affine-preimage or fraction-field equality is assumed.

This is a source-only proof candidate; root controls VM validation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

variable (X : Scheme.{u}) [IsIntegral X]

/-- An integral rational function lies in every original stalk over the
open on which its integral equation has coefficients. -/
theorem exists_stalkRepresentative_of_isIntegral
    (hnormal : IsNormalScheme X) (U : X.Opens) [Nonempty U]
    {q : X.functionField} (hq : IsIntegral Γ(X, U) q) (x : U) :
    ∃ a : X.presheaf.stalk x.1,
      algebraMap (X.presheaf.stalk x.1) X.functionField a = q := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk x.1) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf x
  letI : IsDomain (X.presheaf.stalk x.1) := (hnormal x.1).1
  letI : IsIntegrallyClosed (X.presheaf.stalk x.1) := (hnormal x.1).2
  letI : IsScalarTower Γ(X, U) (X.presheaf.stalk x.1) X.functionField :=
    functionField_isScalarTower X U x
  exact IsIntegrallyClosed.algebraMap_eq_of_integral
    (hq.tower_top (A := X.presheaf.stalk x.1))

/-- Integral rational functions glue to actual sections of the original
structure sheaf; the ambient function field need not be the fraction
field of the possibly nonaffine open's section ring. -/
theorem isIntegrallyClosedIn_openSections_of_isNormal
    (hnormal : IsNormalScheme X) (U : X.Opens) [Nonempty U] :
    IsIntegrallyClosedIn Γ(X, U) X.functionField := by
  refine isIntegrallyClosedIn_iff.mpr
    ⟨X.germToFunctionField_injective U, fun {q} hq => ?_⟩
  have hlocal : q ∈ principalEquationSubmodule X U 1 := by
    apply mem_principalEquationSubmodule_of_locally_mem X U 1 q
    intro x hx
    obtain ⟨a, ha⟩ :=
      exists_stalkRepresentative_of_isIntegral X hnormal U hq ⟨x, hx⟩
    obtain ⟨W, hxW, s, hs⟩ := X.presheaf.germ_exist x a
    letI : Nonempty W := ⟨⟨x, hxW⟩⟩
    have hsfield : X.germToFunctionField W s = q := by
      calc
        _ = algebraMap (X.presheaf.stalk x) X.functionField
            (X.presheaf.germ W x hxW s) :=
          (ConcreteCategory.congr_hom (X.presheaf.germ_stalkSpecializes hxW
            ((genericPoint_spec X).specializes trivial)) s).symm
        _ = algebraMap (X.presheaf.stalk x) X.functionField a := congrArg _ hs
        _ = q := ha
    have hW : q ∈ principalEquationSubmodule X W 1 := by
      apply (mem_principalEquationSubmodule_iff X W 1 q).mpr
      exact ⟨s, by simpa only [Units.val_one, one_mul] using hsfield⟩
    letI : Nonempty (U ⊓ W : X.Opens) := ⟨⟨x, hx, hxW⟩⟩
    refine ⟨U ⊓ W, homOfLE inf_le_left, ⟨hx, hxW⟩, ?_⟩
    exact mem_principalEquationSubmodule_restrict X inf_le_right 1 hW
  obtain ⟨a, ha⟩ := (mem_principalEquationSubmodule_iff X U 1 q).mp hlocal
  exact ⟨a, by simpa only [Units.val_one, one_mul] using ha⟩

/-- Every original nonempty open in an integral normal scheme has an
integrally closed ring of sections. -/
theorem isIntegrallyClosed_openSections_of_isNormal
    (hnormal : IsNormalScheme X) (U : X.Opens) [Nonempty U] :
    IsIntegrallyClosed Γ(X, U) := by
  let e : FractionRing Γ(X, U) →ₐ[Γ(X, U)] X.functionField :=
    IsFractionRing.liftAlgHom (g := Algebra.ofId Γ(X, U) X.functionField)
      (X.germToFunctionField_injective U)
  exact e.isIntegrallyClosedIn e.toRingHom.injective
    (isIntegrallyClosedIn_openSections_of_isNormal X hnormal U)

end KltDP.Geometry

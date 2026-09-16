import KltDP.Geometry.CartierEquationUnits
import Mathlib.LinearAlgebra.Span.Basic

/-!
# The actual principal fractional module of a Cartier equation

For a local rational equation `f`, the convention is `O(D) = f⁻¹ O`.
On a nonempty open this is the actual span of `f⁻¹` inside the original
function field, over the original ring of sections. Pinned singleton-span
and linear-equivalence APIs give its membership criterion and rank-one
coordinate map. Equal Cartier equation classes give equal submodules by
their proved regular transition unit.

These are local section modules and restriction/overlap facts. The global
submodule sheaf and its local trivializations are separate constructions;
no sheaf condition or global invertibility is assumed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

variable (X : Scheme.{u}) [IsIntegral X]

/-- The actual section module `f⁻¹ Γ(X,U)` in the original function field. -/
def principalEquationSubmodule (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ) :
    Submodule Γ(X, U) X.functionField :=
  Submodule.span Γ(X, U) {(↑(f⁻¹) : X.functionField)}

/-- The sign convention is characterized without a chosen coordinate:
`s ∈ f⁻¹ O(U)` precisely when `f * s` is the image of a regular section. -/
theorem mem_principalEquationSubmodule_iff
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ) (s : X.functionField) :
    s ∈ principalEquationSubmodule X U f ↔
      ∃ a : Γ(X, U), X.germToFunctionField U a = (f : X.functionField) * s := by
  rw [principalEquationSubmodule, Submodule.mem_span_singleton]
  apply exists_congr
  intro a
  rw [Algebra.smul_def, mul_comm (algebraMap Γ(X, U) X.functionField a),
    Units.inv_mul_eq_iff_eq_mul]
  rfl

/-- The actual scalar action on the function field is torsion free,
as proved by injectivity of the original section-to-function-field map. -/
theorem principalEquation_noZeroSMulDivisors (U : X.Opens) [Nonempty U] :
    NoZeroSMulDivisors Γ(X, U) X.functionField :=
  NoZeroSMulDivisors.iff_algebraMap_injective.mpr (X.germToFunctionField_injective U)

/-- The rank-one coordinate map sends a regular section `a` to `a/f`.
It is an actual linear equivalence with the actual fractional submodule. -/
def principalEquationSubmoduleEquiv (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ) :
    Γ(X, U) ≃ₗ[Γ(X, U)] principalEquationSubmodule X U f := by
  letI := principalEquation_noZeroSMulDivisors X U
  exact LinearEquiv.toSpanNonzeroSingleton Γ(X, U) X.functionField
    (↑(f⁻¹) : X.functionField) (Units.ne_zero _)

@[simp]
theorem principalEquationSubmoduleEquiv_apply
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ) (a : Γ(X, U)) :
    ((principalEquationSubmoduleEquiv X U f a : principalEquationSubmodule X U f) :
        X.functionField) = X.germToFunctionField U a * (↑(f⁻¹) : X.functionField) := rfl

/-- Equal actual Cartier equation classes define the same fractional
submodule. This is deduced from the actual regular-unit ratio. -/
theorem principalEquationSubmodule_eq_of_class_eq
    (U : X.Opens) [Nonempty U] (f g : X.functionFieldˣ)
    (hfg : cartierEquationClassHom X U (Additive.ofMul f) =
      cartierEquationClassHom X U (Additive.ofMul g)) :
    principalEquationSubmodule X U f = principalEquationSubmodule X U g := by
  letI := principalEquation_noZeroSMulDivisors X U
  apply Submodule.span_singleton_eq_span_singleton.mpr
  refine ⟨cartierTransitionUnit X U f g hfg, ?_⟩
  change algebraMap Γ(X, U) X.functionField
      (cartierTransitionUnit X U f g hfg : Γ(X, U)) * (↑(f⁻¹) : X.functionField) =
    (↑(g⁻¹) : X.functionField)
  change (↑(Units.map (X.germToFunctionField U).hom.toMonoidHom
      (cartierTransitionUnit X U f g hfg) * f⁻¹) : X.functionField) =
    (↑(g⁻¹) : X.functionField)
  rw [map_cartierTransitionUnit]
  congr 1
  calc
    (f / g) * f⁻¹ = (f * f⁻¹) * g⁻¹ := by
      simp only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    _ = g⁻¹ := by rw [mul_inv_cancel, one_mul]

/-- Membership in the actual principal fractional module is preserved
by restriction of its coefficient to a smaller nonempty open. -/
theorem mem_principalEquationSubmodule_restrict
    {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U)
    (f : X.functionFieldˣ) {s : X.functionField}
    (hs : s ∈ principalEquationSubmodule X U f) :
    s ∈ principalEquationSubmodule X V f := by
  obtain ⟨a, ha⟩ := (mem_principalEquationSubmodule_iff X U f s).mp hs
  apply (mem_principalEquationSubmodule_iff X V f s).mpr
  refine ⟨X.presheaf.map (homOfLE h).op a, ?_⟩
  exact (X.presheaf.germ_res_apply (homOfLE h) (genericPoint X)
    (genericPoint_mem_nonempty_open X V) a).trans ha

end KltDP.Geometry

import KltDP.Geometry.CartierPrincipalModule
import KltDP.Geometry.RationalFunctionModule
import KltDP.Compatibility.SheafLocalImage

/-!
# Local membership in actual principal fractional modules

Membership in `f⁻¹ O(U)` is local on `U`. We prove this using the actual
inclusion of the structure-sheaf module into the rational-function module,
and local image descent for a monomorphism of sheaves of abelian groups.
The coefficient is obtained in the original section ring; it is not a
chosen function-field value asserted to be regular.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

variable (X : Scheme.{u}) [IsIntegral X]

/-- A rational function lies in `f⁻¹ O(U)` when it does so on an actual
neighborhood of every point. This produces its regular coefficient on `U`. -/
theorem mem_principalEquationSubmodule_of_locally_mem
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ) (s : X.functionField)
    (hlocal : ∀ x ∈ U, ∃ (V : X.Opens) (i : V ⟶ U) (hxV : x ∈ V),
      letI : Nonempty V := ⟨⟨x, hxV⟩⟩
      s ∈ principalEquationSubmodule X V f) :
    s ∈ principalEquationSubmodule X U f := by
  let φ := (_root_.SheafOfModules.toSheaf X.ringCatSheaf).map
    (structureToRationalFunctionModule X)
  letI : Mono φ := CategoryTheory.Sheaf.mono_of_injective φ
    (fun W => structureToRationalFunctionModule_app_injective X W.unop)
  let t : (rationalFunctionModule X).val.obj (op U) :=
    (rationalFunctionModuleSectionsEquiv X U).symm ((f : X.functionField) * s)
  have ht : ∀ x ∈ U, ∃ (V : X.Opens) (i : V ⟶ U)
      (a : ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj
        (_root_.SheafOfModules.unit X.ringCatSheaf)).val.obj (op V)),
      x ∈ V ∧ φ.val.app (op V) a =
        ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj
          (rationalFunctionModule X)).val.map i.op t := by
    intro x hx
    obtain ⟨V, i, hxV, hsV⟩ := hlocal x hx
    letI : Nonempty V := ⟨⟨x, hxV⟩⟩
    obtain ⟨a, ha⟩ := (mem_principalEquationSubmodule_iff X V f s).mp hsV
    refine ⟨V, i, a, hxV, ?_⟩
    change (structureToRationalFunctionModule X).val.app (op V) a =
      (rationalFunctionModule X).val.map i.op t
    apply (rationalFunctionModuleSectionsEquiv X V).injective
    rw [rationalFunctionModuleSectionsEquiv_structure,
      rationalFunctionModuleSectionsEquiv_naturality]
    change X.germToFunctionField V a =
      rationalFunctionModuleSectionsEquiv X U
        ((rationalFunctionModuleSectionsEquiv X U).symm ((f : X.functionField) * s))
    rw [LinearEquiv.apply_symm_apply]
    exact ha
  obtain ⟨a, ha⟩ := KltDP.Sheaf.exists_preimage_of_locally_in_image φ U t ht
  apply (mem_principalEquationSubmodule_iff X U f s).mpr
  refine ⟨a, ?_⟩
  change (structureToRationalFunctionModule X).val.app (op U) a = t at ha
  calc
    X.germToFunctionField U a = rationalFunctionModuleSectionsEquiv X U
        ((structureToRationalFunctionModule X).val.app (op U) a) :=
      (rationalFunctionModuleSectionsEquiv_structure X U a).symm
    _ = rationalFunctionModuleSectionsEquiv X U t := congrArg _ ha
    _ = (f : X.functionField) * s := LinearEquiv.apply_symm_apply _ _

end KltDP.Geometry

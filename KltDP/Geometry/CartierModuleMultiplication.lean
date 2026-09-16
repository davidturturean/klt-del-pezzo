import KltDP.Geometry.CartierCommonEquations
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# Multiplication of the actual Cartier divisor modules

The product of actual rational sections of `O(D)` and `O(E)` belongs to
`O(D+E)`. This is proved locally on common equation charts: the product
of a section in `f⁻¹ O` and one in `g⁻¹ O` lies in `(fg)⁻¹ O`.
The already proved locality of the actual Cartier submodule then gives
the product on every open, including the empty open.

The actual section multiplication is bilinear and commutes with the
actual ring restrictions. Pinned `ModuleCat.MonoidalCategory.tensorLift`
therefore gives a morphism from the sectionwise presheaf tensor. Its
sheafification and tensor-isomorphism property are separate constructions.
No product closure or tensor isomorphism is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace KltDP.Geometry

variable (X : Scheme.{u})

-- The module interfaces retain the actual carriers but expose only the
-- forgotten ring structures. Make their original commutative structures
-- explicit for the tensor and multiplication elaborators.
local instance structureSectionCommRing (U : (X.Opens)ᵒᵖ) :
    CommRing (X.ringCatSheaf.val.obj U) :=
  inferInstanceAs (CommRing (X.presheaf.obj U))

local instance structurePresheafMonoidal :
    MonoidalCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.val) :=
  _root_.PresheafOfModules.monoidalCategory (R := X.presheaf)

variable [IsIntegral X]

local instance rationalModuleSectionCommRing (U : (X.Opens)ᵒᵖ) :
    CommRing ((rationalFunctionModule X).val.obj U) :=
  inferInstanceAs (CommRing ((rationalFunctionSheaf X).val.obj U))

/-- Multiplying two actual equations represents the sum of their Cartier sections. -/
theorem cartierGlobalEquation_mul (D E : CartierDivisor X)
    (U : X.Opens) [Nonempty U] (f g : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D)
    (hg : cartierEquationClassHom X U (Additive.ofMul g) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op E) :
    cartierEquationClassHom X U (Additive.ofMul (f * g)) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op (D + E) := by
  change cartierEquationClassHom X U (Additive.ofMul f + Additive.ofMul g) = _
  rw [map_add, hf, hg, map_add]

/-- The product of two principal fractional-module sections has the product equation. -/
theorem mul_mem_principalEquationSubmodule (U : X.Opens) [Nonempty U]
    (f g : X.functionFieldˣ) {s t : X.functionField}
    (hs : s ∈ principalEquationSubmodule X U f)
    (ht : t ∈ principalEquationSubmodule X U g) :
    s * t ∈ principalEquationSubmodule X U (f * g) := by
  obtain ⟨a, ha⟩ := (mem_principalEquationSubmodule_iff X U f s).mp hs
  obtain ⟨b, hb⟩ := (mem_principalEquationSubmodule_iff X U g t).mp ht
  apply (mem_principalEquationSubmodule_iff X U (f * g) (s * t)).mpr
  refine ⟨a * b, ?_⟩
  rw [map_mul, ha, hb, Units.val_mul]
  exact mul_mul_mul_comm (f : X.functionField) s (g : X.functionField) t

/-- Actual products of divisor-module sections lie in the module of the sum divisor. -/
theorem cartierSection_mul_mem (D E : CartierDivisor X) (U : X.Opens)
    (s : cartierSectionSubmodule X D U) (t : cartierSectionSubmodule X E U) :
    s.val * t.val ∈ cartierSectionSubmodule X (D + E) U := by
  apply cartierDivisorPresheafSubmodule_isSheaf X (D + E)
  intro x hx
  obtain ⟨V, i, hxV, f, g, hf, hg⟩ :=
    exists_common_cartier_equations X D E U x hx
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hs := s.property V i inferInstance f hf
  have ht := t.property V i inferInstance g hg
  refine ⟨V, i, ?_, hxV⟩
  change (rationalFunctionModule X).val.map i.op (s.val * t.val) ∈
    cartierSectionSubmodule X (D + E) V
  apply (mem_cartierSectionSubmodule_iff X (D + E) V (f * g)
    (cartierGlobalEquation_mul X D E V f g hf hg) _).mpr
  change (rationalFunctionSectionsIso X V).hom
      ((rationalFunctionSheaf X).val.map i.op (s.val * t.val)) ∈
    principalEquationSubmodule X V (f * g)
  rw [map_mul, map_mul]
  exact mul_mem_principalEquationSubmodule X V f g hs ht

/-- Multiplication is the actual product in the rational-function section ring. -/
def cartierSectionMul (D E : CartierDivisor X) (U : X.Opens)
    (s : (cartierDivisorModule X D).val.obj (op U))
    (t : (cartierDivisorModule X E).val.obj (op U)) :
    (cartierDivisorModule X (D + E)).val.obj (op U) :=
  ⟨s.val * t.val, cartierSection_mul_mem X D E U s t⟩

@[simp]
theorem cartierSectionMul_val (D E : CartierDivisor X) (U : X.Opens)
    (s : (cartierDivisorModule X D).val.obj (op U))
    (t : (cartierDivisorModule X E).val.obj (op U)) :
    (cartierSectionMul X D E U s t).val = s.val * t.val := rfl

/-- The actual bilinear product induces the tensor map on one open. -/
def cartierModuleMultiplicationApp (D E : CartierDivisor X) (U : X.Opens) :
    (cartierDivisorModule X D).val.obj (op U) ⊗
        (cartierDivisorModule X E).val.obj (op U) ⟶
      (cartierDivisorModule X (D + E)).val.obj (op U) :=
  ModuleCat.MonoidalCategory.tensorLift (cartierSectionMul X D E U)
    (by
      intro s s' t
      apply Subtype.ext
      exact add_mul s.val s'.val t.val)
    (by
      intro a s t
      apply Subtype.ext
      let a' : (rationalFunctionModule X).val.obj (op U) :=
        (structureToRationalFunctions X).val.app (op U) a
      change (a' * s.val) * t.val = a' * (s.val * t.val)
      exact mul_assoc _ _ _)
    (by
      intro s t t'
      apply Subtype.ext
      exact mul_add s.val t.val t'.val)
    (by
      intro a s t
      apply Subtype.ext
      let a' : (rationalFunctionModule X).val.obj (op U) :=
        (structureToRationalFunctions X).val.app (op U) a
      change s.val * (a' * t.val) = a' * (s.val * t.val)
      exact mul_left_comm _ _ _)

@[simp]
theorem cartierModuleMultiplicationApp_tmul (D E : CartierDivisor X) (U : X.Opens)
    (s : (cartierDivisorModule X D).val.obj (op U))
    (t : (cartierDivisorModule X E).val.obj (op U)) :
    cartierModuleMultiplicationApp X D E U (s ⊗ₜ t) =
      cartierSectionMul X D E U s t := rfl

-- State naturality over the original commutative section rings explicitly,
-- so tensor extensionality does not have to infer them through the sheaf
-- and presheaf monoidal structures at the same time.
-- The actual sheaf-module carriers require additional reduction here.
set_option maxHeartbeats 800000 in
private theorem cartierModuleMultiplicationApp_naturality (D E : CartierDivisor X)
    {U V : (X.Opens)ᵒᵖ} (j : U ⟶ V) :
    (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
      (cartierDivisorModule X D).val (cartierDivisorModule X E).val).map j ≫
        (ModuleCat.restrictScalars (X.presheaf.map j).hom).map
          (cartierModuleMultiplicationApp X D E V.unop) =
      cartierModuleMultiplicationApp X D E U.unop ≫
        (cartierDivisorModule X (D + E)).val.map j := by
  apply ModuleCat.MonoidalCategory.tensor_ext
    (R := X.presheaf.obj U)
    (M₁ := (cartierDivisorModule X D).val.obj U)
    (M₂ := (cartierDivisorModule X E).val.obj U)
    (M₃ := (ModuleCat.restrictScalars (X.presheaf.map j).hom).obj
      ((cartierDivisorModule X (D + E)).val.obj V))
  intro s t
  change cartierModuleMultiplicationApp X D E V.unop
      ((PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
        (cartierDivisorModule X D).val (cartierDivisorModule X E).val).map j
        (s ⊗ₜ t)) =
    (cartierDivisorModule X (D + E)).val.map j
      (cartierModuleMultiplicationApp X D E U.unop (s ⊗ₜ t))
  erw [PresheafOfModules.Monoidal.tensorObj_map_tmul (R := X.presheaf)
    (M₁ := (cartierDivisorModule X D).val) (M₂ := (cartierDivisorModule X E).val) j s t]
  change cartierSectionMul X D E V.unop
      ((cartierDivisorModule X D).val.map j s)
      ((cartierDivisorModule X E).val.map j t) =
    (cartierDivisorModule X (D + E)).val.map j
      (cartierSectionMul X D E U.unop s t)
  apply Subtype.ext
  change (rationalFunctionSheaf X).val.map j s.val *
      (rationalFunctionSheaf X).val.map j t.val =
    (rationalFunctionSheaf X).val.map j (s.val * t.val)
  let s' : (rationalFunctionSheaf X).val.obj U := s.val
  let t' : (rationalFunctionSheaf X).val.obj U := t.val
  exact (((rationalFunctionSheaf X).val.map j).hom.map_mul s' t').symm

set_option maxHeartbeats 800000 in
/-- Multiplication as a morphism from the actual sectionwise presheaf tensor. -/
def cartierModuleMultiplication (D E : CartierDivisor X) :
    (cartierDivisorModule X D).val ⊗ (cartierDivisorModule X E).val ⟶
      (cartierDivisorModule X (D + E)).val where
  app U := cartierModuleMultiplicationApp X D E U.unop
  naturality j := cartierModuleMultiplicationApp_naturality X D E j

/-- The tensor map sends a pure tensor to the actual rational-section product. -/
@[simp]
theorem cartierModuleMultiplication_app_tmul (D E : CartierDivisor X) (U : X.Opens)
    (s : (cartierDivisorModule X D).val.obj (op U))
    (t : (cartierDivisorModule X E).val.obj (op U)) :
    ((cartierModuleMultiplication X D E).app (op U) (s ⊗ₜ t)).val =
      s.val * t.val := rfl

end KltDP.Geometry

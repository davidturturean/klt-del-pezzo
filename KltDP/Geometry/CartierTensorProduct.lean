import KltDP.Geometry.CartierModuleMultiplication
import KltDP.Geometry.CartierPrincipalPicard
import KltDP.Compatibility.SheafificationOnCover

/-!
# The tensor product of the actual Cartier divisor modules

On common equation charts, the existing coordinate maps send `a` to `a/f`
and `b` to `b/g`. Actual rational-section multiplication sends their pure
tensor to `ab/(fg)`. The pinned `TensorProduct.congr` and `TensorProduct.lid`
therefore identify the component map with a linear equivalence. Empty
opens use their actual subsingleton section modules.

The existing covering-sieve criterion then proves that sheafification
inverts the multiplication map. Composing with the established comparison
between sheaf tensor and sheafified presheaf tensor gives the actual
isomorphism `O(D) ⊗ O(E) ≅ O(D+E)` and additivity of its Picard class.
No local bijectivity or tensor compatibility is supplied as an assumption.

Reuse: pinned Mathlib `LinearAlgebra/TensorProduct/Basic.lean`
(`ext'`, `congr`, `congr_tmul`) and `Associator.lean` (`lid`, `lid_tmul`);
the previously reviewed AINT-derived `SheafificationOnCover` and
`SheafModuleMonoidal` supply the sheafification adapters. The Cartier
coordinate compatibility below is proved for the existing actual modules.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X]

local instance cartierTensorStructureSectionCommRing (U : (X.Opens)ᵒᵖ) :
    CommRing (X.ringCatSheaf.val.obj U) :=
  inferInstanceAs (CommRing (X.presheaf.obj U))

local instance cartierTensorStructurePresheafMonoidal :
    MonoidalCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.val) :=
  _root_.PresheafOfModules.monoidalCategory (R := X.presheaf)

/-- Multiplication in the actual local coordinates is `a/f · b/g = ab/(fg)`. -/
theorem cartierSectionMul_equation_coordinates (D E : CartierDivisor X)
    (U : X.Opens) [Nonempty U] (f g : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D)
    (hg : cartierEquationClassHom X U (Additive.ofMul g) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op E)
    (a b : Γ(X, U)) :
    cartierSectionMul X D E U
        (cartierEquationSectionEquiv X D U f hf a)
        (cartierEquationSectionEquiv X E U g hg b) =
      cartierEquationSectionEquiv X (D + E) U (f * g)
        (cartierGlobalEquation_mul X D E U f g hf hg) (a * b) := by
  apply Subtype.ext
  apply (rationalFunctionModuleSectionsEquiv X U).injective
  change (rationalFunctionSectionsIso X U).hom.hom
      (@Mul.mul ((rationalFunctionSheaf X).val.obj (op U)) inferInstance
        (cartierEquationSectionEquiv X D U f hf a).val
        (cartierEquationSectionEquiv X E U g hg b).val) = _
  refine ((rationalFunctionSectionsIso X U).hom.hom.map_mul
    (cartierEquationSectionEquiv X D U f hf a).val
    (cartierEquationSectionEquiv X E U g hg b).val).trans ?_
  change rationalFunctionModuleSectionsEquiv X U
        (cartierEquationSectionEquiv X D U f hf a).val *
      rationalFunctionModuleSectionsEquiv X U
        (cartierEquationSectionEquiv X E U g hg b).val = _
  rw [cartierEquationSectionEquiv_apply_field,
    cartierEquationSectionEquiv_apply_field, cartierEquationSectionEquiv_apply_field]
  change (X.germToFunctionField U).hom a * (↑(f⁻¹) : X.functionField) *
      ((X.germToFunctionField U).hom b * (↑(g⁻¹) : X.functionField)) =
    (X.germToFunctionField U).hom (a * b) * (↑((f * g)⁻¹) : X.functionField)
  simp only [map_mul, mul_inv_rev, Units.val_mul]
  ring

/-- On a nonempty common equation chart, the original multiplication
component is bijective, by the actual tensor product of coordinate maps. -/
theorem cartierModuleMultiplicationApp_bijective_of_equations (D E : CartierDivisor X)
    (U : X.Opens) [Nonempty U] (f g : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D)
    (hg : cartierEquationClassHom X U (Additive.ofMul g) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op E) :
    Function.Bijective (cartierModuleMultiplicationApp X D E U) := by
  let eD := cartierEquationSectionEquiv X D U f hf
  let eE := cartierEquationSectionEquiv X E U g hg
  let eSum := cartierEquationSectionEquiv X (D + E) U (f * g)
    (cartierGlobalEquation_mul X D E U f g hf hg)
  let e := TensorProduct.congr eD.symm eE.symm ≪≫ₗ
    TensorProduct.lid Γ(X, U) Γ(X, U) ≪≫ₗ eSum
  have he : (cartierModuleMultiplicationApp X D E U).hom = e.toLinearMap := by
    apply TensorProduct.ext'
    intro s t
    obtain ⟨a, rfl⟩ := eD.surjective s
    obtain ⟨b, rfl⟩ := eE.surjective t
    change cartierSectionMul X D E U (eD a) (eE b) = e (eD a ⊗ₜ eE b)
    simp only [e, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
      LinearEquiv.symm_apply_apply, TensorProduct.lid_tmul, smul_eq_mul]
    exact cartierSectionMul_equation_coordinates X D E U f g hf hg a b
  change Function.Bijective (cartierModuleMultiplicationApp X D E U).hom
  rw [he]
  exact e.bijective

/-- Pairwise intersections of the proved equation atlases cover the scheme. -/
theorem commonCartierEquationCharts_coversTop (D E : CartierDivisor X) :
    (Opens.grothendieckTopology X).CoversTop
      (fun c : CartierEquationChart X D × CartierEquationChart X E =>
        c.1.openSet ⊓ c.2.openSet) := by
  intro U x hx
  obtain ⟨V, i, hxV, f, g, hf, hg⟩ :=
    exists_common_cartier_equations X D E U x hx
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  let cD : CartierEquationChart X D := {
    openSet := V
    nonempty := inferInstance
    equation := f
    represents := hf }
  let cE : CartierEquationChart X E := {
    openSet := V
    nonempty := inferInstance
    equation := g
    represents := hg }
  refine ⟨V, i, ?_, hxV⟩
  exact ⟨(cD, cE), ⟨homOfLE (le_inf le_rfl le_rfl)⟩⟩

/-- Multiplication is inverted by sheafification because its actual
components are bijective on every subopen of a common equation chart. -/
theorem cartierModuleMultiplication_mem_sheafificationW (D E : CartierDivisor X) :
    PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.val)
      (cartierModuleMultiplication X D E) := by
  apply PresheafOfModules.sheafificationW_of_bijective_on_coversTop
    (cartierModuleMultiplication X D E)
    (fun c : CartierEquationChart X D × CartierEquationChart X E =>
      c.1.openSet ⊓ c.2.openSet) (commonCartierEquationCharts_coversTop X D E)
  intro c V i
  classical
  by_cases hV : Nonempty V
  · letI := hV
    exact cartierModuleMultiplicationApp_bijective_of_equations X D E V
      c.1.equation c.2.equation
      (cartierGlobalEquation_restrict X D
        (homOfLE (i.le.trans inf_le_left)) c.1.equation c.1.represents)
      (cartierGlobalEquation_restrict X E
        (homOfLE (i.le.trans inf_le_right)) c.2.equation c.2.represents)
  · have hbot : V = ⊥ := by
      apply SetLike.ext
      intro x
      exact ⟨fun hx => (hV ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
    subst V
    letI : Subsingleton Γ(X, ⊥) :=
      CommRingCat.subsingleton_of_isTerminal X.sheaf.isTerminalOfEmpty
    letI : Subsingleton (X.ringCatSheaf.val.obj (op ⊥)) :=
      inferInstanceAs (Subsingleton Γ(X, ⊥))
    letI : Subsingleton
        (((cartierDivisorModule X D).val.obj (op ⊥) ⊗
          (cartierDivisorModule X E).val.obj (op ⊥)) :
          ModuleCat (X.ringCatSheaf.val.obj (op ⊥))) :=
      Module.subsingleton (X.ringCatSheaf.val.obj (op ⊥)) _
    letI : Subsingleton ((cartierDivisorModule X (D + E)).val.obj (op ⊥)) :=
      Module.subsingleton Γ(X, ⊥) _
    change Function.Bijective
      (cartierModuleMultiplicationApp X D E ⊥).hom
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

/-- The sheafified original multiplication, followed by the existing
sheafification counit, has target the actual module O(D+E). -/
def cartierModuleMultiplicationSheafified (D E : CartierDivisor X) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj
        ((cartierDivisorModule X D).val ⊗ (cartierDivisorModule X E).val) ⟶
      cartierDivisorModule X (D + E) :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map
      (cartierModuleMultiplication X D E) ≫
    (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf
      (cartierDivisorModule X (D + E))).hom

/-- The local coordinate calculation proves the actual sheafified
multiplication is an isomorphism. -/
theorem isIso_cartierModuleMultiplicationSheafified (D E : CartierDivisor X) :
    IsIso (cartierModuleMultiplicationSheafified X D E) := by
  haveI : IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map
      (cartierModuleMultiplication X D E)) :=
    (PresheafOfModules.sheafificationW_iff (𝟙 X.ringCatSheaf.val)
      (cartierModuleMultiplication X D E)).mp
        (cartierModuleMultiplication_mem_sheafificationW X D E)
  unfold cartierModuleMultiplicationSheafified
  infer_instance

/-- Actual multiplication on the tensor in the category of module sheaves. -/
def cartierTensorMultiplication (D E : CartierDivisor X) :
    letI := Scheme.Modules.monoidalCategory X
    cartierDivisorModule X D ⊗ cartierDivisorModule X E ⟶
      cartierDivisorModule X (D + E) := by
  letI := Scheme.Modules.monoidalCategory X
  exact (PresheafOfModules.sheafTensorIsoSheafification X.sheaf.val
      X.ringCatSheaf.cond (cartierDivisorModule X D) (cartierDivisorModule X E)).hom ≫
    cartierModuleMultiplicationSheafified X D E

/-- Multiplication identifies O(D) tensor O(E) with the actual O(D+E). -/
def cartierTensorIso (D E : CartierDivisor X) :
    letI := Scheme.Modules.monoidalCategory X
    cartierDivisorModule X D ⊗ cartierDivisorModule X E ≅
      cartierDivisorModule X (D + E) := by
  letI := Scheme.Modules.monoidalCategory X
  letI := isIso_cartierModuleMultiplicationSheafified X D E
  exact PresheafOfModules.sheafTensorIsoSheafification X.sheaf.val
    X.ringCatSheaf.cond (cartierDivisorModule X D) (cartierDivisorModule X E) ≪≫
      asIso (cartierModuleMultiplicationSheafified X D E)

/-- The constructed tensor isomorphism has the original multiplication
as its forward map, through the established sheaf tensor comparison. -/
@[simp]
theorem cartierTensorIso_hom (D E : CartierDivisor X) :
    letI := Scheme.Modules.monoidalCategory X
    (cartierTensorIso X D E).hom = cartierTensorMultiplication X D E := rfl

/-- Addition of actual Cartier divisors becomes multiplication in the
actual Picard group because of the proved sheaf tensor isomorphism. -/
theorem cartierPicardClass_add (D E : CartierDivisor X) :
    cartierPicardClass X (D + E) = cartierPicardClass X D * cartierPicardClass X E := by
  letI := Scheme.Modules.monoidalCategory X
  apply Units.ext
  change (cartierPicardClass X (D + E) : Skeleton X.Modules) =
    (cartierPicardClass X D : Skeleton X.Modules) *
      (cartierPicardClass X E : Skeleton X.Modules)
  rw [cartierPicardClass_val, cartierPicardClass_val, cartierPicardClass_val,
    ← Skeleton.toSkeleton_tensorObj]
  exact Quotient.sound ⟨(cartierTensorIso X D E).symm⟩

end KltDP.Geometry

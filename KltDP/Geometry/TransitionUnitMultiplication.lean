import KltDP.Geometry.TransitionUnitSheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# Products of actual transition-unit sections

Multiplying the transition units multiplies the corresponding matching
equations. Componentwise multiplication of the original structure-sheaf
sections is bilinear over the original section ring and commutes with
restriction. It therefore induces a morphism from the sectionwise
presheaf tensor to the module presheaf for the product transition units.

The construction follows the existing CartierModuleMultiplication tensor
map, using the pinned tensor universal property. No cocycle or cover is
needed for this morphism. The product cocycle law is proved separately;
the actual sheaf tensor isomorphism is constructed in TransitionUnitTensor.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace KltDP.Geometry.TransitionUnitGluing

variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
  (g h : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ)

/-- The product of the original transition units on each actual overlap. -/
def productUnits (i j : ι) : Γ(X, U i ⊓ U j)ˣ := g i j * h i j

@[simp]
theorem productUnits_val (i j : ι) :
    (productUnits X U g h i j : Γ(X, U i ⊓ U j)) =
      (g i j : Γ(X, U i ⊓ U j)) * (h i j : Γ(X, U i ⊓ U j)) := rfl

/-- Products preserve the actual normalization and triple-overlap equations. -/
theorem productUnits_isCocycle (hg : IsCocycle X U g) (hh : IsCocycle X U h) :
    IsCocycle X U (productUnits X U g h) where
  unit_self i := by
    rw [productUnits_val, hg.unit_self i, hh.unit_self i, one_mul]
  mul_res i j l := by
    simp only [productUnits_val, map_mul]
    rw [mul_mul_mul_comm, hg.mul_res i j l, hh.mul_res i j l]

/-- Products of matching families satisfy the product transition equations. -/
theorem sectionMul_mem (W : X.Opens)
    (s : sections X U g W) (t : sections X U h W) :
    (fun i => s.val i * t.val i) ∈ sections X U (productUnits X U g h) W := by
  intro i j
  change res X _ (s.val i * t.val i) =
    res X _ (productUnits X U g h i j : Γ(X, U i ⊓ U j)) *
      res X _ (s.val j * t.val j)
  rw [productUnits_val, map_mul, map_mul, map_mul, s.property i j, t.property i j]
  exact mul_mul_mul_comm _ _ _ _

/-- The original componentwise section product, bilinear over O(W). -/
def sectionMul (W : X.Opens) :
    sections X U g W →ₗ[Γ(X, W)] sections X U h W →ₗ[Γ(X, W)]
      sections X U (productUnits X U g h) W where
  toFun s :=
    { toFun := fun t => ⟨fun i => s.val i * t.val i, sectionMul_mem X U g h W s t⟩
      map_add' := by
        intro t t'
        apply Subtype.ext
        funext i
        exact mul_add (s.val i) (t.val i) (t'.val i)
      map_smul' := by
        intro a t
        apply Subtype.ext
        funext i
        change s.val i * (res X (inf_le_left : W ⊓ U i ≤ W) a * t.val i) =
          res X (inf_le_left : W ⊓ U i ≤ W) a * (s.val i * t.val i)
        exact mul_left_comm _ _ _ }
  map_add' := by
    intro s s'
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    funext i
    exact add_mul (s.val i) (s'.val i) (t.val i)
  map_smul' := by
    intro a s
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    funext i
    change (res X (inf_le_left : W ⊓ U i ≤ W) a * s.val i) * t.val i =
      res X (inf_le_left : W ⊓ U i ≤ W) a * (s.val i * t.val i)
    exact mul_assoc _ _ _

@[simp]
theorem sectionMul_val (W : X.Opens)
    (s : sections X U g W) (t : sections X U h W) (i : ι) :
    (sectionMul X U g h W s t).val i = s.val i * t.val i := rfl

/-- The bilinear product commutes with the original component restrictions. -/
theorem sectionMul_restrict {V W : X.Opens} (hVW : V ≤ W)
    (s : sections X U g W) (t : sections X U h W) :
    sectionMul X U g h V (restrict X U g hVW s) (restrict X U h hVW t) =
      restrict X U (productUnits X U g h) hVW (sectionMul X U g h W s t) := by
  apply Subtype.ext
  funext i
  exact (map_mul (res X (inf_le_inf_right (U i) hVW)) (s.val i) (t.val i)).symm

-- Keep the original commutative section rings explicit when working with
-- the forgotten RingCat-valued module interfaces and their chosen tensor.
local instance multiplicationSectionCommRing (W : (X.Opens)ᵒᵖ) :
    CommRing (X.ringCatSheaf.val.obj W) :=
  inferInstanceAs (CommRing (X.presheaf.obj W))

local instance multiplicationPresheafMonoidal :
    MonoidalCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.val) :=
  _root_.PresheafOfModules.monoidalCategory (R := X.presheaf)

local instance multiplicationAdditiveModule
    (q : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ) (W : (X.Opens)ᵒᵖ) :
    Module (X.ringCatSheaf.val.obj W) ((additivePresheaf X U q).obj W) :=
  inferInstanceAs (Module Γ(X, W.unop) (sections X U q W.unop))

/-- The tensor universal property applied to the actual bilinear section product. -/
def multiplicationApp (W : X.Opens) :
    (moduleSheaf X U g).val.obj (op W) ⊗
        (moduleSheaf X U h).val.obj (op W) ⟶
      (moduleSheaf X U (productUnits X U g h)).val.obj (op W) :=
  ModuleCat.ofHom (TensorProduct.lift (sectionMul X U g h W))

@[simp]
theorem multiplicationApp_tmul (W : X.Opens)
    (s : sections X U g W) (t : sections X U h W) :
    multiplicationApp X U g h W (s ⊗ₜ t) = sectionMul X U g h W s t := rfl

-- State all scalar rings in this naturality comparison explicitly. The
-- two factors restrict semilinearly along the original ring restriction.
private theorem multiplicationApp_naturality
    {V W : (X.Opens)ᵒᵖ} (j : V ⟶ W) :
    (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
      (moduleSheaf X U g).val (moduleSheaf X U h).val).map j ≫
        (ModuleCat.restrictScalars (X.presheaf.map j).hom).map
          (multiplicationApp X U g h W.unop) =
      multiplicationApp X U g h V.unop ≫
        (moduleSheaf X U (productUnits X U g h)).val.map j := by
  apply ModuleCat.MonoidalCategory.tensor_ext
    (R := X.presheaf.obj V)
    (M₁ := (moduleSheaf X U g).val.obj V)
    (M₂ := (moduleSheaf X U h).val.obj V)
    (M₃ := (ModuleCat.restrictScalars (X.presheaf.map j).hom).obj
      ((moduleSheaf X U (productUnits X U g h)).val.obj W))
  intro s t
  change multiplicationApp X U g h W.unop
      ((PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
        (moduleSheaf X U g).val (moduleSheaf X U h).val).map j (s ⊗ₜ t)) =
    (moduleSheaf X U (productUnits X U g h)).val.map j
      (multiplicationApp X U g h V.unop (s ⊗ₜ t))
  erw [PresheafOfModules.Monoidal.tensorObj_map_tmul (R := X.presheaf)
    (M₁ := (moduleSheaf X U g).val) (M₂ := (moduleSheaf X U h).val) j s t]
  change sectionMul X U g h W.unop
      (restrict X U g j.unop.le s) (restrict X U h j.unop.le t) =
    restrict X U (productUnits X U g h) j.unop.le (sectionMul X U g h V.unop s t)
  exact sectionMul_restrict X U g h j.unop.le s t

/-- The actual product morphism from the sectionwise presheaf tensor. -/
def multiplication :
    (moduleSheaf X U g).val ⊗ (moduleSheaf X U h).val ⟶
      (moduleSheaf X U (productUnits X U g h)).val where
  app W := multiplicationApp X U g h W.unop
  naturality j := multiplicationApp_naturality X U g h j

/-- Each component of a pure tensor maps to the original product of sections. -/
@[simp]
theorem multiplication_app_tmul (W : X.Opens)
    (s : sections X U g W) (t : sections X U h W) (i : ι) :
    ((multiplication X U g h).app (op W) (s ⊗ₜ t)).val i = s.val i * t.val i := rfl

end KltDP.Geometry.TransitionUnitGluing

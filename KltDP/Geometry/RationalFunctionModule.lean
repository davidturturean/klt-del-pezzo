import KltDP.Geometry.RationalFunctionSheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-!
# The actual module sheaf of rational functions

The rational-function sheaf is first regarded as a sheaf of rings. Its
unit module is then restricted along the actual structure-sheaf map.
Thus the scalar action is precisely multiplication by the image of a
regular function, including on the empty open.

This adapter reuses pinned `sheafCompose`, `SheafOfModules.restrictScalars`,
`SheafOfModules.unit`, and `PresheafOfModules.homMk`. The inclusion of
regular functions and the comparison with the original function field
come from the already constructed ring-sheaf maps. No module gluing or
Cartier-to-Picard comparison is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

variable (X : Scheme.{u}) [IsIntegral X]

/-- The actual rational-function sheaf, with only its ring structure retained. -/
def rationalFunctionRingSheaf : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose _ (forget₂ CommRingCat RingCat)).obj (rationalFunctionSheaf X)

/-- The canonical map of ring sheaves used for restriction of scalars. -/
def structureToRationalFunctionRings : X.ringCatSheaf ⟶ rationalFunctionRingSheaf X :=
  (sheafCompose _ (forget₂ CommRingCat RingCat)).map (structureToRationalFunctions X)

/-- Rational functions as an actual module sheaf over the original structure sheaf. -/
def rationalFunctionModule : X.Modules :=
  (_root_.SheafOfModules.restrictScalars (structureToRationalFunctionRings X)).obj
    (_root_.SheafOfModules.unit (rationalFunctionRingSheaf X))

/-- Its sections are definitionally the actual rational-function sections. -/
theorem rationalFunctionModule_obj_coe (U : X.Opens) :
    ((rationalFunctionModule X).val.obj (op U) : Type u) =
      (rationalFunctionSheaf X).val.obj (op U) := rfl

@[simp]
theorem rationalFunctionModule_map_apply {U V : X.Opens} (i : V ⟶ U)
    (s : (rationalFunctionModule X).val.obj (op U)) :
    (rationalFunctionModule X).val.map i.op s =
      (rationalFunctionSheaf X).val.map i.op s := rfl

/-- The module action is multiplication by the actual structural image. -/
theorem rationalFunctionModule_smul (U : X.Opens) (a : Γ(X, U))
    (s : (rationalFunctionModule X).val.obj (op U)) :
    a • s = @Mul.mul ((rationalFunctionSheaf X).val.obj (op U)) inferInstance
      ((structureToRationalFunctions X).val.app (op U) a) s := rfl

/-- The actual inclusion of the structure sheaf's unit module into rational functions. -/
def structureToRationalFunctionModule :
    _root_.SheafOfModules.unit X.ringCatSheaf ⟶ rationalFunctionModule X :=
  _root_.SheafOfModules.Hom.mk <|
    _root_.PresheafOfModules.homMk
      (whiskerRight (structureToRationalFunctionRings X).val
        (forget₂ RingCat AddCommGrp))
      (fun U a b => ((structureToRationalFunctionRings X).val.app U).hom.map_mul a b)

@[simp]
theorem structureToRationalFunctionModule_app (U : X.Opens) (a : Γ(X, U)) :
    (structureToRationalFunctionModule X).val.app (op U) a =
      (structureToRationalFunctions X).val.app (op U) a := rfl

/-- The inclusion is injective on every open, including the empty open. -/
theorem structureToRationalFunctionModule_app_injective (U : X.Opens) :
    Function.Injective ((structureToRationalFunctionModule X).val.app (op U)) :=
  structureToRationalFunctions_app_injective X U

/-- On a nonempty open, the actual module of rational sections is the original
function field as a module over the ring of regular sections. -/
def rationalFunctionModuleSectionsEquiv (U : X.Opens) [Nonempty U] :
    (rationalFunctionModule X).val.obj (op U) ≃ₗ[Γ(X, U)] X.functionField where
  toFun := (rationalFunctionSectionsIso X U).hom
  invFun := (rationalFunctionSectionsIso X U).inv
  left_inv s := ConcreteCategory.congr_hom (rationalFunctionSectionsIso X U).hom_inv_id s
  right_inv s := ConcreteCategory.congr_hom (rationalFunctionSectionsIso X U).inv_hom_id s
  map_add' := (rationalFunctionSectionsIso X U).hom.hom.map_add
  map_smul' a s := by
    change (rationalFunctionSectionsIso X U).hom.hom
        (@Mul.mul ((rationalFunctionSheaf X).val.obj (op U)) inferInstance
          ((structureToRationalFunctions X).val.app (op U) a) s) =
      algebraMap Γ(X, U) X.functionField a * (rationalFunctionSectionsIso X U).hom s
    exact ((rationalFunctionSectionsIso X U).hom.hom.map_mul
      ((structureToRationalFunctions X).val.app (op U) a) s).trans
        (congrArg (fun b : X.functionField => b * (rationalFunctionSectionsIso X U).hom s)
          (ConcreteCategory.congr_hom (structureToRationalFunctions_app_comp_sectionsIso X U) a))

@[simp]
theorem rationalFunctionModuleSectionsEquiv_apply (U : X.Opens) [Nonempty U]
    (s : (rationalFunctionModule X).val.obj (op U)) :
    rationalFunctionModuleSectionsEquiv X U s = (rationalFunctionSectionsIso X U).hom s := rfl

/-- The linear comparison sends a regular function to its canonical field image. -/
theorem rationalFunctionModuleSectionsEquiv_structure (U : X.Opens) [Nonempty U]
    (a : Γ(X, U)) :
    rationalFunctionModuleSectionsEquiv X U
        ((structureToRationalFunctionModule X).val.app (op U) a) =
      algebraMap Γ(X, U) X.functionField a :=
  ConcreteCategory.congr_hom (structureToRationalFunctions_app_comp_sectionsIso X U) a

/-- Restriction between nonempty opens preserves the represented rational function. -/
theorem rationalFunctionModuleSectionsEquiv_naturality
    {U V : X.Opens} [Nonempty U] [Nonempty V] (i : V ⟶ U)
    (s : (rationalFunctionModule X).val.obj (op U)) :
    rationalFunctionModuleSectionsEquiv X V ((rationalFunctionModule X).val.map i.op s) =
      rationalFunctionModuleSectionsEquiv X U s :=
  ConcreteCategory.congr_hom (rationalFunctionSectionsIso_naturality X i.le) s

end KltDP.Geometry

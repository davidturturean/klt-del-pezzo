import KltDP.Geometry.SchemeExteriorPower
import KltDP.Geometry.SheafPicard
import KltDP.LinearAlgebra.SplitConormalDeterminant
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# The original ordered tensor-to-exterior map of two sheaves

On each open, the map sends a pure tensor to the wedge of the two original
biproduct inclusions. Original restriction naturality makes this a presheaf
map. Sheafification produces a map from the existing sheaf tensor to the
existing exterior-square sheaf. No local frame or invertibility is part of
the definition.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct

universe u

namespace KltDP.Geometry.ProjectiveProductCanonicalExteriorMap

open KltDP.LinearAlgebra.SplitConormalDeterminant

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} (L M : X.Modules)

local instance exteriorMonoidal : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

abbrev tensorPresheaf : X.PresheafOfModules :=
  _root_.PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.val) L.val M.val

private theorem leftWedge_add {A : Type u} [CommRing A]
    {E : Type u} [AddCommGroup E] [Module A E] (x y z : E) :
    leftWedge (R := A) (x + y) z = leftWedge x z + leftWedge y z := by
  change exteriorPower.ιMulti A 2 (Matrix.vecCons (x + y) (fun _ => z)) =
    exteriorPower.ιMulti A 2 (Matrix.vecCons x (fun _ => z)) +
      exteriorPower.ιMulti A 2 (Matrix.vecCons y (fun _ => z))
  exact (exteriorPower.ιMulti A 2).map_vecCons_add (fun _ => z) x y

private def nativeBilinear {A : Type u} [CommRing A]
    (P Q E : ModuleCat.{u} A) (f : P ⟶ E) (g : Q ⟶ E) :
    P →ₗ[A] Q →ₗ[A] E.exteriorPower 2 where
  toFun x := (leftWedge (f x)).comp g.hom
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change leftWedge (f (x + y)) (g z) = _
    rw [map_add, leftWedge_add]
    rfl
  map_smul' r x := by
    apply LinearMap.ext
    intro z
    change leftWedge (f (r • x)) (g z) = _
    rw [map_smul, leftWedge_smul_apply]
    rfl

local instance tensorWedgeRingObjCommRing {C : Type u} [Category.{u} C]
    (R : Cᵒᵖ ⥤ CommRingCat.{u}) (U : Cᵒᵖ) :
    CommRing ((R ⋙ forget₂ CommRingCat RingCat).obj U) :=
  inferInstanceAs (CommRing (R.obj U))

private def nativeSectionsMap {C : Type u} [Category.{u} C]
    (R : Cᵒᵖ ⥤ CommRingCat.{u})
    (P Q E : _root_.PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (f : P ⟶ E) (g : Q ⟶ E) (U : Cᵒᵖ) :
    (_root_.PresheafOfModules.Monoidal.tensorObj (R := R) P Q).obj U ⟶
      (KltDP.Compatibility.ExteriorPowerPresheaf.presheaf R E 2).obj U :=
  ModuleCat.ofHom (TensorProduct.lift
    (nativeBilinear (P.obj U) (Q.obj U) (E.obj U) (f.app U) (g.app U)))

private theorem nativeSectionsMap_tmul {C : Type u} [Category.{u} C]
    (R : Cᵒᵖ ⥤ CommRingCat.{u})
    (P Q E : _root_.PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (f : P ⟶ E) (g : Q ⟶ E) (U : Cᵒᵖ) (x : P.obj U) (y : Q.obj U) :
    nativeSectionsMap R P Q E f g U (x ⊗ₜ[R.obj U] y) =
      exteriorPower.ιMulti (R.obj U) 2 ![f.app U x, g.app U y] :=
  leftWedge_apply _ _

private theorem tensor_wedge_naturality {C : Type u} [Category.{u} C]
    (R : Cᵒᵖ ⥤ CommRingCat.{u})
    (P Q E : _root_.PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (f : P ⟶ E) (g : Q ⟶ E)
    (a : ∀ U : Cᵒᵖ,
      (_root_.PresheafOfModules.Monoidal.tensorObj (R := R) P Q).obj U ⟶
        (KltDP.Compatibility.ExteriorPowerPresheaf.presheaf R E 2).obj U)
    (ha : ∀ (U : Cᵒᵖ) (x : P.obj U) (y : Q.obj U),
      a U (x ⊗ₜ[R.obj U] y) =
        exteriorPower.ιMulti (R.obj U) 2 ![f.app U x, g.app U y])
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    (_root_.PresheafOfModules.Monoidal.tensorObj (R := R) P Q).map i ≫
        (ModuleCat.restrictScalars (R.map i).hom).map (a V) =
      a U ≫ (KltDP.Compatibility.ExteriorPowerPresheaf.presheaf R E 2).map i := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  change a V
      ((_root_.PresheafOfModules.Monoidal.tensorObj (R := R) P Q).map i
        (x ⊗ₜ[R.obj U] y)) =
    (KltDP.Compatibility.ExteriorPowerPresheaf.presheaf R E 2).map i
      (a U (x ⊗ₜ[R.obj U] y))
  erw [_root_.PresheafOfModules.Monoidal.tensorObj_map_tmul, ha, ha,
    KltDP.Compatibility.ExteriorPowerPresheaf.presheaf_map_mk]
  congr 1
  funext j
  fin_cases j
  · exact _root_.PresheafOfModules.naturality_apply f i x
  · exact _root_.PresheafOfModules.naturality_apply g i y

private def nativePresheafMap {C : Type u} [Category.{u} C]
    (R : Cᵒᵖ ⥤ CommRingCat.{u})
    (P Q E : _root_.PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (f : P ⟶ E) (g : Q ⟶ E) :
    _root_.PresheafOfModules.Monoidal.tensorObj (R := R) P Q ⟶
      KltDP.Compatibility.ExteriorPowerPresheaf.presheaf R E 2 where
  app U := nativeSectionsMap R P Q E f g U
  naturality {U V} i :=
    tensor_wedge_naturality R P Q E f g (nativeSectionsMap R P Q E f g)
      (nativeSectionsMap_tmul R P Q E f g) i

/-- The bilinear ordered wedge of the original sheaf biproduct inclusions. -/
def sectionsBilinear (U : X.Opens) :
    (L.val.obj (op U)) →ₗ[Γ(X, U)] (M.val.obj (op U)) →ₗ[Γ(X, U)]
      ((SchemeExteriorPower.presheaf (L ⊞ M) 2).obj (op U)) :=
  nativeBilinear (A := Γ(X, U))
    (L.val.obj (op U)) (M.val.obj (op U)) ((L ⊞ M).val.obj (op U))
    ((biprod.inl : L ⟶ L ⊞ M).val.app (op U))
    ((biprod.inr : M ⟶ L ⊞ M).val.app (op U))

/-- The actual sectionwise tensor-to-exterior map. -/
def sectionsMap (U : X.Opens) :
    (tensorPresheaf L M).obj (op U) ⟶
      (SchemeExteriorPower.presheaf (L ⊞ M) 2).obj (op U) :=
  nativeSectionsMap X.presheaf L.val M.val (L ⊞ M).val
    (biprod.inl : L ⟶ L ⊞ M).val (biprod.inr : M ⟶ L ⊞ M).val (op U)

theorem sectionsMap_tmul (U : X.Opens)
    (x : L.val.obj (op U)) (y : M.val.obj (op U)) :
    sectionsMap L M U (x ⊗ₜ[Γ(X, U)] y) =
      exteriorPower.ιMulti Γ(X, U) 2
        ![(biprod.inl : L ⟶ L ⊞ M).val.app (op U) x,
          (biprod.inr : M ⟶ L ⊞ M).val.app (op U) y] :=
  leftWedge_apply _ _

/-- The ordered wedge commutes with the original restrictions, before sheafification. -/
def presheafMap : tensorPresheaf L M ⟶ SchemeExteriorPower.presheaf (L ⊞ M) 2 :=
  nativePresheafMap X.presheaf L.val M.val (L ⊞ M).val
    (biprod.inl : L ⟶ L ⊞ M).val (biprod.inr : M ⟶ L ⊞ M).val

/-- The existing sheaf tensor is the sheafification of its original tensor presheaf. -/
def tensorIso : L ⊗ M ≅
    (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj
      (tensorPresheaf L M) :=
  _root_.PresheafOfModules.sheafTensorIsoSheafification
    X.sheaf.val X.ringCatSheaf.cond L M

/-- The actual ordered tensor-to-exterior-square map of the original module sheaves. -/
def map : L ⊗ M ⟶ SchemeExteriorPower.sheaf (L ⊞ M) 2 :=
  (tensorIso L M).hom ≫
    (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map
      (presheafMap L M)

end KltDP.Geometry.ProjectiveProductCanonicalExteriorMap

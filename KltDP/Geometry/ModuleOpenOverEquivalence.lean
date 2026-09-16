/-
Original project adapter for the existing open-subscheme module functor.
Released under Apache 2.0; see
docs/reuse_sources/module_sheaf_equivalence/sources/LICENSE.
-/
import KltDP.Compatibility.ModuleSheafEquivalence
import KltDP.Compatibility.SheafGeneratingSectionsMap
import KltDP.Geometry.ModuleOpenOver
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# The actual open-subscheme and Over-site module equivalence

The forward functor is the existing `openToOverFunctor U`, with exactly
the original structure map of `U.ι`. That ring-sheaf map is proved an
isomorphism on every actual subopen. The equivalence of module categories
then supplies actual finite-free and kernel comparisons. In particular,
an arbitrary finite-free-to-unit morphism on the original Over site is
recovered from an actual morphism on the open subscheme, with the original
kernel inclusion preserved. No surjectivity premise on that morphism,
Noetherianity, or coherence assertion enters this transport adapter.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} (U : X.Opens)

local instance : Functor.IsContinuous.{u} U.overEquivalence.functor
    ((Opens.grothendieckTopology X).over U)
    (Opens.grothendieckTopology U.toScheme) := by
  let J := (Opens.grothendieckTopology X).over U
  let K := Opens.grothendieckTopology U.toScheme
  let F := U.overEquivalence.functor
  letI : F.IsDenseSubsite J K := Opens.overEquivalence_isDenseSubsite U
  letI := Functor.IsDenseSubsite.isCoverDense J K F
  letI := Functor.IsDenseSubsite.isLocallyFull J K F
  letI := Functor.IsDenseSubsite.isLocallyFaithful J K F
  exact Functor.IsCoverDense.isContinuous J K F
    (Functor.IsDenseSubsite.coverPreserving J K F)

local instance : Functor.IsContinuous.{u} U.overEquivalence.inverse
    (Opens.grothendieckTopology U.toScheme)
    ((Opens.grothendieckTopology X).over U) := by
  let J := (Opens.grothendieckTopology X).over U
  let K := Opens.grothendieckTopology U.toScheme
  letI : U.overEquivalence.symm.inverse.IsDenseSubsite J K :=
    Opens.overEquivalence_isDenseSubsite U
  exact inferInstanceAs (Functor.IsContinuous.{u} U.overEquivalence.symm.functor K J)

/-- Each component is the original section-ring isomorphism of the open
immersion, so the actual scalar map is an isomorphism of ring sheaves. -/
instance openToOverRingSheafHom_isIso : IsIso (openToOverRingSheafHom U) := by
  haveI (V : (Over U)ᵒᵖ) : IsIso ((openToOverRingSheafHom U).val.app V) := by
    haveI : IsIso (U.ι.app V.unop.left) :=
      Scheme.Hom.isIso_app U.ι V.unop.left (by simpa using V.unop.hom.le)
    change IsIso ((forget₂ CommRingCat RingCat).map (U.ι.app V.unop.left))
    infer_instance
  haveI : IsIso ((sheafToPresheaf ((Opens.grothendieckTopology X).over U)
      RingCat.{u}).map (openToOverRingSheafHom U)) := by
    change IsIso (openToOverRingSheafHom U).val
    exact NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso _
    (sheafToPresheaf ((Opens.grothendieckTopology X).over U) RingCat.{u})

/-- The original functor from modules on the actual open subscheme to
modules on the actual Over site is an equivalence. -/
def openToOverEquivalence : U.toScheme.Modules ≌
    _root_.SheafOfModules.{u} (X.ringCatSheaf.over U) :=
  KltDP.SheafModuleEquivalence.pushforwardEquivalence U.overEquivalence
    (openToOverRingSheafHom U)

@[simp]
theorem openToOverEquivalence_functor :
    (openToOverEquivalence U).functor = openToOverFunctor U := rfl

instance openToOverFunctor_isEquivalence : (openToOverFunctor U).IsEquivalence :=
  (openToOverEquivalence U).isEquivalence_functor

/-- The comparison uses the original coproduct free sheaves and the
already-proved original unit section maps. -/
def openToOverFreeIso (I : Type u) :
    _root_.SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅
      (openToOverFunctor U).obj
        (_root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) I) :=
  _root_.SheafOfModules.mapFreeIso (openToOverFunctor U) I (openToOverUnitIso U)

local instance : (openToOverFunctor U).PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩

/-- Kernel preservation for this actual equivalence uses the original
categorical kernel comparison. -/
def openToOverKernelIso {M N : U.toScheme.Modules} (φ : M ⟶ N) :
    (openToOverFunctor U).obj (kernel φ) ≅ kernel ((openToOverFunctor U).map φ) :=
  PreservesKernel.iso (openToOverFunctor U) φ

/-- The kernel isomorphism preserves its actual inclusion. -/
theorem openToOverKernelIso_hom_ι {M N : U.toScheme.Modules} (φ : M ⟶ N) :
    (openToOverKernelIso U φ).hom ≫ kernel.ι ((openToOverFunctor U).map φ) =
      (openToOverFunctor U).map (kernel.ι φ) := by
  simpa only [openToOverKernelIso, PreservesKernel.iso_hom] using
    kernelComparison_comp_ι φ (openToOverFunctor U)

variable (I : Type u)

/-- Recover an arbitrary original free-to-unit map through the proved
equivalence. There is no epimorphism premise on the given map. -/
def openToOverFreeToUnitPreimage
    (φ : _root_.SheafOfModules.free (R := X.ringCatSheaf.over U) I ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    _root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ⟶
      _root_.SheafOfModules.unit U.toScheme.ringCatSheaf :=
  (openToOverFunctor U).preimage
    ((openToOverFreeIso U I).inv ≫ φ ≫ (openToOverUnitIso U).hom)

@[simp]
theorem openToOverFreeToUnitPreimage_map
    (φ : _root_.SheafOfModules.free (R := X.ringCatSheaf.over U) I ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (openToOverFunctor U).map (openToOverFreeToUnitPreimage U I φ) =
      (openToOverFreeIso U I).inv ≫ φ ≫ (openToOverUnitIso U).hom :=
  (openToOverFunctor U).map_preimage _

/-- The recovered map has the actual original Over-site kernel after
transport. Its source and target comparisons are the original free/unit isos. -/
def openToOverFreeToUnitKernelIso
    (φ : _root_.SheafOfModules.free (R := X.ringCatSheaf.over U) I ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (openToOverFunctor U).obj (kernel (openToOverFreeToUnitPreimage U I φ)) ≅
      kernel φ :=
  openToOverKernelIso U (openToOverFreeToUnitPreimage U I φ) ≪≫
    kernel.mapIso ((openToOverFunctor U).map (openToOverFreeToUnitPreimage U I φ)) φ
      (openToOverFreeIso U I).symm (openToOverUnitIso U).symm (by
        simp only [Iso.symm_hom, openToOverFreeToUnitPreimage_map, Category.assoc,
          Iso.hom_inv_id, Category.comp_id])

/-- The final comparison retains the actual kernel inclusion and the
original finite-free coordinate comparison. -/
theorem openToOverFreeToUnitKernelIso_hom_ι
    (φ : _root_.SheafOfModules.free (R := X.ringCatSheaf.over U) I ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (openToOverFreeToUnitKernelIso U I φ).hom ≫ kernel.ι φ =
      (openToOverFunctor U).map (kernel.ι (openToOverFreeToUnitPreimage U I φ)) ≫
        (openToOverFreeIso U I).inv := by
  simp only [openToOverFreeToUnitKernelIso, Iso.trans_hom, Category.assoc,
    kernel.mapIso_hom, kernel.lift_ι, Iso.symm_hom]
  rw [← Category.assoc, openToOverKernelIso_hom_ι]

end KltDP.Geometry

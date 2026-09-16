/-
Original project adapter for the pinned restriction functors and actual
kernel comparison. Released under Apache 2.0; see
docs/reuse_sources/all_open_unit_kernel/sources/LICENSE.
-/
import KltDP.Compatibility.ModuleSheafEquivalence
import KltDP.Compatibility.SheafFiniteTypeLocality
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Actual kernel generators under iterated Over restriction

The original iterated-slice transport is an equivalence of the original
module sheaf categories. Restrict an arbitrary free-to-unit map, compare
its actual kernel, and pull an actual generating epimorphism back through
that equivalence. No generation or epimorphism assumption is imposed on
the original free-to-unit map.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) {U : C} (V : Over U)

/-- The equivalence has exactly the already constructed original
iterated-Over pushforward as its forward functor. -/
def iteratedOverEquivalence :
    SheafOfModules.{u} ((R.over U).over V) ≌ SheafOfModules.{u} (R.over V.left) := by
  letI : Functor.IsContinuous.{u} (Over.iteratedSliceEquiv V).symm.functor
      (J.over V.left) ((J.over U).over V) :=
    iteratedSliceBackward_isContinuous J V
  letI : Functor.IsContinuous.{u} (Over.iteratedSliceEquiv V).symm.inverse
      ((J.over U).over V) (J.over V.left) :=
    iteratedSliceForward_isContinuous J V
  exact KltDP.SheafModuleEquivalence.pushforwardEquivalence
    (Over.iteratedSliceEquiv V).symm (𝟙 (R.over V.left))

@[simp]
theorem iteratedOverEquivalence_functor :
    (iteratedOverEquivalence R V).functor = iteratedOverFunctor R V := rfl

instance iteratedOverFunctor_isEquivalence : (iteratedOverFunctor R V).IsEquivalence :=
  (iteratedOverEquivalence R V).isEquivalence_functor

/-- A section on the original object gives its original compatible
family on the Over site by restriction along each actual arrow. -/
def sectionOnOver (M : SheafOfModules.{u} R) (W : C) (s : M.val.obj (op W)) :
    (M.over W).sections :=
  PresheafOfModules.sectionsMk (fun T => M.val.map T.unop.hom.op s)
    (fun {T T'} f => by
      simpa only [← op_comp, Over.w] using
        (CategoryTheory.congr_fun
          (M.val.presheaf.map_comp T.unop.hom.op f.unop.left.op) s).symm)

/-- Original compatible sections of `M.over W` are exactly original
sections of `M` on `W`, by evaluation at the identity object. -/
def overSectionsEquiv (M : SheafOfModules.{u} R) (W : C) :
    (M.over W).sections ≃ M.val.obj (op W) where
  toFun s := s.val (op (Over.mk (𝟙 W)))
  invFun := sectionOnOver R M W
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro T
    exact s.property
      (Over.homMk T.unop.hom (Category.comp_id _) : T.unop ⟶ Over.mk (𝟙 W)).op
  right_inv s := by
    change M.val.presheaf.map (𝟙 (op W)) s = s
    exact CategoryTheory.congr_fun (M.val.presheaf.map_id _) s

/-- The inverse correspondence uses the actual original restriction map. -/
@[simp]
theorem overSectionsEquiv_symm_val (M : SheafOfModules.{u} R) (W : C)
    (s : M.val.obj (op W)) (T : (Over W)ᵒᵖ) :
    ((overSectionsEquiv R M W).symm s).val T = M.val.map T.unop.hom.op s := rfl

variable [hPullbacks : HasPullbacks C]
  [hWeak : ∀ W : C, HasWeakSheafify (J.over W) AddCommGrp.{u}]
  [hLocal : ∀ W : C, (J.over W).WEqualsLocallyBijective AddCommGrp.{u}]
  [∀ W : C, (J.over W).HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  [∀ (W : C) (T : Over W), HasWeakSheafify ((J.over W).over T) AddCommGrp.{u}]
  [∀ (W : C) (T : Over W), ((J.over W).over T).WEqualsLocallyBijective AddCommGrp.{u}]
  [∀ (W : C) (T : Over W), ((J.over W).over T).HasSheafCompose
    (forget₂ RingCat.{u} AddCommGrp.{u})]

include hPullbacks in
local instance : HasBinaryProducts (Over U) :=
  CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback

include hWeak hLocal in
local instance : (overFunctor (R.over U) V).IsRightAdjoint :=
  inferInstanceAs ((pushforward.{u} (F := Over.forget V)
    (J := (J.over U).over V) (K := J.over U) (𝟙 ((R.over U).over V))).IsRightAdjoint)

local instance : (overFunctor (R.over U) V).PreservesZeroMorphisms :=
  ⟨fun _ _ => rfl⟩

local instance : (iteratedOverFunctor R V).PreservesZeroMorphisms :=
  ⟨fun _ _ => rfl⟩

/-- Restriction to the nested site followed by its actual flattening. -/
def overToSingleFunctor : SheafOfModules.{u} (R.over U) ⥤
    SheafOfModules.{u} (R.over V.left) :=
  overFunctor (R.over U) V ⋙ iteratedOverFunctor R V

include hPullbacks in
instance overToSingleFunctor_isLeftAdjoint : (overToSingleFunctor R V).IsLeftAdjoint := by
  letI : HasBinaryProducts (Over U) :=
    @CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback C _ hPullbacks U
  exact ((overPushforwardOverAdj (R.over U) V).comp
    (iteratedOverAdjunction R V)).isLeftAdjoint

include hWeak hLocal in
instance overToSingleFunctor_isRightAdjoint : (overToSingleFunctor R V).IsRightAdjoint := by
  letI : HasWeakSheafify (J.over U) AddCommGrp.{u} := hWeak U
  letI : (J.over U).WEqualsLocallyBijective AddCommGrp.{u} := hLocal U
  letI : (overFunctor (R.over U) V).IsRightAdjoint :=
    (PullbackConstruction.adjunction.{u} (F := Over.forget V)
      (J := (J.over U).over V) (K := J.over U) (𝟙 ((R.over U).over V))).isRightAdjoint
  exact ((iteratedOverEquivalence R V).symm.toAdjunction.comp
    (Adjunction.ofIsRightAdjoint (overFunctor (R.over U) V))).isRightAdjoint

local instance : (overToSingleFunctor R V).PreservesZeroMorphisms :=
  inferInstanceAs ((overFunctor (R.over U) V ⋙ iteratedOverFunctor R V).PreservesZeroMorphisms)

/-- The actual restricted unit comparison, with its original direction. -/
def overToSingleUnitIso : unit (R.over V.left) ≅
    (overToSingleFunctor R V).obj (unit (R.over U)) :=
  (Iso.refl _ : unit (R.over V.left) ≅
      (iteratedOverFunctor R V).obj (unit ((R.over U).over V))) ≪≫
    (iteratedOverFunctor R V).mapIso (unitOverIso (R := R.over U) V).symm

/-- Original finite-free coordinates for the actual restricted map. -/
def overToSingleFreeIso (I : Type u) : free (R := R.over V.left) I ≅
    (overToSingleFunctor R V).obj (free (R := R.over U) I) :=
  mapFreeIso (overToSingleFunctor R V) I (overToSingleUnitIso R V)

variable (I : Type u)
  (φ : free (R := R.over U) I ⟶ unit (R.over U))

/-- The map on the smaller original Over site, obtained from the
original restricted map and the actual unit/free comparisons. -/
def overToSingleFreeToUnitMap : free (R := R.over V.left) I ⟶ unit (R.over V.left) :=
  (overToSingleFreeIso R V I).hom ≫ (overToSingleFunctor R V).map φ ≫
    (overToSingleUnitIso R V).inv

/-- The original restricted kernel is the kernel of the actual restricted
finite family, after the original iterated-slice transport. -/
def overToSingleKernelIso :
    (iteratedOverFunctor R V).obj ((kernel φ).over V) ≅
      kernel (overToSingleFreeToUnitMap R V I φ) :=
  PreservesKernel.iso (overToSingleFunctor R V) φ ≪≫
    kernel.mapIso ((overToSingleFunctor R V).map φ) (overToSingleFreeToUnitMap R V I φ)
      (overToSingleFreeIso R V I).symm (overToSingleUnitIso R V).symm (by
        simp only [overToSingleFreeToUnitMap, Iso.symm_hom, Iso.inv_hom_id_assoc])

/-- The comparison retains the actual kernel inclusion. -/
theorem overToSingleKernelIso_hom_ι :
    (overToSingleKernelIso R V I φ).hom ≫ kernel.ι (overToSingleFreeToUnitMap R V I φ) =
      (overToSingleFunctor R V).map (kernel.ι φ) ≫ (overToSingleFreeIso R V I).inv := by
  simp only [overToSingleKernelIso, Iso.trans_hom, Category.assoc,
    kernel.mapIso_hom, kernel.lift_ι, Iso.symm_hom, PreservesKernel.iso_hom]
  rw [← Category.assoc, kernelComparison_comp_ι]

/-- Pull actual kernel generators back to the original nested restriction.
The only supplied map is the genuine smaller-site generator epimorphism. -/
def liftIteratedKernelGenerators {A : Type u}
    (p : free (R := R.over V.left) A ⟶ kernel (overToSingleFreeToUnitMap R V I φ)) :
    free (R := (R.over U).over V) A ⟶ (kernel φ).over V :=
  (iteratedOverFunctor R V).preimage
    ((mapFreeIso (iteratedOverFunctor R V) A (Iso.refl _)).inv ≫
      p ≫ (overToSingleKernelIso R V I φ).inv)

/-- These are the original mapped generators, with their actual free
and kernel comparisons, not merely an existence assertion. -/
@[simp]
theorem liftIteratedKernelGenerators_map {A : Type u}
    (p : free (R := R.over V.left) A ⟶ kernel (overToSingleFreeToUnitMap R V I φ)) :
    (iteratedOverFunctor R V).map (liftIteratedKernelGenerators R V I φ p) =
      (mapFreeIso (iteratedOverFunctor R V) A (Iso.refl _)).inv ≫
        p ≫ (overToSingleKernelIso R V I φ).inv :=
  (iteratedOverFunctor R V).map_preimage _

/-- Epimorphism reflection gives actual generation on the original
nested restriction, without any epimorphism premise on `φ`. -/
instance liftIteratedKernelGenerators_epi {A : Type u}
    (p : free (R := R.over V.left) A ⟶ kernel (overToSingleFreeToUnitMap R V I φ)) [Epi p] :
    Epi (liftIteratedKernelGenerators R V I φ p) := by
  letI : (iteratedOverFunctor R V).Faithful :=
    (iteratedOverEquivalence R V).fullyFaithfulFunctor.faithful
  letI : (iteratedOverFunctor R V).ReflectsEpimorphisms :=
    CategoryTheory.Functor.reflectsEpimorphisms_of_faithful (iteratedOverFunctor R V)
  apply (iteratedOverFunctor R V).epi_of_epi_map
  rw [liftIteratedKernelGenerators_map]
  infer_instance

end SheafOfModules

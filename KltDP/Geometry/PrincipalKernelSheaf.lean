import KltDP.Geometry.SchemeModulePullbackUnit
import KltDP.Compatibility.SheafIsoOnBasis
import Mathlib.AlgebraicGeometry.IdealSheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# Actual sheaf trivializations of regular principal kernels

A global regular equation generating the actual kernel on an affine
target gives an actual isomorphism from its structure module to the
kernel module. The map is multiplication by that equation, lifted through
the categorical kernel. Bijectivity is proved on the basis of basic
opens using the pinned localization-compatible ideal kernel.

Quasi-compactness is stated explicitly where it is needed to identify
affine section kernels with `Scheme.Hom.ker`. No inverse module map,
local-freeness, or sheaf trivialization is a hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}}

/-- Multiplication by an actual global regular function on the structure
module, constructed from its compatible restrictions. -/
def schemeScalarEnd (d : Γ(Y, ⊤)) :
    End (_root_.SheafOfModules.unit Y.ringCatSheaf) :=
  (_root_.SheafOfModules.unit Y.ringCatSheaf).unitHomEquiv.symm
    (schemeModuleSectionOfTop (_root_.SheafOfModules.unit Y.ringCatSheaf) d)

/-- The actual sectionwise formula fixes the multiplication convention. -/
@[simp]
theorem schemeScalarEnd_app (d : Γ(Y, ⊤)) (U : Y.Opens) (r : Γ(Y, U)) :
    (schemeScalarEnd d).val.app (op U) r =
      r * Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op d := rfl

/-- At the top open the endomorphism multiplies by the original equation. -/
@[simp]
theorem schemeScalarEnd_appTop (d r : Γ(Y, ⊤)) :
    (schemeScalarEnd d).val.app (op ⊤) r = r * d := by
  rw [schemeScalarEnd_app]
  change r * Y.presheaf.map (𝟙 (op (⊤ : Y.Opens))) d = r * d
  rw [Y.presheaf.map_id]
  rfl

variable (f : X ⟶ Y) (d : Γ(Y, ⊤)) (hd : f.appTop d = 0)

include hd in
/-- An actual equation killed by the structure map gives a morphism
whose image lies in its categorical kernel. -/
theorem schemeScalarEnd_comp_structure_eq_zero :
    schemeScalarEnd d ≫ structureToPushforwardUnit f = 0 := by
  apply (((schemeModulePushforward f).obj
    (_root_.SheafOfModules.unit X.ringCatSheaf)).unitHomEquiv).injective
  apply (schemeModuleSectionsEquivTop _).injective
  change f.appTop ((schemeScalarEnd d).val.app (op ⊤) (1 : Γ(Y, ⊤))) = 0
  rw [schemeScalarEnd_appTop, one_mul]
  exact hd

/-- The actual equation map into the existing categorical kernel sheaf. -/
def schemeKernelGenerator :
    _root_.SheafOfModules.unit Y.ringCatSheaf ⟶ schemeKernelIdeal f :=
  kernel.lift (structureToPushforwardUnit f) (schemeScalarEnd d)
    (schemeScalarEnd_comp_structure_eq_zero f d hd)

/-- The lifted map retains the original multiplication after inclusion. -/
@[simp]
theorem schemeKernelGenerator_comp_ι :
    schemeKernelGenerator f d hd ≫ schemeKernelIdealι f = schemeScalarEnd d :=
  kernel.lift_ι _ _ _

/-- The generator map is multiplication by the restricted equation on
each actual section ring, followed by the actual kernel inclusion. -/
@[simp]
theorem schemeKernelGenerator_app_ι (U : Y.Opens) (r : Γ(Y, U)) :
    (schemeKernelIdealι f).val.app (op U)
        ((schemeKernelGenerator f d hd).val.app (op U) r) =
      r * Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op d :=
  (congrArg (fun α : End (_root_.SheafOfModules.unit Y.ringCatSheaf) =>
    α.val.app (op U) r) (schemeKernelGenerator_comp_ι f d hd)).trans
      (schemeScalarEnd_app d U r)

/-- Literal regular principal generation of the section kernel implies
bijectivity of the constructed equation map on that open. -/
theorem schemeKernelGenerator_app_bijective (U : Y.Opens)
    (hker : RingHom.ker (f.app U).hom =
      Ideal.span {Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op d})
    (hregular : Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op d ∈
      nonZeroDivisors Γ(Y, U)) :
    Function.Bijective ((schemeKernelGenerator f d hd).val.app (op U)) := by
  have hι : Function.Injective ((schemeKernelIdealι f).val.app (op U)) := by
    apply (ModuleCat.mono_iff_injective _).mp
    change Mono ((_root_.SheafOfModules.evaluation Y.ringCatSheaf (op U)).map
      (kernel.ι (structureToPushforwardUnit f)))
    infer_instance
  constructor
  · intro r s hrs
    apply (mul_cancel_right_mem_nonZeroDivisors hregular).mp
    simpa only [schemeKernelGenerator_app_ι] using
      congrArg ((schemeKernelIdealι f).val.app (op U)) hrs
  · intro y
    have hy : (schemeKernelIdealι f).val.app (op U) y ∈ RingHom.ker (f.app U).hom := by
      change ((schemeKernelIdealι f ≫ structureToPushforwardUnit f).val.app (op U)) y = 0
      rw [schemeKernelIdealι_comp]
      rfl
    rw [hker] at hy
    obtain ⟨r, hr⟩ := (Ideal.mem_span_singleton' (α := Γ(Y, U))).mp hy
    refine ⟨r, hι ?_⟩
    rw [schemeKernelGenerator_app_ι]
    exact hr

variable [IsAffine Y] [QuasiCompact f]

/-- The actual kernel on a basic open is the localization of the actual
global kernel, by the pinned affine ideal-sheaf kernel theorem. -/
theorem schemeKernel_basicOpen (r : Γ(Y, ⊤)) :
    RingHom.ker (f.app (Y.basicOpen r)).hom =
      Ideal.map (Y.presheaf.map (homOfLE (show Y.basicOpen r ≤ ⊤ from le_top)).op).hom
        (RingHom.ker f.appTop.hom) := by
  rw [← Scheme.Hom.ker_apply f ⟨Y.basicOpen r, (isAffineOpen_top Y).basicOpen r⟩,
    Scheme.ker_of_isAffine, Scheme.IdealSheafData.ofIdealTop_ideal]

/-- A regular principal actual global kernel on an affine target gives
an isomorphism of actual module sheaves. -/
theorem schemeKernelGenerator_isIso
    (hker : RingHom.ker f.appTop.hom = Ideal.span {d})
    (hregular : d ∈ nonZeroDivisors Γ(Y, ⊤)) :
    IsIso (schemeKernelGenerator f d hd) := by
  apply KltDP.SheafOfModules.isIso_of_bijective_on_basis
    (schemeKernelGenerator f d hd) (isBasis_basicOpen Y)
  intro r
  apply schemeKernelGenerator_app_bijective f d hd (Y.basicOpen r)
  · rw [schemeKernel_basicOpen f r, hker, Ideal.map_span, Set.image_singleton]
  · exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers r)
      Γ(Y, Y.basicOpen r) hregular

/-- The actual regular equation gives a normalized structure-module
trivialization of the actual kernel sheaf on an affine scheme. -/
def principalKernelSheafIso
    (hker : RingHom.ker f.appTop.hom = Ideal.span {d})
    (hregular : d ∈ nonZeroDivisors Γ(Y, ⊤)) :
    _root_.SheafOfModules.unit Y.ringCatSheaf ≅ schemeKernelIdeal f := by
  letI := schemeKernelGenerator_isIso f d hd hker hregular
  exact asIso (schemeKernelGenerator f d hd)

end KltDP.Geometry

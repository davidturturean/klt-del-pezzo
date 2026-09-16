import KltDP.Geometry.QuasicoherentIdealSheafData
import KltDP.Geometry.GluedIdealSheafKernel
import KltDP.Geometry.SchemeConormal
import KltDP.Compatibility.SheafIsoOnBasis
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-!
# Recovering the original quasicoherent ideal subsheaf

The inclusion of a quasicoherent ideal subsheaf factors through the
categorical kernel of its glued closed subscheme. On each affine open,
the kernel is the original section ideal. The resulting map is therefore
an isomorphism, and both directions preserve the inclusions into the
original structure sheaf.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.QuasicoherentImageIdeal

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}}
  (I : (_root_.SheafOfModules.unit X.ringCatSheaf).Submodule)
  [I.toSheafOfModules.IsQuasicoherent]

/-- The actual glued inclusion has the original subsheaf as its affine
section kernel. -/
theorem ofSubmodule_ker_app (U : X.affineOpens) :
    RingHom.ker ((ofSubmodule I).gluedTo.app U.1).hom = I.obj (op U.1) :=
  ((ofSubmodule I).ker_gluedTo_app U).trans (ofSubmodule_ideal I U)

/-- The original subsheaf inclusion is killed by the actual structural map. -/
theorem inclusion_comp_structure_eq_zero :
    I.ι ≫ structureToPushforwardUnit (ofSubmodule I).gluedTo = 0 := by
  have hB : Opens.IsBasis (Set.range (fun U : X.affineOpens => U.1)) := by
    simpa only [Subtype.range_val] using isBasis_affine_open X
  apply (_root_.SheafOfModules.toSheaf X.ringCatSheaf).map_injective
  apply CategoryTheory.Sheaf.hom_ext _ _
  apply TopCat.Sheaf.hom_ext _ _ hB
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  change ↥(I.obj (op U.1)) at s
  change s.val ∈ RingHom.ker ((ofSubmodule I).gluedTo.app U.1).hom
  rw [ofSubmodule_ker_app I U]
  exact s.property

/-- Factor the original inclusion through the actual categorical kernel. -/
def toGluedKernel :
    I.toSheafOfModules ⟶ schemeKernelIdeal (ofSubmodule I).gluedTo :=
  kernel.lift (structureToPushforwardUnit (ofSubmodule I).gluedTo) I.ι
    (inclusion_comp_structure_eq_zero I)

/-- The factorization preserves the original inclusion. -/
@[simp]
theorem toGluedKernel_comp_ι :
    toGluedKernel I ≫ schemeKernelIdealι (ofSubmodule I).gluedTo = I.ι :=
  kernel.lift_ι _ _ _

/-- The inclusion compatibility holds on every original open section. -/
@[simp]
theorem toGluedKernel_app_ι (U : X.Opens) (s : I.obj (op U)) :
    (schemeKernelIdealι (ofSubmodule I).gluedTo).val.app (op U)
        ((toGluedKernel I).val.app (op U) s) = s.val :=
  congrArg (fun α : I.toSheafOfModules ⟶ _root_.SheafOfModules.unit X.ringCatSheaf =>
    α.val.app (op U) s) (toGluedKernel_comp_ι I)

/-- On affine opens the constructed factorization is bijective. -/
theorem toGluedKernel_app_bijective (U : X.affineOpens) :
    Function.Bijective ((toGluedKernel I).val.app (op U.1)) := by
  have hι : Function.Injective
      ((schemeKernelIdealι (ofSubmodule I).gluedTo).val.app (op U.1)) := by
    apply (ModuleCat.mono_iff_injective _).mp
    change Mono ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op U.1)).map
      (kernel.ι (structureToPushforwardUnit (ofSubmodule I).gluedTo)))
    infer_instance
  constructor
  · intro s t hst
    apply Subtype.ext
    simpa only [toGluedKernel_app_ι] using
      congrArg ((schemeKernelIdealι (ofSubmodule I).gluedTo).val.app (op U.1)) hst
  · intro y
    have hy : (schemeKernelIdealι (ofSubmodule I).gluedTo).val.app (op U.1) y ∈
        RingHom.ker ((ofSubmodule I).gluedTo.app U.1).hom := by
      change ((schemeKernelIdealι (ofSubmodule I).gluedTo ≫
        structureToPushforwardUnit (ofSubmodule I).gluedTo).val.app (op U.1)) y = 0
      rw [schemeKernelIdealι_comp]
      rfl
    rw [ofSubmodule_ker_app I U] at hy
    refine ⟨⟨(schemeKernelIdealι (ofSubmodule I).gluedTo).val.app (op U.1) y, hy⟩,
      hι ?_⟩
    exact toGluedKernel_app_ι I U.1 _

/-- The affine-basis criterion applies to the original factorization. -/
theorem toGluedKernel_isIso : IsIso (toGluedKernel I) := by
  have hB : Opens.IsBasis (Set.range (fun U : X.affineOpens => U.1)) := by
    simpa only [Subtype.range_val] using isBasis_affine_open X
  exact KltDP.SheafOfModules.isIso_of_bijective_on_basis (toGluedKernel I) hB
    (toGluedKernel_app_bijective I)

/-- The original quasicoherent ideal subsheaf is the actual kernel module
of the closed subscheme constructed from its own affine section ideals. -/
def gluedKernelIso :
    I.toSheafOfModules ≅ schemeKernelIdeal (ofSubmodule I).gluedTo := by
  letI := toGluedKernel_isIso I
  exact asIso (toGluedKernel I)

/-- The forward isomorphism commutes with both original inclusions. -/
@[simp]
theorem gluedKernelIso_hom_ι :
    (gluedKernelIso I).hom ≫ schemeKernelIdealι (ofSubmodule I).gluedTo = I.ι :=
  toGluedKernel_comp_ι I

/-- The inverse isomorphism also commutes with the original inclusions. -/
@[simp]
theorem gluedKernelIso_inv_ι :
    (gluedKernelIso I).inv ≫ I.ι = schemeKernelIdealι (ofSubmodule I).gluedTo := by
  calc
    _ = (gluedKernelIso I).inv ≫ ((gluedKernelIso I).hom ≫
        schemeKernelIdealι (ofSubmodule I).gluedTo) := by rw [gluedKernelIso_hom_ι]
    _ = _ := by rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end KltDP.Geometry.QuasicoherentImageIdeal

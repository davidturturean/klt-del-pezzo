import Mathlib.AlgebraicGeometry.IdealSheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import KltDP.Geometry.SchemeConormal
import KltDP.Geometry.ClosedImmersionStructureEpi
import KltDP.Geometry.SchemeModulePushforwardScalars
import KltDP.Geometry.PicardEulerValue

/-!
# Closed immersions with equal kernel ideal sheaves

A closed immersion is quasi-compact, so its kernel ideal sheaf records the kernels of `i.app V` on
affine opens `V`; since a section vanishes iff it vanishes on an affine cover (the target is a sheaf),
two closed immersions with the same kernel ideal sheaf have the same kernel `ker (i.app U)` on *every*
open `U` (`ker_app_eq_of_ker_eq`). Hence the kernel module sheaves of the two structure maps
`O_X → i_*O_Z`, `O_X → i'_*O_{Z'}` coincide (`kernelIsoOfKerEq`), and since both structure maps are
epimorphisms (`ClosedImmersionStructureEpi`), the pushed-forward structure sheaves are isomorphic
as `O_X`-modules (`pushforwardUnitIsoOfKerEq`): they are the cokernels of the same kernel. Over a
base `g : X ⟶ Spec k` this gives `dim_k H⁰(Z, O_Z) = dim_k H⁰(Z', O_{Z'})`
(`cohomologyDimension_unit_eq_of_ker_eq`), the degree-transport form of "closed immersions with
equal kernel ideal sheaves have isomorphic sources over `X`" consumed by the intersection symmetry.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {Z X : Scheme.{u}} (i : Z ⟶ X)

/-- A section of `X` is killed by `i.app U` iff its restrictions to all affine sub-opens are. -/
theorem app_eq_zero_iff_forall_affine (U : X.Opens) (s : Γ(X, U)) :
    i.app U s = 0 ↔
      ∀ (V : X.Opens), IsAffineOpen V → ∀ (hV : V ≤ U),
        i.app V (X.presheaf.map (homOfLE hV).op s) = 0 := by
  constructor
  · intro h V _ hV
    have hn : i.app V (X.presheaf.map (homOfLE hV).op s) =
        Z.presheaf.map ((Opens.map i.base).map (homOfLE hV)).op (i.app U s) :=
      ConcreteCategory.congr_hom (i.naturality (homOfLE hV).op) s
    rw [hn, h, map_zero]
  · intro h
    have hcov : ∀ x : U, ∃ V : X.Opens, IsAffineOpen V ∧ (x : X) ∈ V ∧ V ≤ U :=
      fun x => (Opens.isBasis_iff_nbhd.mp (isBasis_affine_open X)) x.2
    choose W hW using hcov
    refine Z.sheaf.eq_of_locally_eq' (fun x : U => i ⁻¹ᵁ W x) (i ⁻¹ᵁ U)
      (fun x => (Opens.map i.base).map (homOfLE (hW x).2.2)) ?_ (i.app U s) 0 ?_
    · intro z hz
      exact Opens.mem_iSup.mpr ⟨⟨i.base z, hz⟩, (hW ⟨i.base z, hz⟩).2.1⟩
    · intro x
      have hn : i.app (W x) (X.presheaf.map (homOfLE (hW x).2.2).op s) =
          Z.presheaf.map ((Opens.map i.base).map (homOfLE (hW x).2.2)).op (i.app U s) :=
        ConcreteCategory.congr_hom (i.naturality (homOfLE (hW x).2.2).op) s
      rw [map_zero]
      exact hn.symm.trans (h (W x) (hW x).1 (hW x).2.2)

variable [IsClosedImmersion i]

/-- **Closed immersions with the same kernel ideal sheaf have the same kernel on every open.** -/
theorem ker_app_eq_of_ker_eq {Z' : Scheme.{u}} (i' : Z' ⟶ X) [IsClosedImmersion i']
    (h : i.ker = i'.ker) (U : X.Opens) :
    RingHom.ker (i.app U).hom = RingHom.ker (i'.app U).hom := by
  have hker : ∀ (V : X.Opens) (hV : IsAffineOpen V) (t : Γ(X, V)),
      i.app V t = 0 ↔ i'.app V t = 0 := by
    intro V hV t
    have e : RingHom.ker (i.app V).hom = RingHom.ker (i'.app V).hom := by
      rw [← Scheme.Hom.ker_apply i ⟨V, hV⟩, ← Scheme.Hom.ker_apply i' ⟨V, hV⟩, h]
    constructor
    · intro ht
      exact RingHom.mem_ker.mp (e ▸ RingHom.mem_ker.mpr ht)
    · intro ht
      exact RingHom.mem_ker.mp (e.symm ▸ RingHom.mem_ker.mpr ht)
  ext s
  rw [RingHom.mem_ker, RingHom.mem_ker]
  change i.app U s = 0 ↔ i'.app U s = 0
  rw [app_eq_zero_iff_forall_affine i U s, app_eq_zero_iff_forall_affine i' U s]
  exact ⟨fun hh V hV hVU => (hker V hV _).mp (hh V hV hVU),
    fun hh V hV hVU => (hker V hV _).mpr (hh V hV hVU)⟩

section PushforwardIso

variable {Z Z' X : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X) [IsClosedImmersion i] [IsClosedImmersion i']
  (h : i.ker = i'.ker)

include h in
/-- Sections of the kernel of `O_X → i_*O_Z` are killed by `O_X → i'_*O_{Z'}`. -/
theorem kernel_ι_comp_structure_of_ker_eq :
    Limits.kernel.ι (structureToPushforwardUnit i) ≫ structureToPushforwardUnit i' = 0 := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  rintro ⟨U⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hmem : (Limits.kernel.ι (structureToPushforwardUnit i)).val.app (op U) x ∈
      RingHom.ker (i.app U).hom := by
    change ((schemeKernelIdealι i ≫ structureToPushforwardUnit i).val.app (op U)) x = 0
    rw [schemeKernelIdealι_comp]
    rfl
  rw [ker_app_eq_of_ker_eq i i' h U] at hmem
  change i'.app U ((Limits.kernel.ι (structureToPushforwardUnit i)).val.app (op U) x) = 0
  exact RingHom.mem_ker.mp hmem

include h in
/-- The kernels of the two structure maps coincide. -/
def kernelIsoOfKerEq :
    Limits.kernel (structureToPushforwardUnit i) ≅ Limits.kernel (structureToPushforwardUnit i') where
  hom := Limits.kernel.lift (structureToPushforwardUnit i') (Limits.kernel.ι (structureToPushforwardUnit i))
    (kernel_ι_comp_structure_of_ker_eq i i' h)
  inv := Limits.kernel.lift (structureToPushforwardUnit i) (Limits.kernel.ι (structureToPushforwardUnit i'))
    (kernel_ι_comp_structure_of_ker_eq i' i h.symm)
  hom_inv_id := by
    rw [← cancel_mono (Limits.kernel.ι (structureToPushforwardUnit i)), Category.assoc,
      Limits.kernel.lift_ι, Limits.kernel.lift_ι, Category.id_comp]
  inv_hom_id := by
    rw [← cancel_mono (Limits.kernel.ι (structureToPushforwardUnit i')), Category.assoc,
      Limits.kernel.lift_ι, Limits.kernel.lift_ι, Category.id_comp]

/-- The kernel isomorphism is compatible with the kernel inclusions. -/
theorem kernelIsoOfKerEq_hom_ι :
    (kernelIsoOfKerEq i i' h).hom ≫ Limits.kernel.ι (structureToPushforwardUnit i') =
      Limits.kernel.ι (structureToPushforwardUnit i) :=
  Limits.kernel.lift_ι _ _ _

include h in
/-- **Closed immersions with equal kernel ideal sheaves have isomorphic pushed-forward structure
sheaves** (as `O_X`-modules): both are the cokernel of the common kernel. -/
def pushforwardUnitIsoOfKerEq :
    (schemeModulePushforward i).obj (_root_.SheafOfModules.unit Z.ringCatSheaf) ≅
      (schemeModulePushforward i').obj (_root_.SheafOfModules.unit Z'.ringCatSheaf) := by
  haveI := structureToPushforwardUnit_epi_of_isClosedImmersion i
  haveI := structureToPushforwardUnit_epi_of_isClosedImmersion i'
  exact (asIso (Abelian.factorThruCoimage (structureToPushforwardUnit i))).symm ≪≫
    Limits.cokernel.mapIso (Limits.kernel.ι (structureToPushforwardUnit i))
      (Limits.kernel.ι (structureToPushforwardUnit i')) (kernelIsoOfKerEq i i' h) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.comp_id, kernelIsoOfKerEq_hom_ι]) ≪≫
    asIso (Abelian.factorThruCoimage (structureToPushforwardUnit i'))

section DegreeTransport

variable {k : Type u} [Field k]

include h in
/-- **Degree transport**: closed immersions with equal kernel ideal sheaves have the same
`dim_k H⁰(·, O)` over any base `g : X ⟶ Spec k` (through the pushforward comparison
`H⁰(X, i_*O_Z) ≃ H⁰(Z, O_Z)` and the module isomorphism `i_*O_Z ≅ i'_*O_{Z'}`). -/
theorem cohomologyDimension_unit_eq_of_ker_eq (g : X ⟶ Spec (CommRingCat.of k)) :
    cohomologyDimension (i ≫ g) (_root_.SheafOfModules.unit Z.ringCatSheaf) 0 =
      cohomologyDimension (i' ≫ g) (_root_.SheafOfModules.unit Z'.ringCatSheaf) 0 := by
  letI := baseRingModule g ((schemeModulePushforward i).obj (_root_.SheafOfModules.unit Z.ringCatSheaf)) 0
  letI := baseRingModule (i ≫ g) (_root_.SheafOfModules.unit Z.ringCatSheaf) 0
  letI := baseRingModule g ((schemeModulePushforward i').obj (_root_.SheafOfModules.unit Z'.ringCatSheaf)) 0
  letI := baseRingModule (i' ≫ g) (_root_.SheafOfModules.unit Z'.ringCatSheaf) 0
  have h₁ : cohomologyDimension g ((schemeModulePushforward i).obj
      (_root_.SheafOfModules.unit Z.ringCatSheaf)) 0 =
      cohomologyDimension (i ≫ g) (_root_.SheafOfModules.unit Z.ringCatSheaf) 0 :=
    (pushforwardHZeroBaseRingLinearEquiv i g (_root_.SheafOfModules.unit Z.ringCatSheaf)).finrank_eq
  have h₂ : cohomologyDimension g ((schemeModulePushforward i').obj
      (_root_.SheafOfModules.unit Z'.ringCatSheaf)) 0 =
      cohomologyDimension (i' ≫ g) (_root_.SheafOfModules.unit Z'.ringCatSheaf) 0 :=
    (pushforwardHZeroBaseRingLinearEquiv i' g (_root_.SheafOfModules.unit Z'.ringCatSheaf)).finrank_eq
  rw [← h₁, ← h₂]
  exact cohomologyDimension_eq_of_iso g (pushforwardUnitIsoOfKerEq i i' h) 0

end DegreeTransport

end PushforwardIso

end KltDP.Geometry

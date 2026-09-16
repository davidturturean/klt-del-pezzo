import KltDP.Geometry.QuasicoherentIdealKernelIso
import KltDP.Geometry.GluedIdealInvertible
import KltDP.Geometry.InvertibleSheafPicard
import KltDP.Compatibility.SheafIsoOnBasis
import KltDP.Compatibility.InvertibleQuasicoherent

/-!
# The kernel module of a morphism and the kernel module of its glued kernel subscheme

For a quasi-compact morphism `f : X ⟶ Y` whose kernel module `schemeKernelIdeal f` is
quasicoherent, the accepted image-ideal data of the kernel inclusion is the kernel ideal sheaf
`f.ker` (`ofMorphism_kernelι`), and the affine-basis kernel comparison identifies
`schemeKernelIdeal f` with the kernel module of the glued closed subscheme of `f.ker`
(`kernelIdealGluedIso`, compatible with the inclusions into the structure sheaf). Consequently,
when the kernel module is invertible and `f.ker` is locally principal regular, the ideal line
`⟨schemeKernelIdeal f, _⟩` and the accepted `gluedKernelLine f.ker` have the same Picard class
(`toPic_eq_gluedKernelLine`).

This is a public copy of the private constructions of the accepted
`FrobeniusStrictTransformProductKernel`/`FrobeniusStrictTransformClassesTower` modules (no
accepted module is modified).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

open QuasicoherentImageIdeal

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section KernelIdealSheaf

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Sections of the kernel module are exactly the kernel of the section map. -/
theorem schemeKernelIdealι_range_eq_ker (U : Y.Opens) :
    LinearMap.range ((schemeKernelIdealι f).val.app (op U)).hom =
      RingHom.ker (f.app U).hom := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    change ((schemeKernelIdealι f ≫ structureToPushforwardUnit f).val.app (op U)) y = 0
    rw [schemeKernelIdealι_comp]
    rfl
  · intro s hs
    let e := schemeKernelIdealSectionsIso f U
    have hs' : s ∈ LinearMap.ker ((structureToPushforwardUnit f).val.app (op U)).hom := hs
    refine ⟨e.inv ⟨s, hs'⟩, ?_⟩
    have h := ConcreteCategory.congr_hom (schemeKernelIdealSectionsIso_hom_subtype f U)
      (e.inv ⟨s, hs'⟩)
    change (LinearMap.ker ((structureToPushforwardUnit f).val.app (op U)).hom).subtype
        (e.hom (e.inv ⟨s, hs'⟩)) =
      (schemeKernelIdealι f).val.app (op U) (e.inv ⟨s, hs'⟩) at h
    rw [Iso.inv_hom_id_apply] at h
    exact h.symm

/-- The image ideal sheaf of the kernel inclusion is the kernel ideal sheaf. -/
theorem ofMorphism_schemeKernelIdealι [QuasiCompact f] [(schemeKernelIdeal f).IsQuasicoherent] :
    ofMorphism (schemeKernelIdealι f) = f.ker := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [ofMorphism_ideal, Scheme.Hom.ker_apply]
  exact schemeKernelIdealι_range_eq_ker f U.1

end KernelIdealSheaf

section ImageKernel

variable {X : Scheme.{u}} {M : X.Modules} [M.IsQuasicoherent]
  (g : M ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)

/-- The glued image ideal is killed by the component image map. -/
theorem image_comp_structureToPushforwardUnit_zero :
    g ≫ structureToPushforwardUnit (ofMorphism g).gluedTo = 0 := by
  have hB : Opens.IsBasis (Set.range (fun U : X.affineOpens => U.1)) := by
    simpa only [Subtype.range_val] using isBasis_affine_open X
  apply (_root_.SheafOfModules.toSheaf X.ringCatSheaf).map_injective
  apply CategoryTheory.Sheaf.hom_ext _ _
  apply TopCat.Sheaf.hom_ext _ _ hB
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  change g.val.app (op U.1) s ∈ RingHom.ker ((ofMorphism g).gluedTo.app U.1).hom
  rw [(ofMorphism g).ker_gluedTo_app U, ofMorphism_ideal]
  exact ⟨s, rfl⟩

/-- The factorisation of `g` through the kernel module of the glued image subscheme. -/
def imageToGluedKernel : M ⟶ schemeKernelIdeal (ofMorphism g).gluedTo :=
  kernel.lift (structureToPushforwardUnit (ofMorphism g).gluedTo) g
    (image_comp_structureToPushforwardUnit_zero g)

theorem imageToGluedKernel_inclusion :
    imageToGluedKernel g ≫ schemeKernelIdealι (ofMorphism g).gluedTo = g :=
  kernel.lift_ι _ _ _

theorem imageToGluedKernel_app_inclusion (U : X.Opens) (s : M.val.obj (op U)) :
    (schemeKernelIdealι (ofMorphism g).gluedTo).val.app (op U)
        ((imageToGluedKernel g).val.app (op U) s) = g.val.app (op U) s :=
  congrArg (fun α : M ⟶ _root_.SheafOfModules.unit X.ringCatSheaf =>
    α.val.app (op U) s) (imageToGluedKernel_inclusion g)

/-- Monicity and the affine image ideals give bijectivity on affine opens. -/
theorem imageToGluedKernel_app_bijective [Mono g] (U : X.affineOpens) :
    Function.Bijective ((imageToGluedKernel g).val.app (op U.1)) := by
  have hg : Function.Injective (g.val.app (op U.1)) := by
    apply (ModuleCat.mono_iff_injective _).mp
    change Mono ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op U.1)).map g)
    infer_instance
  have hι : Function.Injective
      ((schemeKernelIdealι (ofMorphism g).gluedTo).val.app (op U.1)) := by
    apply (ModuleCat.mono_iff_injective _).mp
    change Mono ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op U.1)).map
      (kernel.ι (structureToPushforwardUnit (ofMorphism g).gluedTo)))
    infer_instance
  constructor
  · intro s t hst
    apply hg
    simpa only [imageToGluedKernel_app_inclusion] using
      congrArg ((schemeKernelIdealι (ofMorphism g).gluedTo).val.app (op U.1)) hst
  · intro y
    have hy : (schemeKernelIdealι (ofMorphism g).gluedTo).val.app (op U.1) y ∈
        RingHom.ker ((ofMorphism g).gluedTo.app U.1).hom := by
      change ((schemeKernelIdealι (ofMorphism g).gluedTo ≫
        structureToPushforwardUnit (ofMorphism g).gluedTo).val.app (op U.1)) y = 0
      rw [schemeKernelIdealι_comp]
      rfl
    rw [(ofMorphism g).ker_gluedTo_app U, ofMorphism_ideal] at hy
    obtain ⟨s, hs⟩ := hy
    refine ⟨s, hι ?_⟩
    exact (imageToGluedKernel_app_inclusion g U.1 s).trans hs

/-- A monic map into the structure sheaf is isomorphic to the kernel module of its glued image
subscheme. -/
def monicImageGluedKernelIso [Mono g] : M ≅ schemeKernelIdeal (ofMorphism g).gluedTo := by
  have hB : Opens.IsBasis (Set.range (fun U : X.affineOpens => U.1)) := by
    simpa only [Subtype.range_val] using isBasis_affine_open X
  letI := KltDP.SheafOfModules.isIso_of_bijective_on_basis (imageToGluedKernel g) hB
    (imageToGluedKernel_app_bijective g)
  exact asIso (imageToGluedKernel g)

theorem monicImageGluedKernelIso_inclusion [Mono g] :
    (monicImageGluedKernelIso g).hom ≫ schemeKernelIdealι (ofMorphism g).gluedTo = g :=
  imageToGluedKernel_inclusion g

end ImageKernel

section KernelGlued

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [(schemeKernelIdeal f).IsQuasicoherent]

instance schemeKernelIdealι_mono : Mono (schemeKernelIdealι f) := by
  unfold schemeKernelIdealι
  infer_instance

/-- The kernel module of `f` is the kernel module of the glued closed subscheme of `f.ker`. -/
def kernelIdealGluedIso : schemeKernelIdeal f ≅ schemeKernelIdeal f.ker.gluedTo :=
  monicImageGluedKernelIso (schemeKernelIdealι f) ≪≫
    eqToIso (congrArg (fun I : Y.IdealSheafData => schemeKernelIdeal I.gluedTo)
      (ofMorphism_schemeKernelIdealι f))

omit [(schemeKernelIdeal f).IsQuasicoherent] in
/-- The ideal line of an invertible kernel module has the Picard class of the accepted ideal line
of the glued closed subscheme of its kernel ideal sheaf (quasicoherence is derived from
invertibility). -/
theorem toPic_eq_gluedKernelLine
    (hinv : KltDP.SheafOfModules.IsInvertible (R := Y.ringCatSheaf) (schemeKernelIdeal f))
    (hI : IdealLocallyPrincipalRegular f.ker) :
    InvertibleSheaf.toPic (X := Y) ⟨schemeKernelIdeal f, hinv⟩ = (gluedKernelLine f.ker hI).toPic := by
  letI := hinv
  letI : (schemeKernelIdeal f).IsQuasicoherent := inferInstance
  letI := Scheme.Modules.monoidalCategory Y
  apply Units.ext
  rw [InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val]
  exact Quotient.sound ⟨kernelIdealGluedIso f⟩

end KernelGlued

end KltDP.Geometry

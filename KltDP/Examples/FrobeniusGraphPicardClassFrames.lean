import KltDP.Examples.FrobeniusGraphPicardClassDiagonal
import KltDP.Geometry.SchemeKernelOpenPullback
import KltDP.Geometry.OpenFrameTransitionCoefficient

/-!
# Invertibility of the original closed Frobenius graph ideal

The two monomial equations give frames of the kernel of the original
global graph morphism on its diagonal chart images. On the actual open
complement, the source is empty and multiplication by one frames the
kernel. These three opens cover the ambient product, so the original
graph kernel itself is an invertible sheaf.

This constructs the actual ideal line. Its inverse is the graph divisor
line; the identification with the ruling tensor powers is not assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassFrames

open KltDP.Geometry SchemeModuleRestriction OpenFrameTransitionCoefficient
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusBlowupContact FrobeniusBlowupChartIteration
open FrobeniusGraphPicardClassAffine FrobeniusGraphPicardClassCharts
open FrobeniusGraphPicardClassDiagonal

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

private theorem kernel_restrict_top {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (U : Y.affineOpens) :
    RingHom.ker (f ∣_ U.1).appTop.hom = (f.ker.ideal U).comap U.1.topIso.hom.hom := by
  have h : (f ∣_ U.1).appTop =
      (U.1.topIso.hom ≫ f.app U.1) ≫ (f ⁻¹ᵁ U.1).topIso.inv := by
    simpa only [Scheme.Γ_map_op, Category.assoc] using Γ_map_morphismRestrict f U.1
  have hi : Function.Injective (f ⁻¹ᵁ U.1).topIso.inv.hom :=
    (f ⁻¹ᵁ U.1).topIso.symm.commRingCatIsoToRingEquiv.injective
  rw [h, CommRingCat.hom_comp, RingHom.ker_comp_of_injective _ hi,
    CommRingCat.hom_comp, ← RingHom.comap_ker, ← Scheme.Hom.ker_apply f U]

def diagonalOpen (i : Fin 2) : (projectiveProduct k).Opens := productChart i i ''ᵁ ⊤

def diagonalAffineOpen (i : Fin 2) : (projectiveProduct k).affineOpens :=
  ⟨diagonalOpen i, (isAffineOpen_top (Spec (CommRingCat.of (planeRing k)))).image_of_isOpenImmersion
    (productChart i i)⟩

/-- The same original polynomial graph equation on its actual image open. -/
def diagonalSection (p : ℕ) (i : Fin 2) : Γ(projectiveProduct k, diagonalOpen (k := k) i) :=
  ((productChart i i).appIso ⊤).inv (firstEquation (k := k) p)

theorem diagonalSection_ideal (p : ℕ) (i : Fin 2) :
    (graphIdeal (k := k) p).ideal (diagonalAffineOpen i) = Ideal.span {diagonalSection p i} := by
  let e := ((productChart (k := k) i i).appIso ⊤).symm.commRingCatIsoToRingEquiv
  have h := graphIdeal_diagonalChart (k := k) p i
    ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of (planeRing k)))⟩
  rw [Scheme.Hom.ker_apply, firstEquation_kernel] at h
  change Ideal.span {firstEquation (k := k) p} =
    ((graphIdeal p).ideal (diagonalAffineOpen i)).comap e.toRingHom at h
  calc
    _ = (((graphIdeal p).ideal (diagonalAffineOpen i)).comap e.toRingHom).map e.toRingHom :=
      (Ideal.map_comap_of_surjective e.toRingHom e.surjective _).symm
    _ = (Ideal.span {firstEquation (k := k) p}).map e.toRingHom := by rw [← h]
    _ = Ideal.span {diagonalSection p i} := by rw [Ideal.map_span, Set.image_singleton]; rfl

def diagonalEquation (p : ℕ) (i : Fin 2) : Γ((diagonalOpen (k := k) i).toScheme, ⊤) :=
  (diagonalOpen i).topIso.inv (diagonalSection p i)

theorem diagonalEquation_kernel (p : ℕ) (i : Fin 2) :
    RingHom.ker (projectiveGraphMorphism (k := k) p ∣_ diagonalOpen i).appTop.hom =
      Ideal.span {diagonalEquation p i} := by
  change RingHom.ker (projectiveGraphMorphism (k := k) p ∣_
    (diagonalAffineOpen i).1).appTop.hom = _
  rw [kernel_restrict_top (projectiveGraphMorphism p) (diagonalAffineOpen i)]
  change ((graphIdeal p).ideal (diagonalAffineOpen i)).comap
    (diagonalOpen i).topIso.hom.hom = _
  rw [diagonalSection_ideal]
  let e := (diagonalOpen (k := k) i).topIso.commRingCatIsoToRingEquiv
  change (Ideal.span {diagonalSection p i}).comap e.toRingHom =
    Ideal.span {e.symm (diagonalSection p i)}
  rw [RingEquiv.toRingHom_eq_coe e, Ideal.comap_coe e, ← Ideal.map_symm e,
    Ideal.map_span, Set.image_singleton]

theorem diagonalEquation_eq_zero (p : ℕ) (i : Fin 2) :
    (projectiveGraphMorphism (k := k) p ∣_ diagonalOpen i).appTop (diagonalEquation p i) = 0 := by
  apply RingHom.mem_ker.mp
  rw [diagonalEquation_kernel]
  exact Ideal.subset_span (Set.mem_singleton _)

theorem diagonalEquation_regular (p : ℕ) (i : Fin 2) :
    diagonalEquation (k := k) p i ∈ nonZeroDivisors Γ((diagonalOpen (k := k) i).toScheme, ⊤) := by
  let e := (diagonalOpen (k := k) i).topIso.commRingCatIsoToRingEquiv
  let a := ((productChart (k := k) i i).appIso ⊤).commRingCatIsoToRingEquiv
  apply mem_nonZeroDivisors_of_injective (f := e) e.injective
  change e (e.symm (diagonalSection p i)) ∈ nonZeroDivisors Γ(projectiveProduct k, diagonalOpen i)
  rw [e.apply_symm_apply]
  apply mem_nonZeroDivisors_of_injective (f := a) a.injective
  change a (a.symm (firstEquation p)) ∈ nonZeroDivisors Γ(Spec (CommRingCat.of (planeRing k)), ⊤)
  rw [a.apply_symm_apply]
  exact firstEquation_regular p

/-- A frame of the restricted original graph morphism, rather than a replacement ideal. -/
def diagonalLocalFrameIso (p : ℕ) (i : Fin 2) :
    _root_.SheafOfModules.unit (diagonalOpen (k := k) i).toScheme.ringCatSheaf ≅
      schemeKernelIdeal (projectiveGraphMorphism (k := k) p ∣_ diagonalOpen i) := by
  letI : IsAffine (diagonalOpen (k := k) i).toScheme := (diagonalAffineOpen i).2
  letI : IsClosedImmersion (projectiveGraphMorphism (k := k) p ∣_ diagonalOpen i) :=
    MorphismProperty.of_isPullback
      (isPullback_morphismRestrict (projectiveGraphMorphism p) (diagonalOpen i)).flip inferInstance
  exact principalKernelSheafIso (projectiveGraphMorphism p ∣_ diagonalOpen i) (diagonalEquation p i)
    (diagonalEquation_eq_zero p i) (diagonalEquation_kernel p i) (diagonalEquation_regular p i)

/-- The target is literally the pullback of the original global graph kernel. -/
def diagonalGlobalFrameIso (p : ℕ) (i : Fin 2) :
    _root_.SheafOfModules.unit (diagonalOpen (k := k) i).toScheme.ringCatSheaf ≅
      (schemeModulePullback (diagonalOpen (k := k) i).ι).obj
        (schemeKernelIdeal (projectiveGraphMorphism (k := k) p)) :=
  diagonalLocalFrameIso p i ≪≫
    localKernelToGlobalPullbackIso (projectiveGraphMorphism p) (diagonalOpen i)

theorem diagonalGlobalFrameIso_inclusion (p : ℕ) (i : Fin 2) :
    (diagonalGlobalFrameIso (k := k) p i).hom ≫
      pulledKernelInclusion (projectiveGraphMorphism (k := k) p)
        (diagonalOpen (k := k) i).ι =
      (schemeScalarEnd (Y := (diagonalOpen (k := k) i).toScheme)
        (diagonalEquation (k := k) p i) :
        _root_.SheafOfModules.unit (diagonalOpen (k := k) i).toScheme.ringCatSheaf ⟶
          _root_.SheafOfModules.unit (diagonalOpen (k := k) i).toScheme.ringCatSheaf) :=
  localKernelGlobalEquation_inclusion (projectiveGraphMorphism (k := k) p)
    (diagonalOpen (k := k) i) (diagonalEquation (k := k) p i)
    (diagonalEquation_eq_zero (k := k) p i)

instance complement_source_isEmpty (p : ℕ) :
    IsEmpty ((projectiveGraphMorphism (k := k) p ⁻¹ᵁ graphComplement p).toScheme) := by
  refine ⟨fun x => ?_⟩
  exact x.property ⟨x.val, rfl⟩

private theorem emptyKernelGenerator_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsEmpty X] :
    IsIso (schemeKernelGenerator f 1 (Subsingleton.elim _ _)) := by
  apply KltDP.SheafOfModules.isIso_of_bijective_on_basis
    (B := fun U : Y.Opens => U) _
    (Opens.isBasis_iff_nbhd.mpr (fun {U x} hx => ⟨U, ⟨U, rfl⟩, hx, le_rfl⟩))
  intro U
  apply schemeKernelGenerator_app_bijective f 1 (Subsingleton.elim _ _) U
  · rw [map_one, Ideal.span_singleton_one]
    apply top_unique
    intro r _
    exact Subsingleton.elim _ _
  · rw [map_one]
    exact one_mem _

/-- The original graph kernel is the unit line on its actual open complement. -/
def complementGlobalFrameIso (p : ℕ) :
    _root_.SheafOfModules.unit (graphComplement (k := k) p).toScheme.ringCatSheaf ≅
      (schemeModulePullback (graphComplement (k := k) p).ι).obj
        (schemeKernelIdeal (projectiveGraphMorphism (k := k) p)) := by
  let f := projectiveGraphMorphism (k := k) p ∣_ graphComplement p
  letI := emptyKernelGenerator_isIso f
  exact asIso (schemeKernelGenerator f 1 (Subsingleton.elim _ _)) ≪≫
    localKernelToGlobalPullbackIso (projectiveGraphMorphism p) (graphComplement p)

def originalAtlasOpen (p : ℕ) : Option (Fin 2) → (projectiveProduct k).Opens
  | none => graphComplement p
  | some i => diagonalOpen i

theorem originalAtlasOpens_cover (p : ℕ) (x : projectiveProduct k) :
    ∃ i : ULift.{u} (Option (Fin 2)), x ∈ originalAtlasOpen (k := k) p i.down := by
  obtain ⟨i, hi⟩ := graphAtlasOpens_cover p x
  refine ⟨⟨i⟩, ?_⟩
  cases i with
  | none => exact hi
  | some i =>
    change x ∈ productChart i i ''ᵁ ⊤
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact hi

def originalOpenFrame (p : ℕ) (i : Option (Fin 2)) :
    _root_.SheafOfModules.unit (originalAtlasOpen (k := k) p i).toScheme.ringCatSheaf ≅
      (restriction (originalAtlasOpen (k := k) p i).ι).obj
        (schemeKernelIdeal (projectiveGraphMorphism (k := k) p)) := by
  cases i with
  | none => exact complementGlobalFrameIso p ≪≫
      ((restrictionIsoPullback (graphComplement (k := k) p).ι).app _).symm
  | some i => exact diagonalGlobalFrameIso p i ≪≫
      ((restrictionIsoPullback (diagonalOpen (k := k) i).ι).app _).symm

/-- A local trivialization atlas of the original graph kernel module. -/
def originalGraphAtlas (p : ℕ) : KltDP.SheafOfModules.LocalTrivializations
    (R := (projectiveProduct k).ringCatSheaf)
    (schemeKernelIdeal (projectiveGraphMorphism (k := k) p)) :=
  localTrivializationsOfOpenCharts _ (fun i : ULift.{u} (Option (Fin 2)) =>
    originalAtlasOpen p i.down) (originalAtlasOpens_cover p)
    (fun i => originalOpenFrame p i.down)

/-- Invertibility is proved for the actual original global closed graph kernel. -/
theorem graphKernel_isInvertible (p : ℕ) :
    isInvertibleSheaf (projectiveProduct k)
      (schemeKernelIdeal (projectiveGraphMorphism (k := k) p)) := by
  change KltDP.SheafOfModules.IsInvertible (R := (projectiveProduct k).ringCatSheaf)
    (schemeKernelIdeal (projectiveGraphMorphism (k := k) p))
  exact KltDP.SheafOfModules.LocalTrivializations.isInvertible
    (R := (projectiveProduct k).ringCatSheaf)
    (M := schemeKernelIdeal (projectiveGraphMorphism (k := k) p))
    (originalGraphAtlas (k := k) p)

/-- The graph ideal line retains literally the original global graph kernel. -/
def graphIdealLine (p : ℕ) : InvertibleSheaf (projectiveProduct k) :=
  InvertibleSheaf.ofLocalTrivializations _ (originalGraphAtlas p)

theorem graphIdealLine_obj (p : ℕ) :
    (graphIdealLine (k := k) p).obj = schemeKernelIdeal (projectiveGraphMorphism p) := rfl

end KltDP.Examples.FrobeniusGraphPicardClassFrames

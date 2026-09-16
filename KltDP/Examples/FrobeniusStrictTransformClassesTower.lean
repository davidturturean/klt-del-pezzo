import KltDP.Examples.FrobeniusStrictTransformPicardStep
import KltDP.Examples.FrobeniusGraphPicardClassTotalTransform
import KltDP.Examples.FrobeniusExceptionalFinalConfiguration
import KltDP.Geometry.QuasicoherentIdealKernelIso
import KltDP.Geometry.SchematicImageOpenImmersion
import KltDP.Compatibility.InvertibleQuasicoherent
import Mathlib.Algebra.BigOperators.Fin

/-!
# Strict-transform classes along one contact tower (Proposition 10.1, graph clause)

Iterating the one-step Picard relation `strictCurvePicardClass_succ` along the actual
contact tower at the origin gives, on every stage `N` and for every residual exponent `m`,
the class of the actual strict transform of the graph `y = x^{m+N}`:

  `strictCurvePicardClass N m = (m + N) • a_N + b_N - ∑_{j < N} E_j`,

where `a_N`, `b_N` are the total transforms of the two original fiber classes
(`firstFiberTotalClass`, `secondFiberTotalClass`) and `E_j = totalExceptionalClass N j` is the
total transform to stage `N` of the exceptional curve created by the `(j+1)`-st blowup. For the
`p`-fold tower this is the manuscript's `B = p a + b - ∑_j E_j` at stage `N ≤ p`.

The base of the induction identifies the stage-zero strict kernel line with the accepted
graph ideal line: the stage-zero strict-transform ideal sheaf is the kernel of the closed graph,
and a quasi-compact morphism with quasicoherent kernel module has that module isomorphic to the
kernel module of the glued subscheme of its kernel ideal sheaf.

Not included here: the strict transform of the tangent fiber and of the older exceptional
curves (the manuscript's `F` and `C_j`); see `STRICT_TRANSFORM_CLASSES.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusStrictTransformClassesTower

open KltDP.Geometry
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusGraphClosed FrobeniusProjectiveMorphism FrobeniusGraphPicardClassFrames
open FrobeniusProjectivePoints
open FrobeniusGraphPicardClassTotalTransform
open FrobeniusStrictTransformInvertible FrobeniusStrictTransformProductKernel
open FrobeniusStrictTransformPicardStep FrobeniusExceptionalFinalConfiguration
open QuasicoherentImageIdeal

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section KernelIdealSheaf

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Sections of the actual kernel module are exactly the kernel of the section map. -/
private theorem kernel_range_eq_ker (U : Y.Opens) :
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

/-- The actual image ideal sheaf of the kernel inclusion is the kernel ideal sheaf. -/
private theorem ofMorphism_kernelι [QuasiCompact f] [(schemeKernelIdeal f).IsQuasicoherent] :
    ofMorphism (schemeKernelIdealι f) = f.ker := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [ofMorphism_ideal, Scheme.Hom.ker_apply]
  exact kernel_range_eq_ker f U.1

end KernelIdealSheaf

section OriginalImageKernel

variable {X : Scheme.{u}} {M : X.Modules} [M.IsQuasicoherent]
  (g : M ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)

/-- The existing glued image ideal is killed by the original component image map. -/
private theorem image_comp_structure_zero :
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

/-- This is the factor of the original map through the original glued image kernel. -/
private def imageToKernel : M ⟶ schemeKernelIdeal (ofMorphism g).gluedTo :=
  kernel.lift (structureToPushforwardUnit (ofMorphism g).gluedTo) g
    (image_comp_structure_zero g)

private theorem imageToKernel_inclusion :
    imageToKernel g ≫ schemeKernelIdealι (ofMorphism g).gluedTo = g :=
  kernel.lift_ι _ _ _

private theorem imageToKernel_app_inclusion (U : X.Opens) (s : M.val.obj (op U)) :
    (schemeKernelIdealι (ofMorphism g).gluedTo).val.app (op U)
        ((imageToKernel g).val.app (op U) s) = g.val.app (op U) s :=
  congrArg (fun α : M ⟶ _root_.SheafOfModules.unit X.ringCatSheaf =>
    α.val.app (op U) s) (imageToKernel_inclusion g)

/-- Monicity and the exact original affine image ideals prove bijectivity. -/
private theorem imageToKernel_app_bijective [Mono g] (U : X.affineOpens) :
    Function.Bijective ((imageToKernel g).val.app (op U.1)) := by
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
    simpa only [imageToKernel_app_inclusion] using
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
    exact (imageToKernel_app_inclusion g U.1 s).trans hs

/-- The existing affine-basis kernel comparison for an actual monic image map. -/
private def monicImageKernelIso [Mono g] : M ≅ schemeKernelIdeal (ofMorphism g).gluedTo := by
  have hB : Opens.IsBasis (Set.range (fun U : X.affineOpens => U.1)) := by
    simpa only [Subtype.range_val] using isBasis_affine_open X
  letI := KltDP.SheafOfModules.isIso_of_bijective_on_basis (imageToKernel g) hB
    (imageToKernel_app_bijective g)
  exact asIso (imageToKernel g)

end OriginalImageKernel

/-- A quasi-compact morphism with quasicoherent kernel module has that module isomorphic to the
kernel module of the actual glued subscheme of its kernel ideal sheaf. -/
private def kernelIdealGluedIso {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [(schemeKernelIdeal f).IsQuasicoherent] :
    schemeKernelIdeal f ≅ schemeKernelIdeal f.ker.gluedTo :=
  haveI : Mono (schemeKernelIdealι f) := by
    unfold schemeKernelIdealι
    infer_instance
  monicImageKernelIso (schemeKernelIdealι f) ≪≫
    eqToIso (congrArg (fun I : Y.IdealSheafData => schemeKernelIdeal I.gluedTo)
      (ofMorphism_kernelι f))

variable {k : Type u} [Field k]

local instance towerOriginIdealMaximal :
    (FrobeniusBlowupChartIteration.originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- The stage-zero strict-transform ideal sheaf is the kernel of the original closed graph. -/
theorem strictTransformIdeal_zero (p : ℕ) :
    @Eq (projectiveContactStage (k := k) 0).IdealSheafData
      (strictTransformIdeal (k := k) 0 p) (graphι p).ker := by
  have h : wholeGraphLift (k := k) 0 p = (graphPuncture p).ι ≫ graphι p :=
    (Category.comp_id _).symm.trans (wholeGraphLift_projection (k := k) 0 p)
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  letI : Nonempty (graph (k := k) p) :=
    ⟨(graphIsoProjectiveLine (k := k) p).inv.base (Classical.choice inferInstance)⟩
  letI : IsIntegral (graph (k := k) p) :=
    isIntegral_of_isOpenImmersion (graphIsoProjectiveLine (k := k) p).hom
  rw [strictTransformIdeal, h]
  exact SchematicImageOpenImmersion.ker_precompose_openImmersion (graphPuncture p).ι (graphι p)

/-- The original projective graph and the stage-zero strict transform have the same kernel
ideal sheaf. -/
theorem graph_ker_eq_strictTransformIdeal_zero (p : ℕ) :
    @Eq (projectiveContactStage (k := k) 0).IdealSheafData
      (projectiveGraphMorphism (k := k) p).ker (strictTransformIdeal (k := k) 0 p) := by
  rw [strictTransformIdeal_zero, ← graphIso_inv_ι]
  exact SchematicImageOpenImmersion.ker_precompose_iso (graphIsoProjectiveLine p).symm (graphι p)

/-- The stage-zero strict kernel module is the original graph kernel module. -/
def strictKernelZeroIso (p : ℕ) :
    schemeKernelIdeal (projectiveGraphMorphism (k := k) p) ≅
      schemeKernelIdeal (strictTransformι (k := k) 0 p) :=
  haveI : KltDP.SheafOfModules.IsInvertible (R := (projectiveProduct k).ringCatSheaf)
      (schemeKernelIdeal (projectiveGraphMorphism (k := k) p)) := graphKernel_isInvertible p
  haveI : (schemeKernelIdeal (projectiveGraphMorphism (k := k) p)).IsLocallyFree :=
    KltDP.SheafOfModules.IsInvertible.isLocallyFree
      (schemeKernelIdeal (projectiveGraphMorphism (k := k) p))
  haveI : (schemeKernelIdeal (projectiveGraphMorphism (k := k) p)).IsQuasicoherent :=
    KltDP.SheafOfModules.locallyFree_isQuasicoherent
      (schemeKernelIdeal (projectiveGraphMorphism (k := k) p))
  kernelIdealGluedIso (projectiveGraphMorphism p) ≪≫
    eqToIso (congrArg (fun I : (projectiveContactStage (k := k) 0).IdealSheafData =>
      schemeKernelIdeal I.gluedTo) (graph_ker_eq_strictTransformIdeal_zero p))

/-- The stage-zero strict kernel line has the class of the total graph ideal line. -/
theorem strictKernelLine_zero_toPic (p : ℕ) :
    (strictKernelLine (k := k) 0 p).toPic = (graphTotalIdealLine (k := k) 0 p).toPic := by
  letI := Scheme.Modules.monoidalCategory (projectiveContactStage (k := k) 0)
  have hid : @Eq (projectiveContactStage (k := k) 0).Pic
      (schemePicardPullbackHom (projectiveContactProjection (k := k) 0)
        (graphIdealLine (k := k) p).toPic)
      (graphIdealLine (k := k) p).toPic :=
    congrArg (fun φ : (projectiveProduct k).Pic →* (projectiveProduct k).Pic =>
      φ (graphIdealLine (k := k) p).toPic) (schemePicardPullbackHom_id (projectiveProduct k))
  rw [graphTotalIdealLine, ← schemePicardPullbackHom_toPic, hid]
  apply Units.ext
  rw [InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val]
  exact Quotient.sound ⟨(strictKernelZeroIso p).symm⟩

/-- At stage zero the strict-transform class is the original graph relation `m a + b`. -/
theorem strictCurvePicardClass_zero (m : ℕ) :
    strictCurvePicardClass (k := k) 0 m =
      m • firstFiberTotalClass 0 + secondFiberTotalClass 0 := by
  rw [← inverse_graphTotalIdeal_picard_eq_actual_fibers, strictCurvePicardClass,
    strictKernelLine_zero_toPic]

/-- The total transform, on stage `N`, of the exceptional curve created by the `(j+1)`-st
blowup of the actual contact tower. -/
def totalExceptionalClass (N : ℕ) (j : Fin N) :
    Additive (projectiveContactStage (k := k) N).Pic :=
  (schemePicardPullbackHom (between (projectiveProductInitial (k := k)) j.isLt)).toAdditive
    (stepExceptionalPicardClass j)

/-- Earlier total exceptional classes on the next stage are the one-step pullbacks. -/
theorem totalExceptionalClass_castSucc (N : ℕ) (j : Fin N) :
    totalExceptionalClass (k := k) (N + 1) (Fin.castSucc j) =
      (schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection N)).toAdditive
        (totalExceptionalClass N j) := by
  have h : between (projectiveProductInitial (k := k)) (Fin.castSucc j).isLt =
      (projectiveProductInitial (k := k)).stepProjection N ≫
        between (projectiveProductInitial (k := k)) j.isLt :=
    between_succ (projectiveProductInitial (k := k)) j.isLt
  unfold totalExceptionalClass
  rw [h, schemePicardPullbackHom_comp]
  rfl

/-- The newest total exceptional class is the actual exceptional class of the last blowup. -/
theorem totalExceptionalClass_last (N : ℕ) :
    totalExceptionalClass (k := k) (N + 1) (Fin.last N) = stepExceptionalPicardClass N := by
  have hb : between (projectiveProductInitial (k := k)) (Fin.last N).isLt = 𝟙 _ :=
    between_refl (projectiveProductInitial (k := k)) (N + 1)
  have hid : @Eq ((projectiveContactStage (k := k) (N + 1)).Pic →*
      (projectiveContactStage (k := k) (N + 1)).Pic)
      (schemePicardPullbackHom (between (projectiveProductInitial (k := k)) (Fin.last N).isLt))
      (MonoidHom.id _) := by
    rw [hb]
    exact schemePicardPullbackHom_id _
  unfold totalExceptionalClass
  rw [hid]
  rfl

/-- The first total fiber class on the next stage is the one-step pullback. -/
theorem firstFiberTotalClass_succ (N : ℕ) :
    firstFiberTotalClass (k := k) (N + 1) =
      (schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection N)).toAdditive
        (firstFiberTotalClass N) := by
  unfold firstFiberTotalClass
  rw [← schemePicardPullbackHom_toPic, ← schemePicardPullbackHom_toPic]
  have hcomp : projectiveContactProjection (k := k) (N + 1) =
      (projectiveProductInitial (k := k)).stepProjection N ≫
        projectiveContactProjection N := rfl
  rw [hcomp, schemePicardPullbackHom_comp, map_neg]
  rfl

/-- The second total fiber class on the next stage is the one-step pullback. -/
theorem secondFiberTotalClass_succ (N : ℕ) :
    secondFiberTotalClass (k := k) (N + 1) =
      (schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection N)).toAdditive
        (secondFiberTotalClass N) := by
  unfold secondFiberTotalClass graphTotalIdealLine
  rw [← schemePicardPullbackHom_toPic, ← schemePicardPullbackHom_toPic]
  have hcomp : projectiveContactProjection (k := k) (N + 1) =
      (projectiveProductInitial (k := k)).stepProjection N ≫
        projectiveContactProjection N := rfl
  rw [hcomp, schemePicardPullbackHom_comp, map_neg]
  rfl

/-- The strict transform of the graph `y = x^{m+N}` on stage `N` has class
`(m + N) a_N + b_N - ∑_{j<N} E_j` in the actual Picard group of that stage. -/
theorem strictCurvePicardClass_tower (N m : ℕ) :
    strictCurvePicardClass (k := k) N m =
      (m + N) • firstFiberTotalClass N + secondFiberTotalClass N -
        ∑ j : Fin N, totalExceptionalClass N j := by
  induction N generalizing m with
  | zero =>
    rw [strictCurvePicardClass_zero, Nat.add_zero, Fin.sum_univ_zero, sub_zero]
  | succ N ih =>
    rw [strictCurvePicardClass_succ, ih (m + 1), map_sub, map_add, map_nsmul, map_sum,
      ← firstFiberTotalClass_succ, ← secondFiberTotalClass_succ, Fin.sum_univ_castSucc,
      totalExceptionalClass_last]
    simp only [totalExceptionalClass_castSucc]
    rw [show m + 1 + N = m + (N + 1) by omega, sub_sub]

/-- The manuscript's `B = p a + b - ∑_{j<N} E_j` for the `p`-fold tower at stage `N ≤ p`. -/
theorem strictCurvePicardClass_pFold (p N : ℕ) (h : N ≤ p) :
    strictCurvePicardClass (k := k) N (p - N) =
      p • firstFiberTotalClass N + secondFiberTotalClass N -
        ∑ j : Fin N, totalExceptionalClass N j := by
  rw [strictCurvePicardClass_tower, Nat.sub_add_cancel h]

/-- Bundle: the graph strict-transform class formula on every stage and residual exponent,
with the one-step pullback bookkeeping of the total exceptional classes. -/
theorem strictTransformClasses_tower :
    (∀ N m : ℕ, strictCurvePicardClass (k := k) N m =
      (m + N) • firstFiberTotalClass N + secondFiberTotalClass N -
        ∑ j : Fin N, totalExceptionalClass N j) ∧
    (∀ (N : ℕ) (j : Fin N), totalExceptionalClass (k := k) (N + 1) (Fin.castSucc j) =
      (schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection N)).toAdditive
        (totalExceptionalClass N j)) ∧
    (∀ N : ℕ, totalExceptionalClass (k := k) (N + 1) (Fin.last N) =
      stepExceptionalPicardClass N) :=
  ⟨strictCurvePicardClass_tower, totalExceptionalClass_castSucc, totalExceptionalClass_last⟩

end KltDP.Examples.FrobeniusStrictTransformClassesTower

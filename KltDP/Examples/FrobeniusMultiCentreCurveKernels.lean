import KltDP.Geometry.SchemeKernelOpenBaseChange
import KltDP.Examples.FrobeniusStrictImageIso
import KltDP.Examples.FrobeniusMultiCentreClassTable

/-!
# The curves of `S_{p,n}` on the cluster opens: kernel lines and classes

`S_{p,n}`'s own curves — the strict graph `graphStrictι`, the strict fibres `fiberStrictι i` and
the exceptional curves `exceptionalCurveι i idx` (accepted closed immersions into
`multiSurface (q+1) n a`) — are compared, on the cluster open `isoPreimage q n a i`, with the
curves of the `i`-th translated tower: the kernel line of each curve of `S_{p,n}`, restricted to the
cluster open, is the restriction along the open immersion `isoMap` of the kernel line of the
corresponding tower curve (`graphKernelClusterIso`, `fiberKernelClusterIso`,
`exceptionalKernelClusterIso`; from the accepted kernel identities `graphStrictι_ker_isoOpen`,
`fiberStrictι_ker_isoOpen`, the isomorphisms `graphRestrictIso`, `fiberRestrictIso`, the pasting of
pullbacks for the exceptional curves, and `SchemeKernelOpenBaseChange`).  Hence the restricted
kernel lines are invertible and their classes are the BRIEF25 cluster classes
(`clusterGraphKernelLine_toPic`, …); the accepted total-transform classes `exceptionalClass` of
`S_{p,n}` and the pullbacks to `S_{p,n}` of the translated fibres `x = 1 + a_i`, `y = 1 + a_i^p`
restrict to the cluster total classes.  **`clusterClassTable_own`** restates the class table of the
cluster open with the restrictions of `S_{p,n}`'s own classes.

The cover of `S_{p,n}` by the cluster opens and the open where the composite blowdown is an
isomorphism is `cluster_cover` (distinct centres over an algebraically closed field).

Not treated: the identification of the pulled-back translated fibre classes with the accepted
`multiFirstFiberClass`/`multiSecondFiberClass` (fibres `x = 1`, `y = 1`; translation invariance of
the fibre classes in `Pic (P¹ × P¹)`), and any statement in `Pic S_{p,n}` itself.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCurveKernels

open KltDP.Geometry KltDP.Geometry.SchemeKernelIdealIsoTransport
  KltDP.Geometry.SchemeKernelOpenBaseChange
open FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
  FrobeniusContactTowerSelectedPoint FrobeniusTranslatedCharts FrobeniusStrictTransformClosure
  FrobeniusFiberClosure FrobeniusGlobalExceptionalSuccessor FrobeniusMultiCentreSurface
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphFiber FrobeniusMultiCentreGraphNewest
  FrobeniusStrictImageIso FrobeniusTowerTransportClasses FrobeniusMultiCentreClassTable
  FrobeniusProjectivePoints FrobeniusBlowupChartIteration

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] (q n : ℕ) (a : Fin n → k) (i : Fin n)

/-- The centre of a chart is a maximal ideal (the accepted witness). -/
local instance curveKernelsOriginMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-! ## The factorisation of `isoMap` -/

/-- The isomorphism of the cluster open onto the open `isoOpen` of the tower. -/
def clusterIso : (isoPreimage q n a i).toScheme ≅ (isoOpen q n a i).toScheme :=
  asIso (towerProjection (q + 1) n a i ∣_ isoOpen q n a i)

theorem clusterIso_hom_ι :
    (clusterIso q n a i).hom ≫ (isoOpen q n a i).ι =
      (isoPreimage q n a i).ι ≫ towerProjection (q + 1) n a i := by
  rw [clusterIso, asIso_hom, morphismRestrict_ι]

theorem clusterIso_hom_ι' : (clusterIso q n a i).hom ≫ (isoOpen q n a i).ι = isoMap q n a i := by
  rw [clusterIso_hom_ι, isoMap_eq]

/-! ## The strict fibre -/

/-- **The kernel line of `F_i ⊂ S_{p,n}` restricted to the cluster open is the restriction of the
kernel line of the tower's strict fibre.** -/
def fiberKernelClusterIso :
    (schemeModulePullback (isoPreimage q n a i).ι).obj
        (schemeKernelIdeal (fiberStrictι (q + 1) n a i)) ≅
      (schemeModulePullback (isoMap q n a i)).obj
        (schemeKernelIdeal (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1))) :=
  (kernelRestrictBaseChangeIso (fiberStrictι (q + 1) n a i) (isoPreimage q n a i)).symm ≪≫
    (schemeKernelIdealEqIso (fiberRestrictIso_hom_fst q n a i)).symm ≪≫
    schemeKernelPrecompIso (fiberRestrictIso q n a i) _ ≪≫
    kernelOpenBaseChangeIso _ (clusterIso q n a i) (isoMap q n a i) (clusterIso_hom_ι' q n a i)

theorem fiberKernelCluster_isInvertible :
    KltDP.SheafOfModules.IsInvertible (R := (clusterScheme q n a i).ringCatSheaf)
      ((schemeModulePullback (isoPreimage q n a i).ι).obj
        (schemeKernelIdeal (fiberStrictι (q + 1) n a i))) :=
  isInvertible_of_iso (schemeModulePullback_isInvertible (isoMap q n a i) _
    (translatedFiberKernelLine (q + 1) (a i) (q + 1)).property) (fiberKernelClusterIso q n a i).symm

/-- The kernel line of `F_i` restricted to the cluster open. -/
def clusterFiberKernelLine : InvertibleSheaf (clusterScheme q n a i) :=
  ⟨_, fiberKernelCluster_isInvertible q n a i⟩

/-- **Its class is the cluster class `F̃`.** -/
theorem clusterFiberKernelLine_toPic :
    -Additive.ofMul (clusterFiberKernelLine q n a i).toPic = clusterFiberClass q n a i := by
  unfold clusterFiberClass translatedFiberClass
  rw [toPic_eq_pullback_of_iso (isoMap q n a i) (translatedFiberKernelLine (q + 1) (a i) (q + 1))
    (clusterFiberKernelLine q n a i) (fiberKernelClusterIso q n a i), map_neg]
  rfl

/-! ## The strict graph -/

section Graph

variable [Fact (q + 1).Prime] [CharP k (q + 1)]

/-- **The kernel line of `B ⊂ S_{p,n}` restricted to the cluster open is the restriction of the
kernel line of the tower's strict graph.** -/
def graphKernelClusterIso :
    (schemeModulePullback (isoPreimage q n a i).ι).obj
        (schemeKernelIdeal (graphStrictι (q + 1) n a)) ≅
      (schemeModulePullback (isoMap q n a i)).obj
        (schemeKernelIdeal (closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0)) :=
  (kernelRestrictBaseChangeIso (graphStrictι (q + 1) n a) (isoPreimage q n a i)).symm ≪≫
    (schemeKernelIdealEqIso (graphRestrictIso_hom_fst q n a i)).symm ≪≫
    schemeKernelPrecompIso (graphRestrictIso q n a i) _ ≪≫
    kernelOpenBaseChangeIso _ (clusterIso q n a i) (isoMap q n a i) (clusterIso_hom_ι' q n a i)

theorem graphKernelCluster_isInvertible :
    KltDP.SheafOfModules.IsInvertible (R := (clusterScheme q n a i).ringCatSheaf)
      ((schemeModulePullback (isoPreimage q n a i).ι).obj
        (schemeKernelIdeal (graphStrictι (q + 1) n a))) :=
  isInvertible_of_iso (schemeModulePullback_isInvertible (isoMap q n a i) _
    (translatedStrictKernelLine (q + 1) (a i) (q + 1) 0).property)
    (graphKernelClusterIso q n a i).symm

/-- The kernel line of `B` restricted to the cluster open. -/
def clusterGraphKernelLine : InvertibleSheaf (clusterScheme q n a i) :=
  ⟨_, graphKernelCluster_isInvertible q n a i⟩

/-- **Its class is the cluster class `B`.** -/
theorem clusterGraphKernelLine_toPic :
    -Additive.ofMul (clusterGraphKernelLine q n a i).toPic = clusterStrictCurveClass q n a i 0 := by
  unfold clusterStrictCurveClass translatedStrictCurveClass
  rw [toPic_eq_pullback_of_iso (isoMap q n a i) (translatedStrictKernelLine (q + 1) (a i) (q + 1) 0)
    (clusterGraphKernelLine q n a i) (graphKernelClusterIso q n a i), map_neg]
  rfl

end Graph

/-! ## The exceptional curves -/

/-- **The kernel line of the exceptional curve `E_{i,idx} ⊂ S_{p,n}` restricted to the cluster open
is the restriction of the kernel line of the tower's final component** (pasting of pullbacks). -/
def exceptionalKernelClusterIso (idx : FinalIndex.{0} q) :
    (schemeModulePullback (isoPreimage q n a i).ι).obj
        (schemeKernelIdeal (exceptionalCurveι q n a i idx)) ≅
      (schemeModulePullback ((isoPreimage q n a i).ι ≫ towerProjection (q + 1) n a i)).obj
        (schemeKernelIdeal (finalComponentι (translatedInitial (q + 1) (a i)) q idx)) :=
  (kernelRestrictBaseChangeIso (exceptionalCurveι q n a i idx) (isoPreimage q n a i)).symm ≪≫
    (schemeKernelIdealEqIso (pullbackRightPullbackFstIso_hom_fst (towerProjection (q + 1) n a i)
      (finalComponentι (translatedInitial (q + 1) (a i)) q idx) (isoPreimage q n a i).ι)).symm ≪≫
    schemeKernelPrecompIso (pullbackRightPullbackFstIso (towerProjection (q + 1) n a i)
      (finalComponentι (translatedInitial (q + 1) (a i)) q idx) (isoPreimage q n a i).ι) _ ≪≫
    kernelOpenBaseChangeIso _ (clusterIso q n a i) _ (clusterIso_hom_ι q n a i)

theorem finalComponentKernel_isInvertible (idx : FinalIndex.{0} q) :
    KltDP.SheafOfModules.IsInvertible
      (R := (selectedStage (q + 1) (a i) (q + 1)).ringCatSheaf)
      (schemeKernelIdeal (finalComponentι (translatedInitial (q + 1) (a i)) q idx)) := by
  cases idx with
  | inl j => exact (translatedOldFinalKernelLine (q + 1) (a i) (q + 1) j.val (by omega)).property
  | inr _ => exact PointBlowupGluing.globalCenterFiberIdeal_isInvertible _ _ _

theorem exceptionalKernelCluster_isInvertible (idx : FinalIndex.{0} q) :
    KltDP.SheafOfModules.IsInvertible (R := (clusterScheme q n a i).ringCatSheaf)
      ((schemeModulePullback (isoPreimage q n a i).ι).obj
        (schemeKernelIdeal (exceptionalCurveι q n a i idx))) :=
  isInvertible_of_iso (schemeModulePullback_isInvertible _ _
    (finalComponentKernel_isInvertible q n a i idx)) (exceptionalKernelClusterIso q n a i idx).symm

/-- The kernel line of `E_{i,idx}` restricted to the cluster open. -/
def clusterExceptionalKernelLine (idx : FinalIndex.{0} q) :
    InvertibleSheaf (clusterScheme q n a i) :=
  ⟨_, exceptionalKernelCluster_isInvertible q n a i idx⟩

/-- **The class of the restricted kernel line of `C_{ij}` is the cluster class `C_j`.** -/
theorem clusterExceptionalKernelLine_toPic_inl (j : Fin q) :
    -Additive.ofMul (clusterExceptionalKernelLine q n a i (Sum.inl j)).toPic =
      clusterOldExceptionalStrictClass q n a i j.val (by omega) := by
  unfold clusterOldExceptionalStrictClass translatedOldExceptionalStrictClass
  rw [toPic_eq_pullback_of_iso ((isoPreimage q n a i).ι ≫ towerProjection (q + 1) n a i)
    (translatedOldFinalKernelLine (q + 1) (a i) (q + 1) j.val (by omega))
    (clusterExceptionalKernelLine q n a i (Sum.inl j))
    (exceptionalKernelClusterIso q n a i (Sum.inl j)), map_neg, ← isoMap_eq]
  rfl

/-- **The class of the restricted kernel line of `P_i` is the cluster class `P`.** -/
theorem clusterExceptionalKernelLine_toPic_inr :
    -Additive.ofMul (clusterExceptionalKernelLine q n a i (Sum.inr PUnit.unit)).toPic =
      clusterStepExceptionalClass q n a i := by
  unfold clusterStepExceptionalClass translatedStepExceptionalClass
  rw [toPic_eq_pullback_of_iso ((isoPreimage q n a i).ι ≫ towerProjection (q + 1) n a i)
    (translatedStepExceptionalIdealLine (q + 1) (a i) q)
    (clusterExceptionalKernelLine q n a i (Sum.inr PUnit.unit))
    (exceptionalKernelClusterIso q n a i (Sum.inr PUnit.unit)), map_neg, ← isoMap_eq]
  rfl

/-! ## The total-transform classes of `S_{p,n}` on the cluster open -/

/-- **The accepted total-transform class `E_{ij}` of `S_{p,n}` restricts to the cluster total
class.** -/
theorem exceptionalClass_restrict (j : Fin (q + 1)) :
    (schemePicardPullbackHom (isoPreimage q n a i).ι).toAdditive
        (exceptionalClass (q + 1) n a i j) =
      clusterTotalExceptionalClass q n a i j := by
  unfold exceptionalClass clusterTotalExceptionalClass translatedTotalExceptionalClass
    translatedStepExceptionalClass towerExceptionalLine
  rw [map_neg, ← schemePicardPullbackHom_toPic, ← schemePicardPullbackHom_toPic]
  change -Additive.ofMul (schemePicardPullbackHom (isoPreimage q n a i).ι
      (schemePicardPullbackHom (towerProjection (q + 1) n a i)
        (schemePicardPullbackHom (between (translatedInitial (q + 1) (a i)) j.isLt)
          (translatedStepExceptionalIdealLine (q + 1) (a i) j).toPic))) =
    -Additive.ofMul (schemePicardPullbackHom (isoMap q n a i)
      (schemePicardPullbackHom (between (translatedInitial (q + 1) (a i)) j.isLt)
        (translatedStepExceptionalIdealLine (q + 1) (a i) j).toPic))
  rw [isoMap_eq, schemePicardPullbackHom_comp]
  rfl

/-- The pullback to `S_{p,n}` of the class of the fibre `x = 1 + a_i` (ideal-sheaf sign). -/
def multiTranslatedFirstFiberClass : Additive (multiSurface (q + 1) n a).Pic :=
  -Additive.ofMul (pullbackInvertibleSheaf (multiProjection (q + 1) n a)
    (translatedVerticalIdealLine (q + 1) (a i))).toPic

/-- The pullback to `S_{p,n}` of the class of the fibre `y = 1 + a_i^p` (ideal-sheaf sign). -/
def multiTranslatedSecondFiberClass : Additive (multiSurface (q + 1) n a).Pic :=
  -Additive.ofMul (pullbackInvertibleSheaf (multiProjection (q + 1) n a)
    (translatedHorizontalIdealLine (q + 1) (a i))).toPic

theorem ι_multiProjection :
    (isoPreimage q n a i).ι ≫ multiProjection (q + 1) n a =
      isoMap q n a i ≫ selectedProjection (q + 1) (a i) (q + 1) := by
  rw [isoMap_eq, Category.assoc, towerProjection_projection]

theorem multiTranslatedFirstFiberClass_restrict :
    (schemePicardPullbackHom (isoPreimage q n a i).ι).toAdditive
        (multiTranslatedFirstFiberClass q n a i) =
      clusterFirstFiberTotalClass q n a i := by
  unfold multiTranslatedFirstFiberClass clusterFirstFiberTotalClass translatedFirstFiberTotalClass
  rw [map_neg, ← schemePicardPullbackHom_toPic, ← schemePicardPullbackHom_toPic]
  change -Additive.ofMul (schemePicardPullbackHom (isoPreimage q n a i).ι
      (schemePicardPullbackHom (multiProjection (q + 1) n a)
        (translatedVerticalIdealLine (q + 1) (a i)).toPic)) =
    -Additive.ofMul (schemePicardPullbackHom (isoMap q n a i)
      (schemePicardPullbackHom (selectedProjection (q + 1) (a i) (q + 1))
        (translatedVerticalIdealLine (q + 1) (a i)).toPic))
  rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, ← schemePicardPullbackHom_comp,
    ← schemePicardPullbackHom_comp, ι_multiProjection]

theorem multiTranslatedSecondFiberClass_restrict :
    (schemePicardPullbackHom (isoPreimage q n a i).ι).toAdditive
        (multiTranslatedSecondFiberClass q n a i) =
      clusterSecondFiberTotalClass q n a i := by
  unfold multiTranslatedSecondFiberClass clusterSecondFiberTotalClass
    translatedSecondFiberTotalClass
  rw [map_neg, ← schemePicardPullbackHom_toPic, ← schemePicardPullbackHom_toPic]
  change -Additive.ofMul (schemePicardPullbackHom (isoPreimage q n a i).ι
      (schemePicardPullbackHom (multiProjection (q + 1) n a)
        (translatedHorizontalIdealLine (q + 1) (a i)).toPic)) =
    -Additive.ofMul (schemePicardPullbackHom (isoMap q n a i)
      (schemePicardPullbackHom (selectedProjection (q + 1) (a i) (q + 1))
        (translatedHorizontalIdealLine (q + 1) (a i)).toPic))
  rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, ← schemePicardPullbackHom_comp,
    ← schemePicardPullbackHom_comp, ι_multiProjection]

/-! ## The class table with `S_{p,n}`'s own curves, on the cluster open -/

/-- **The class table on the cluster open, with the restrictions of `S_{p,n}`'s own classes**: the
kernel lines of `B`, `F_i`, `C_{ij}`, `P_i` restricted to the cluster open, the accepted total
transforms `E_{ij}`, and the pullbacks of the translated fibres `a_i`, `b_i`. -/
theorem clusterClassTable_own [Fact (q + 1).Prime] [CharP k (q + 1)] :
    (-Additive.ofMul (clusterGraphKernelLine q n a i).toPic =
      (q + 1) • (schemePicardPullbackHom (isoPreimage q n a i).ι).toAdditive
          (multiTranslatedFirstFiberClass q n a i) +
        (schemePicardPullbackHom (isoPreimage q n a i).ι).toAdditive
          (multiTranslatedSecondFiberClass q n a i) -
        ∑ j : Fin (q + 1), (schemePicardPullbackHom (isoPreimage q n a i).ι).toAdditive
          (exceptionalClass (q + 1) n a i j)) ∧
    (∀ j : Fin q, -Additive.ofMul (clusterExceptionalKernelLine q n a i (Sum.inl j)).toPic =
      (schemePicardPullbackHom (isoPreimage q n a i).ι).toAdditive
          (exceptionalClass (q + 1) n a i ⟨j.val, by omega⟩) -
        (schemePicardPullbackHom (isoPreimage q n a i).ι).toAdditive
          (exceptionalClass (q + 1) n a i ⟨j.val + 1, by omega⟩)) ∧
    (-Additive.ofMul (clusterFiberKernelLine q n a i).toPic =
      clusterFiberZeroTotalClass q n a i -
        ∑ j : Fin (q + 1), (schemePicardPullbackHom (isoPreimage q n a i).ι).toAdditive
          (exceptionalClass (q + 1) n a i j)) ∧
    (-Additive.ofMul (clusterExceptionalKernelLine q n a i (Sum.inr PUnit.unit)).toPic =
      (schemePicardPullbackHom (isoPreimage q n a i).ι).toAdditive
        (exceptionalClass (q + 1) n a i (Fin.last q))) := by
  refine ⟨?_, fun j => ?_, ?_, ?_⟩
  · rw [clusterGraphKernelLine_toPic, multiTranslatedFirstFiberClass_restrict,
      multiTranslatedSecondFiberClass_restrict]
    simp_rw [exceptionalClass_restrict]
    exact clusterStrictCurveClass_zero q n a i
  · rw [clusterExceptionalKernelLine_toPic_inl, exceptionalClass_restrict,
      exceptionalClass_restrict]
    exact clusterOldExceptionalStrictClass_eq q n a i j.val (by omega)
  · rw [clusterFiberKernelLine_toPic]
    simp_rw [exceptionalClass_restrict]
    exact clusterFiberClass_tower q n a i
  · rw [clusterExceptionalKernelLine_toPic_inr, exceptionalClass_restrict]
    exact (clusterTotalExceptionalClass_last q n a i).symm

/-! ## The cover of `S_{p,n}` -/

/-- The open of `S_{p,n}` over the complement of all the centres, where the composite blowdown is an
isomorphism. -/
abbrev blowdownIsoOpen : (multiSurface (q + 1) n a).Opens :=
  multiProjection (q + 1) n a ⁻¹ᵁ centersComplement (q + 1) n a

theorem mem_isoPreimage_of_projection_eq [IsAlgClosed k] (ha : Function.Injective a)
    (x : multiSurface (q + 1) n a)
    (hx : (multiProjection (q + 1) n a).base x = graphPoint (q + 1) (a i)) :
    x ∈ isoPreimage q n a i := by
  show (selectedProjection (q + 1) (a i) (q + 1)).base ((towerProjection (q + 1) n a i).base x) ∈
    otherComplement q n a i
  rw [← Scheme.comp_base_apply, towerProjection_projection, hx]
  exact center_mem_otherComplement q n a ha i

/-- **`S_{p,n}` is covered by the isomorphism open of the composite blowdown and the `n` cluster
opens.** -/
theorem cluster_cover [IsAlgClosed k] (ha : Function.Injective a) (x : multiSurface (q + 1) n a) :
    x ∈ blowdownIsoOpen q n a ∨ ∃ i, x ∈ isoPreimage q n a i := by
  by_cases h : (multiProjection (q + 1) n a).base x ∈ centersComplement (q + 1) n a
  · exact Or.inl h
  · right
    rw [mem_centersComplement_iff] at h
    push_neg at h
    obtain ⟨i, hi⟩ := h
    exact ⟨i, mem_isoPreimage_of_projection_eq q n a i ha x hi⟩

theorem cluster_cover_iSup [IsAlgClosed k] (ha : Function.Injective a) :
    (⊤ : (multiSurface (q + 1) n a).Opens) ≤
      blowdownIsoOpen q n a ⊔ ⨆ i : Fin n, isoPreimage q n a i := by
  intro x _
  have hx : x ∈ ((blowdownIsoOpen q n a ⊔ ⨆ i : Fin n, isoPreimage q n a i :
      (multiSurface (q + 1) n a).Opens) : Set (multiSurface (q + 1) n a)) := by
    rw [Opens.coe_sup]
    rcases cluster_cover q n a ha x with h | ⟨i, hi⟩
    · exact Or.inl h
    · exact Or.inr (Opens.mem_iSup.mpr ⟨i, hi⟩)
  exact hx

end KltDP.Examples.FrobeniusMultiCentreCurveKernels

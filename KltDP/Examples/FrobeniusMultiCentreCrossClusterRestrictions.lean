import KltDP.Examples.FrobeniusMultiCentreExceptionalGlobalClasses
import KltDP.Geometry.RationalTreePicardMultidegree

/-!
# Cross-cluster restrictions on `S_{p,n}`

The cluster open `U_i = isoPreimage q n a i` of `S_{p,n}` lies over the complement of the centres
`a_{i'}`, `i' ≠ i`, while every exceptional curve of the `i'`-th cluster and every total transform
`E_{i'j}` lies over the centre `a_{i'}`.  Hence, for `i' ≠ i`, on `U_i`:

* the exceptional curves of the `i'`-th cluster are disjoint from `U_i`
  (`disjoint_cluster_exceptional`), so their ideal lines restrict to the unit and their classes to
  `0` (`exceptionalKernelLine_restrict_cluster`);
* the accepted total transforms restrict to `0` (`exceptionalClass_restrict_cluster`), by the
  accepted `kernelLine_pullback_unitIso` applied to the exceptional fibre of the `i'`-th tower.

Together with the accepted restriction identities on the cluster's own open
(`FrobeniusMultiCentreCurveKernels.clusterClassTable_own`) and on the isomorphism open
(`FrobeniusMultiCentreIsoOpenClasses.exceptionalClass_restrict_isoOpen`), these are the remaining
restriction entries of the class table of `S_{p,n}` for the exceptional rows.  They are not needed
for the global rows of `FrobeniusMultiCentreExceptionalGlobalClasses`, which are proved at the level
of ideal modules.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCrossClusterRestrictions

open KltDP.Geometry KltDP.Geometry.SchemeKernelIdealIsoTransport
  KltDP.Geometry.KernelLinePullbackOffRange KltDP.Geometry.RationalTreePicard
open FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
  FrobeniusContactTowerSelectedPoint FrobeniusTranslatedCharts FrobeniusMultiCentreSurface
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphNewest FrobeniusTowerTransportClasses
  FrobeniusMultiCentreCurveKernels FrobeniusGlobalExceptionalSuccessor
  FrobeniusStageComplement.PlaneChartedScheme FrobeniusBlowupChartIteration
  FrobeniusProjectivePoints FrobeniusMultiCentreExceptionalGlobalClasses

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] (q n : ℕ) (a : Fin n → k)

/-- The centre of a chart is a maximal ideal (the accepted witness). -/
local instance crossClusterOriginMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-! ## Disjointness -/

/-- The cluster open `U_i` misses every exceptional curve of another cluster. -/
theorem disjoint_cluster_exceptional {i i' : Fin n} (hii' : i' ≠ i) (idx : FinalIndex.{0} q) :
    Disjoint (Set.range (isoPreimage q n a i).ι.base)
      (Set.range (exceptionalCurveι q n a i' idx).base) := by
  rw [Set.disjoint_left]
  rintro x ⟨y, hy⟩ hx
  have h1 := exceptionalSupport_projection q n a i' idx x hx
  have h2 : (multiProjection (q + 1) n a).base x ∈ otherComplement q n a i := by
    rw [← hy, Scheme.Opens.ι_base_apply, ← towerProjection_projection (q + 1) n a i,
      Scheme.comp_base_apply]
    exact y.2
  rw [h1] at h2
  exact center_not_mem_otherComplement q n a i i' hii' h2

/-- The composite `U_i ⟶ T_{i'} ⟶ stage j+1` misses the exceptional fibre `E_j` of the `i'`-th
tower, for `i' ≠ i`. -/
theorem disjoint_cluster_previousFiber {i i' : Fin n} (hii' : i' ≠ i) (j : Fin (q + 1)) :
    Disjoint (Set.range (((isoPreimage q n a i).ι ≫ towerProjection (q + 1) n a i') ≫
        between (translatedInitial (q + 1) (a i')) j.isLt).base)
      (Set.range (previousFiberι ((translatedInitial (q + 1) (a i')).stage j.val)).base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨y, rfl⟩ ⟨z, hz⟩
  have h1 := previousFiber_projection_center (translatedInitial (q + 1) (a i')) j.val z
  rw [hz, selected_center] at h1
  have h2 : ((translatedInitial (q + 1) (a i')).toInitial (j.val + 1)).base
      ((((isoPreimage q n a i).ι ≫ towerProjection (q + 1) n a i') ≫
        between (translatedInitial (q + 1) (a i')) j.isLt).base y) =
      (multiProjection (q + 1) n a).base ((isoPreimage q n a i).ι.base y) := by
    rw [← Scheme.comp_base_apply, ← between_zero, Category.assoc, between_comp, between_zero,
      ← towerProjection_projection (q + 1) n a i', Scheme.comp_base_apply,
      Scheme.comp_base_apply, Scheme.comp_base_apply]
    rfl
  rw [h2] at h1
  have h3 : (multiProjection (q + 1) n a).base ((isoPreimage q n a i).ι.base y) ∈
      otherComplement q n a i := by
    rw [Scheme.Opens.ι_base_apply, ← towerProjection_projection (q + 1) n a i,
      Scheme.comp_base_apply]
    exact y.2
  rw [h1] at h3
  exact center_not_mem_otherComplement q n a i i' hii' h3

/-! ## The restricted classes -/

/-- **The accepted total transforms `E_{i'j}` restrict to `0` on the cluster open `U_i`,
`i' ≠ i`.** -/
theorem exceptionalClass_restrict_cluster {i i' : Fin n} (hii' : i' ≠ i) (j : Fin (q + 1)) :
    (schemePicardPullbackHom (isoPreimage q n a i).ι).toAdditive
      (exceptionalClass (q + 1) n a i' j) = 0 := by
  unfold exceptionalClass towerExceptionalLine
  rw [map_neg, ← schemePicardPullbackHom_toPic, ← schemePicardPullbackHom_toPic]
  change -Additive.ofMul (schemePicardPullbackHom (isoPreimage q n a i).ι
      (schemePicardPullbackHom (towerProjection (q + 1) n a i')
        (schemePicardPullbackHom (between (translatedInitial (q + 1) (a i')) j.isLt)
          (translatedStepExceptionalIdealLine (q + 1) (a i') j.val).toPic))) = 0
  have h0 : (pullbackInvertibleSheaf
      (((isoPreimage q n a i).ι ≫ towerProjection (q + 1) n a i') ≫
        between (translatedInitial (q + 1) (a i')) j.isLt)
      (translatedStepExceptionalIdealLine (q + 1) (a i') j.val)).toPic = 1 :=
    (toPic_eq_one_iff_iso_unit _).mpr ⟨kernelLine_pullback_unitIso _ _
      (disjoint_cluster_previousFiber q n a hii' j)⟩
  rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, ← schemePicardPullbackHom_comp,
    ← schemePicardPullbackHom_comp, schemePicardPullbackHom_toPic, h0, ofMul_one, neg_zero]

section Distinct

variable [IsAlgClosed k] (ha : Function.Injective a)

/-- **The ideal lines of the exceptional curves of another cluster restrict to `0` on `U_i`.** -/
theorem exceptionalKernelLine_restrict_cluster {i i' : Fin n} (hii' : i' ≠ i)
    (idx : FinalIndex.{0} q) :
    (schemePicardPullbackHom (isoPreimage q n a i).ι).toAdditive
      (-Additive.ofMul (exceptionalKernelLine q n a ha i' idx).toPic) = 0 := by
  rw [map_neg]
  change -Additive.ofMul (schemePicardPullbackHom (isoPreimage q n a i).ι
    (exceptionalKernelLine q n a ha i' idx).toPic) = 0
  have h0 : (pullbackInvertibleSheaf (isoPreimage q n a i).ι
      (exceptionalKernelLine q n a ha i' idx)).toPic = 1 :=
    (toPic_eq_one_iff_iso_unit _).mpr ⟨kernelLine_pullback_unitIso
      (exceptionalCurveι q n a i' idx) (isoPreimage q n a i).ι
      (disjoint_cluster_exceptional q n a hii' idx)⟩
  rw [schemePicardPullbackHom_toPic, h0, ofMul_one, neg_zero]

end Distinct

end KltDP.Examples.FrobeniusMultiCentreCrossClusterRestrictions

import KltDP.Geometry.SchemeKernelBaseChangeIsoLocus
import KltDP.Examples.FrobeniusMultiCentreCurveKernels

/-!
# The exceptional rows of the class table of `S_{p,n}`, in `Pic S_{p,n}` itself

The exceptional curve `E_{i,idx}` of `S_{p,n} = multiSurface (q+1) n a` is by definition the base
change along the tower projection `π_i = towerProjection (q+1) n a i` of the final exceptional
component `idx` of the `i`-th translated tower.  Over the open `isoOpen q n a i` (the preimage of
the complement of the other centres, where `π_i` restricts to an isomorphism, accepted
`isoOpen_restrict_isIso`) the tower component lives (accepted `finalComponent_range_subset`), so the
generic comparison `KltDP.Geometry.SchemeKernelBaseChangeIsoLocus.baseChangeKernelIso` applies and
gives, in the actual ideal modules of `S_{p,n}`,

  `π_i^* I(E_j^{tower}) ≅ I(E_{i,idx})`   (`exceptionalKernelGlobalIso`),

hence `I(E_{i,idx})` is invertible and its class is the pullback along `π_i` of the tower class
(`neg_exceptionalKernelLine_toPic`).  Since the accepted total-transform class `exceptionalClass`
is itself defined as a Picard pullback along `π_i` (`exceptionalClass_eq_pullback`), the translated
tower relations of `FrobeniusTowerTransportClasses` push forward to the two global rows

  `C_{ij} = E_{ij} − E_{i,j+1}`,  `P_i = E_{i,p}`   (`classTable_SPn_exceptional`)

in `Additive (multiSurface (q+1) n a).Pic` — the first identities of Proposition 10.1 proved on
`S_{p,n}` itself rather than on a cluster open.  The hypotheses are the accepted ones for distinct
centres (`[IsAlgClosed k]`, `ha : Function.Injective a`), which are satisfiable (`n = 0`, or any
injective family over an algebraically closed field).

The rows `F_i` and `B` are not treated here: `F_i` needs the strict fibre's tower relation together
with the identification of the translated stage-`0` fibre class with `b`, and `B` is not a curve of
a single cluster.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusMultiCentreExceptionalGlobalClasses

open KltDP.Geometry KltDP.Geometry.SchemeKernelIdealIsoTransport
  KltDP.Geometry.SchemeKernelBaseChangeIsoLocus
open FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
  FrobeniusContactTowerSelectedPoint FrobeniusTranslatedCharts FrobeniusMultiCentreSurface
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphNewest FrobeniusTowerTransportClasses
  FrobeniusMultiCentreCurveKernels FrobeniusBlowupChartIteration FrobeniusProjectivePoints

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] (q n : ℕ) (a : Fin n → k)

/-- The centre of a chart is a maximal ideal (the accepted witness). -/
local instance exceptionalGlobalOriginMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-! ## The accepted total transform as a Picard pullback -/

section Pullback

variable (i : Fin n)

set_option maxHeartbeats 4000000 in
/-- **The accepted total-transform class `E_{ij}` is the pullback along the tower projection of the
translated tower's total exceptional class.** -/
theorem exceptionalClass_eq_pullback (j : Fin (q + 1)) :
    exceptionalClass (q + 1) n a i j =
      (schemePicardPullbackHom (towerProjection (q + 1) n a i)).toAdditive
        (translatedTotalExceptionalClass (q + 1) (a i) (q + 1) j) := by
  unfold exceptionalClass towerExceptionalLine translatedTotalExceptionalClass
    translatedStepExceptionalClass
  simp only [map_neg]
  change -Additive.ofMul (pullbackInvertibleSheaf (towerProjection (q + 1) n a i)
      (pullbackInvertibleSheaf (between (translatedInitial (q + 1) (a i)) j.isLt)
        (translatedStepExceptionalIdealLine (q + 1) (a i) j.val))).toPic =
    -Additive.ofMul (schemePicardPullbackHom (towerProjection (q + 1) n a i)
      (schemePicardPullbackHom (between (translatedInitial (q + 1) (a i)) j.isLt)
        (translatedStepExceptionalIdealLine (q + 1) (a i) j.val).toPic))
  rw [schemePicardPullbackHom_toPic, schemePicardPullbackHom_toPic]

end Pullback

/-! ## The kernel ideal of an exceptional curve of `S_{p,n}` -/

section Distinct

variable [IsAlgClosed k] (ha : Function.Injective a) (i : Fin n)

include ha in
/-- Every final exceptional component of the `i`-th tower lies in the open over which the tower
projection is an isomorphism. -/
theorem finalComponent_range_subset_isoOpen (idx : FinalIndex.{0} q) :
    Set.range (finalComponentι (translatedInitial (q + 1) (a i)) q idx).base ⊆
      ((isoOpen q n a i : (selectedStage (q + 1) (a i) (q + 1)).Opens) :
        Set (selectedStage (q + 1) (a i) (q + 1))) := by
  have h := finalComponent_range_subset q n a ha i idx
  rw [Scheme.Opens.range_ι] at h
  exact h

set_option maxHeartbeats 4000000 in
/-- **The kernel ideal of `E_{i,idx} ⊂ S_{p,n}` is the pullback along the tower projection of the
kernel ideal of the tower's final component.** -/
def exceptionalKernelGlobalIso (idx : FinalIndex.{0} q) :
    (schemeModulePullback (towerProjection (q + 1) n a i)).obj
        (schemeKernelIdeal (finalComponentι (translatedInitial (q + 1) (a i)) q idx)) ≅
      schemeKernelIdeal (exceptionalCurveι q n a i idx) :=
  baseChangeKernelIso (towerProjection (q + 1) n a i)
    (finalComponentι (translatedInitial (q + 1) (a i)) q idx) (isoOpen q n a i)
    (finalComponent_range_subset_isoOpen q n a ha i idx)

set_option maxHeartbeats 4000000 in
include ha in
/-- The kernel ideal of `E_{i,idx}` on `S_{p,n}` is invertible. -/
theorem exceptionalKernel_isInvertible (idx : FinalIndex.{0} q) :
    KltDP.SheafOfModules.IsInvertible (R := (multiSurface (q + 1) n a).ringCatSheaf)
      (schemeKernelIdeal (exceptionalCurveι q n a i idx)) :=
  isInvertible_baseChangeKernel (towerProjection (q + 1) n a i)
    (finalComponentι (translatedInitial (q + 1) (a i)) q idx) (isoOpen q n a i)
    (finalComponent_range_subset_isoOpen q n a ha i idx)
    (finalComponentKernel_isInvertible q n a i idx)

/-- The ideal line of `E_{i,idx}` on `S_{p,n}`. -/
def exceptionalKernelLine (idx : FinalIndex.{0} q) : InvertibleSheaf (multiSurface (q + 1) n a) :=
  ⟨schemeKernelIdeal (exceptionalCurveι q n a i idx),
    exceptionalKernel_isInvertible q n a ha i idx⟩

set_option maxHeartbeats 4000000 in
/-- **The class of `E_{i,idx}` on `S_{p,n}` is the pullback of the tower class.** -/
theorem neg_exceptionalKernelLine_toPic (idx : FinalIndex.{0} q) :
    -Additive.ofMul (exceptionalKernelLine q n a ha i idx).toPic =
      (schemePicardPullbackHom (towerProjection (q + 1) n a i)).toAdditive
        (-Additive.ofMul (InvertibleSheaf.toPic
          (⟨schemeKernelIdeal (finalComponentι (translatedInitial (q + 1) (a i)) q idx),
              finalComponentKernel_isInvertible q n a i idx⟩ :
            InvertibleSheaf (selectedStage (q + 1) (a i) (q + 1))))) :=
  neg_baseChangeKernelLine_toPic (towerProjection (q + 1) n a i)
    (finalComponentι (translatedInitial (q + 1) (a i)) q idx) (isoOpen q n a i)
    (finalComponent_range_subset_isoOpen q n a ha i idx)
    (finalComponentKernel_isInvertible q n a i idx)

/-! ## The tower classes of the final components -/

set_option maxHeartbeats 4000000 in
/-- The class of the older component `C_j` of the tower. -/
theorem finalComponentLine_toPic_inl (j : Fin q) :
    -Additive.ofMul (InvertibleSheaf.toPic
        (⟨schemeKernelIdeal (finalComponentι (translatedInitial (q + 1) (a i)) q (Sum.inl j)),
            finalComponentKernel_isInvertible q n a i (Sum.inl j)⟩ :
          InvertibleSheaf (selectedStage (q + 1) (a i) (q + 1)))) =
      translatedOldExceptionalStrictClass (q + 1) (a i) (q + 1) j.val (by omega) := by
  unfold translatedOldExceptionalStrictClass
  rw [toPic_eq_of_iso
    (⟨schemeKernelIdeal (finalComponentι (translatedInitial (q + 1) (a i)) q (Sum.inl j)),
        finalComponentKernel_isInvertible q n a i (Sum.inl j)⟩ :
      InvertibleSheaf (selectedStage (q + 1) (a i) (q + 1)))
    (translatedOldFinalKernelLine (q + 1) (a i) (q + 1) j.val (by omega)) (Iso.refl _)]

set_option maxHeartbeats 4000000 in
/-- The class of the newest component `P` of the tower. -/
theorem finalComponentLine_toPic_inr :
    -Additive.ofMul (InvertibleSheaf.toPic
        (⟨schemeKernelIdeal (finalComponentι (translatedInitial (q + 1) (a i)) q
              (Sum.inr PUnit.unit)),
            finalComponentKernel_isInvertible q n a i (Sum.inr PUnit.unit)⟩ :
          InvertibleSheaf (selectedStage (q + 1) (a i) (q + 1)))) =
      translatedStepExceptionalClass (q + 1) (a i) q := by
  unfold translatedStepExceptionalClass
  rw [toPic_eq_of_iso
    (⟨schemeKernelIdeal (finalComponentι (translatedInitial (q + 1) (a i)) q
          (Sum.inr PUnit.unit)),
        finalComponentKernel_isInvertible q n a i (Sum.inr PUnit.unit)⟩ :
      InvertibleSheaf (selectedStage (q + 1) (a i) (q + 1)))
    (translatedStepExceptionalIdealLine (q + 1) (a i) q) (Iso.refl _)]

/-! ## The global exceptional rows -/

set_option maxHeartbeats 4000000 in
/-- **The row `C_{ij} = E_{ij} − E_{i,j+1}` in `Pic S_{p,n}`.** -/
theorem chainClass_SPn (j : Fin q) :
    -Additive.ofMul (exceptionalKernelLine q n a ha i (Sum.inl j)).toPic =
      exceptionalClass (q + 1) n a i ⟨j.val, by omega⟩ -
        exceptionalClass (q + 1) n a i ⟨j.val + 1, by omega⟩ := by
  rw [neg_exceptionalKernelLine_toPic, finalComponentLine_toPic_inl,
    translatedOldExceptionalStrictClasses_tower, map_sub, exceptionalClass_eq_pullback,
    exceptionalClass_eq_pullback]

set_option maxHeartbeats 4000000 in
/-- **The row `P_i = E_{i,p}` in `Pic S_{p,n}`.** -/
theorem newestClass_SPn :
    -Additive.ofMul (exceptionalKernelLine q n a ha i (Sum.inr PUnit.unit)).toPic =
      exceptionalClass (q + 1) n a i (Fin.last q) := by
  rw [neg_exceptionalKernelLine_toPic, finalComponentLine_toPic_inr,
    ← translatedTotalExceptionalClass_last, exceptionalClass_eq_pullback]

/-- **The exceptional rows of the class table of `S_{p,n}`, in `Additive (Pic S_{p,n})` itself**:
the classes of the chain curves `C_{ij}` and of the newest curve `P_i` of every cluster, in terms of
the accepted total transforms `E_{ij}`. -/
theorem classTable_SPn_exceptional :
    (∀ j : Fin q, -Additive.ofMul (exceptionalKernelLine q n a ha i (Sum.inl j)).toPic =
        exceptionalClass (q + 1) n a i ⟨j.val, by omega⟩ -
          exceptionalClass (q + 1) n a i ⟨j.val + 1, by omega⟩) ∧
      (-Additive.ofMul (exceptionalKernelLine q n a ha i (Sum.inr PUnit.unit)).toPic =
        exceptionalClass (q + 1) n a i (Fin.last q)) :=
  ⟨fun j => chainClass_SPn q n a ha i j, newestClass_SPn q n a ha i⟩

end Distinct

end KltDP.Examples.FrobeniusMultiCentreExceptionalGlobalClasses

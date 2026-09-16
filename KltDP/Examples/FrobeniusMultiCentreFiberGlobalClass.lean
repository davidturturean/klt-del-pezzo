import KltDP.Examples.FrobeniusMultiCentreFiberIdealIso
import KltDP.Examples.FrobeniusMultiCentreExceptionalGlobalClasses
import KltDP.Examples.ProjectiveProductFiberClassInvariance
import KltDP.Examples.FrobeniusTowerTransportPicardRelation

/-!
# The global fibre row `F_i = b − Σ_j E_{ij}` in `Pic S_{p,n}`

`FrobeniusMultiCentreFiberIdeal` identifies the ideal of `F_i` with the ideal of the base change of
the tower's strict fibre, and the compiled `range_fiberClosureInclusion_subset_isoOpen` feeds the
queued `SchemeKernelBaseChangeIsoLocus.baseChangeKernelIso`; so the class of `F_i` on `S_{p,n}` is the
Picard pullback along `towerProjection` of the tower's fibre class.  The accepted tower relation
`translatedFiberClass_tower'` then gives the row, with `translatedSecondFiberClass` pulled back to the
accepted `multiSecondFiberClass` through `between_zero`, `towerProjection_projection` and the queued
`multiTranslatedSecondFiberClass_eq`, and the exceptional terms identified by the queued
`exceptionalClass_eq_pullback`:

  **`fiberClass_SPn : −[F_i] = b − Σ_j E_{ij}`** in `Additive (multiSurface (q+1) n a).Pic`.

This is the third row of Proposition 10.1 proved on `S_{p,n}` itself.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusMultiCentreFiberGlobalClass

open KltDP.Geometry KltDP.Geometry.SchemeKernelIdealIsoTransport
  KltDP.Geometry.SchemeKernelBaseChangeIsoLocus
open FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint FrobeniusGlobalBlowupStages
  FrobeniusExceptionalFinalConfiguration FrobeniusFiberClosure FrobeniusMultiCentreSurface
  FrobeniusMultiCentreGraphFiber FrobeniusMultiCentreGraphNewest FrobeniusMultiCentreCurveKernels
  FrobeniusTowerTransportClasses FrobeniusTowerTransportPicardRelation
  FrobeniusMultiCentreFiberRange FrobeniusMultiCentreFiberIdeal
  FrobeniusMultiCentreFiberIdealIso
  FrobeniusMultiCentreExceptionalGlobalClasses ProjectiveProductFiberClassInvariance

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] (q n : ℕ) (a : Fin n → k)

section Fibre

variable [IsAlgClosed k] [Fact (q + 1).Prime] [CharP k (q + 1)] (ha : Function.Injective a)
  (i : Fin n)

include ha in
/-- The ideal of `F_i` on `S_{p,n}` is invertible. -/
theorem fiberKernel_isInvertible :
    KltDP.SheafOfModules.IsInvertible (R := (multiSurface (q + 1) n a).ringCatSheaf)
      (schemeKernelIdeal (fiberStrictι (q + 1) n a i)) :=
  isInvertible_of_iso
    (isInvertible_baseChangeKernel (towerProjection (q + 1) n a i)
      (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1)) (isoOpen q n a i)
      (range_fiberClosureInclusion_subset_isoOpen q n a ha i)
      (translatedFiberKernelLine (q + 1) (a i) (q + 1)).property)
    (fiberKernelGlobalIso q n a ha i).symm

/-- The ideal line of `F_i` on `S_{p,n}`. -/
def fiberKernelLine : InvertibleSheaf (multiSurface (q + 1) n a) :=
  ⟨schemeKernelIdeal (fiberStrictι (q + 1) n a i), fiberKernel_isInvertible q n a ha i⟩

/-- **The class of `F_i` is the pullback along the tower projection of the tower's fibre class.** -/
theorem neg_fiberKernelLine_toPic :
    -Additive.ofMul (fiberKernelLine q n a ha i).toPic =
      (schemePicardPullbackHom (towerProjection (q + 1) n a i)).toAdditive
        (translatedFiberClass (q + 1) (a i) (q + 1)) := by
  rw [toPic_eq_of_iso (fiberKernelLine q n a ha i)
    (baseChangeKernelLine (towerProjection (q + 1) n a i)
      (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1)) (isoOpen q n a i)
      (range_fiberClosureInclusion_subset_isoOpen q n a ha i)
      (translatedFiberKernelLine (q + 1) (a i) (q + 1)).property)
    (fiberKernelGlobalIso q n a ha i)]
  exact neg_baseChangeKernelLine_toPic (towerProjection (q + 1) n a i)
    (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1)) (isoOpen q n a i)
    (range_fiberClosureInclusion_subset_isoOpen q n a ha i)
    (translatedFiberKernelLine (q + 1) (a i) (q + 1)).property

/-- The pullback of the tower's `b` is the accepted `multiSecondFiberClass`. -/
theorem pullback_translatedSecondFiberClass :
    (schemePicardPullbackHom (towerProjection (q + 1) n a i)).toAdditive
        ((schemePicardPullbackHom
            (between (translatedInitial (q + 1) (a i)) (Nat.zero_le (q + 1)))).toAdditive
          (translatedSecondFiberClass (q + 1) (a i))) =
      multiSecondFiberClass (q + 1) n a := by
  rw [← multiTranslatedSecondFiberClass_eq q n a i]
  unfold translatedSecondFiberClass multiTranslatedSecondFiberClass
  rw [map_neg, map_neg, between_zero]
  change -Additive.ofMul (schemePicardPullbackHom (towerProjection (q + 1) n a i)
      (schemePicardPullbackHom (selectedProjection (q + 1) (a i) (q + 1))
        (translatedHorizontalIdealLine (q + 1) (a i)).toPic)) = _
  rw [← MonoidHom.comp_apply, ← schemePicardPullbackHom_comp, towerProjection_projection,
    schemePicardPullbackHom_toPic]

/-- **The global fibre row of the class table of `S_{p,n}`:** `F_i = b − Σ_j E_{ij}`. -/
theorem fiberClass_SPn :
    -Additive.ofMul (fiberKernelLine q n a ha i).toPic =
      multiSecondFiberClass (q + 1) n a -
        ∑ j : Fin (q + 1), exceptionalClass (q + 1) n a i j := by
  rw [neg_fiberKernelLine_toPic q n a ha i, translatedFiberClass_tower', map_sub, map_sum,
    pullback_translatedSecondFiberClass q n a i]
  simp_rw [← exceptionalClass_eq_pullback q n a i]

end Fibre

end KltDP.Examples.FrobeniusMultiCentreFiberGlobalClass

import KltDP.Examples.FrobeniusMultiCentreRulingPairing
import KltDP.Examples.FrobeniusMultiCentreExceptionalPrime
import KltDP.Geometry.HodgeIndexReduction

/-!
# Every original total exceptional class is orthogonal to both rulings

The actual exceptional curves project to their original selected centre.
A base fibre at a different coordinate therefore has trivial kernel line
on the original composite curve morphism. Its actual restriction degree
is zero. Fibre-class invariance and the proved old/new exceptional class
identities give zero pairing of every original total exceptional class
with both original rulings. No contraction map or degree is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreExceptionalRulingRows

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
  KltDP.Geometry.PrimeCurveClassPairing KltDP.Geometry.KernelLinePullbackOffRange
open FrobeniusProjectivePoints FrobeniusUnaffectedFibers FrobeniusContactTowerSelectedPoint
  FrobeniusGraphPicardClassFiberClasses FrobeniusExceptionalFinalConfiguration
  FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral FrobeniusMultiCentreExceptional
  FrobeniusMultiCentreExceptionalPrime FrobeniusMultiCentreExceptionalGlobalClasses
  FrobeniusMultiCentreGraphExceptionalPairing FrobeniusMultiCentreRulingPairing
  ProjectiveProductFiberClassInvariance

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- Restriction degree on each original embedded exceptional prime curve. -/
abbrev exceptionalPairing (i : Fin n) (idx : FinalIndex.{0} q) :
    Additive (multiSurface (q + 1) n a).Pic →+ ℤ :=
  (multiSurfaceSurface (q + 1) n a ha hproj).picardRestrictionDegreeHom
    (exceptionalPrimeCurveSPn q n a ha i idx hproj)

/-- A base kernel line missing the original centre is trivial on the actual composite curve map. -/
theorem exceptionalPairing_baseKernel_zero (i : Fin n) (idx : FinalIndex.{0} q)
    {Z : Scheme.{u}} (g : Z ⟶ projectiveProduct k) [IsClosedImmersion g]
    (L : InvertibleSheaf (projectiveProduct k)) (hL : L.obj = schemeKernelIdeal g)
    (hg : graphPoint (q + 1) (a i) ∉ Set.range g.base) :
    exceptionalPairing q n a ha hproj i idx
      ((schemePicardPullbackHom (multiProjection (q + 1) n a)).toAdditive
        (-Additive.ofMul L.toPic)) = 0 := by
  let C := exceptionalPrimeCurveSPn q n a ha i idx hproj
  rw [map_neg, map_neg]
  change -(C.picardRestrictionDegree
    (schemePicardPullbackHom (multiProjection (q + 1) n a) L.toPic)) = 0
  rw [schemePicardPullbackHom_toPic, C.picardRestrictionDegree_toPic,
    C.restrictionDegree_pullback]
  have hd : Disjoint (Set.range (C.inclusion ≫ multiProjection (q + 1) n a).base)
      (Set.range g.base) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ hx
    have hC : C.inclusion.base x ∈ exceptionalSupport q n a i idx := by
      change C.inclusion.base x ∈ Set.range (exceptionalCurveι q n a i idx).base
      rw [← coe_exceptionalPrimeCurveSPn q n a ha i idx hproj, ← PrimeCurve.range_inclusion]
      exact ⟨x, rfl⟩
    have hπ : (multiProjection (q + 1) n a).base (C.inclusion.base x) =
        graphPoint (q + 1) (a i) :=
      exceptionalSupport_projection q n a i idx (C.inclusion.base x) hC
    change (multiProjection (q + 1) n a).base (C.inclusion.base x) ∈ Set.range g.base at hx
    exact hg (hπ ▸ hx)
  have e : (pullbackInvertibleSheaf (C.inclusion ≫ multiProjection (q + 1) n a) L).obj ≅
      _root_.SheafOfModules.unit C.toScheme.ringCatSheaf := by
    change (schemeModulePullback (C.inclusion ≫ multiProjection (q + 1) n a)).obj L.obj ≅ _
    rw [hL]
    exact kernelLine_pullback_unitIso g _ hd
  rw [C.lineDegree_eq_zero_of_iso_unit _ e, neg_zero]

theorem exceptionalPairing_firstFiber_zero (i : Fin n) (idx : FinalIndex.{0} q) :
    exceptionalPairing q n a ha hproj i idx (multiFirstFiberClass (q + 1) n a) = 0 := by
  rw [← pullback_firstFiberClass, ← verticalFiberClass_eq_firstFiberClass (a i + 1)]
  apply exceptionalPairing_baseKernel_zero q n a ha hproj i idx
    (verticalFiberMorphismAt (a i + 1)) (verticalFiberLine (a i + 1)) rfl
  rintro ⟨y, hy⟩
  have h := verticalFiber_avoids_center (q + 1) (a i) (a i + 1) (by simp) y
  rw [selected_center] at h
  exact h hy

theorem exceptionalPairing_secondFiber_zero (i : Fin n) (idx : FinalIndex.{0} q) :
    exceptionalPairing q n a ha hproj i idx (multiSecondFiberClass (q + 1) n a) = 0 := by
  rw [← pullback_secondFiberClass, ← horizontalFiberClass_eq_secondFiberClass (a i ^ (q + 1) + 1)]
  apply exceptionalPairing_baseKernel_zero q n a ha hproj i idx
    (FrobeniusGraphPicardClassZeroFiber.horizontalFiberMorphism (a i ^ (q + 1) + 1))
    (FrobeniusMultiCentreIsoOpenClasses.horizontalFiberLine (a i ^ (q + 1) + 1)) rfl
  rintro ⟨y, hy⟩
  have h := horizontalFiber_avoids_center (q + 1) (a i) (a i ^ (q + 1) + 1) (by simp) y
  rw [selected_center] at h
  exact h hy

theorem exceptionalKernel_firstFiber_pairing_zero (i : Fin n) (idx : FinalIndex.{0} q) :
    multiPairing (q + 1) n a ha hproj
      (-Additive.ofMul (exceptionalKernelLine q n a ha i idx).toPic)
      (multiFirstFiberClass (q + 1) n a) = 0 := by
  letI := exceptionalCurve_isIntegral q n a ha i idx
  exact (pairing_kernelLine_left (multiSurfaceSurface (q + 1) n a ha hproj)
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
    (exceptionalPrimeCurveSPn q n a ha i idx hproj) (exceptionalCurveι q n a i idx)
    (coe_exceptionalPrimeCurveSPn q n a ha i idx hproj)
    (exceptionalKernelLine q n a ha i idx) rfl (multiFirstFiberClass (q + 1) n a)).trans
    (exceptionalPairing_firstFiber_zero q n a ha hproj i idx)

theorem exceptionalKernel_secondFiber_pairing_zero (i : Fin n) (idx : FinalIndex.{0} q) :
    multiPairing (q + 1) n a ha hproj
      (-Additive.ofMul (exceptionalKernelLine q n a ha i idx).toPic)
      (multiSecondFiberClass (q + 1) n a) = 0 := by
  letI := exceptionalCurve_isIntegral q n a ha i idx
  exact (pairing_kernelLine_left (multiSurfaceSurface (q + 1) n a ha hproj)
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
    (exceptionalPrimeCurveSPn q n a ha i idx hproj) (exceptionalCurveι q n a i idx)
    (coe_exceptionalPrimeCurveSPn q n a ha i idx hproj)
    (exceptionalKernelLine q n a ha i idx) rfl (multiSecondFiberClass (q + 1) n a)).trans
    (exceptionalPairing_secondFiber_zero q n a ha hproj i idx)

theorem totalClass_firstFiber_pairing_zero (i : Fin n) (j : Fin (q + 1)) :
    multiPairing (q + 1) n a ha hproj (exceptionalClass (q + 1) n a i j)
      (multiFirstFiberClass (q + 1) n a) = 0 := by
  let f := (multiSurfaceSurface (q + 1) n a ha hproj).picardPairingHom
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj) (multiFirstFiberClass (q + 1) n a).toMul
  change f (exceptionalClass (q + 1) n a i j) = 0
  refine Fin.reverseInduction ?_ (fun r hr => ?_) j
  · have h : f (-Additive.ofMul (exceptionalKernelLine q n a ha i (.inr PUnit.unit)).toPic) = 0 :=
      exceptionalKernel_firstFiber_pairing_zero q n a ha hproj i (.inr PUnit.unit)
    rwa [newestClass_SPn] at h
  · have h : f (-Additive.ofMul (exceptionalKernelLine q n a ha i (.inl r)).toPic) = 0 :=
      exceptionalKernel_firstFiber_pairing_zero q n a ha hproj i (.inl r)
    have hC : -Additive.ofMul (exceptionalKernelLine q n a ha i (.inl r)).toPic =
        exceptionalClass (q + 1) n a i r.castSucc - exceptionalClass (q + 1) n a i r.succ :=
      chainClass_SPn q n a ha i r
    rwa [hC, map_sub, hr, sub_zero] at h

theorem totalClass_secondFiber_pairing_zero (i : Fin n) (j : Fin (q + 1)) :
    multiPairing (q + 1) n a ha hproj (exceptionalClass (q + 1) n a i j)
      (multiSecondFiberClass (q + 1) n a) = 0 := by
  let f := (multiSurfaceSurface (q + 1) n a ha hproj).picardPairingHom
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj) (multiSecondFiberClass (q + 1) n a).toMul
  change f (exceptionalClass (q + 1) n a i j) = 0
  refine Fin.reverseInduction ?_ (fun r hr => ?_) j
  · have h : f (-Additive.ofMul (exceptionalKernelLine q n a ha i (.inr PUnit.unit)).toPic) = 0 :=
      exceptionalKernel_secondFiber_pairing_zero q n a ha hproj i (.inr PUnit.unit)
    rwa [newestClass_SPn] at h
  · have h : f (-Additive.ofMul (exceptionalKernelLine q n a ha i (.inl r)).toPic) = 0 :=
      exceptionalKernel_secondFiber_pairing_zero q n a ha hproj i (.inl r)
    have hC : -Additive.ofMul (exceptionalKernelLine q n a ha i (.inl r)).toPic =
        exceptionalClass (q + 1) n a i r.castSucc - exceptionalClass (q + 1) n a i r.succ :=
      chainClass_SPn q n a ha i r
    rwa [hC, map_sub, hr, sub_zero] at h

theorem firstFiber_totalClass_pairing_zero (i : Fin n) (j : Fin (q + 1)) :
    multiPairing (q + 1) n a ha hproj (multiFirstFiberClass (q + 1) n a)
      (exceptionalClass (q + 1) n a i j) = 0 := by
  rw [multiPairing_symm]
  exact totalClass_firstFiber_pairing_zero q n a ha hproj i j

theorem secondFiber_totalClass_pairing_zero (i : Fin n) (j : Fin (q + 1)) :
    multiPairing (q + 1) n a ha hproj (multiSecondFiberClass (q + 1) n a)
      (exceptionalClass (q + 1) n a i j) = 0 := by
  rw [multiPairing_symm]
  exact totalClass_secondFiber_pairing_zero q n a ha hproj i j

end KltDP.Examples.FrobeniusMultiCentreExceptionalRulingRows

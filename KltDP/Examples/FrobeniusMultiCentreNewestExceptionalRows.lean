import KltDP.Examples.FrobeniusMultiCentreNewestExceptionalSelf

/-!
# The actual newest-exceptional row against ruling and total exceptional classes

The original newest curve contracts to the original closed centre under
the last step of its tower. Pullback classes therefore have degree zero.
Foreign components are actually disjoint; their kernel degrees and the
proved consecutive-total-class relations give the foreign total rows.
Together with the computed newest self-value this gives the full newest
row against the original ruling and total exceptional classes.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreNewestExceptionalRows

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
  KltDP.Geometry.PrimeCurveClassPairing
open FrobeniusBlowupContact FrobeniusProjectivePoints
  FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
  FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint
  FrobeniusExceptionalFinalConfiguration FrobeniusTowerTransportClasses
  FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassFiberClasses
  FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreExceptionalPrime
  FrobeniusMultiCentreExceptionalGlobalClasses FrobeniusMultiCentreNewestExceptionalSelf

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a)) (i : Fin n)

/-- Last-step pullbacks restrict trivially on the original newest exceptional curve. -/
theorem newestPairing_pullback_step
    (p : Additive (selectedStage (q + 1) (a i) q).Pic) :
    newestPairing q n a ha hproj i
      ((schemePicardPullbackHom (towerProjection (q + 1) n a i)).toAdditive
        ((schemePicardPullbackHom ((translatedInitial (q + 1) (a i)).stepProjection q)).toAdditive p)) =
      0 := by
  letI : (originPoint (k := k)).asIdeal.IsMaximal := centerIdeal_isMaximal
  letI : Field (planeRing k ⧸ (originPoint (k := k)).asIdeal) := Ideal.Quotient.field _
  letI := exceptionalCurve_isIntegral q n a ha i (.inr PUnit.unit)
  change (exceptionalPrimeCurveSPn q n a ha i (.inr PUnit.unit) hproj).picardRestrictionDegree
    (schemePicardPullbackHom (towerProjection (q + 1) n a i)
      (schemePicardPullbackHom ((translatedInitial (q + 1) (a i)).stepProjection q) p.toMul)) = 0
  rw [← MonoidHom.comp_apply, ← schemePicardPullbackHom_comp]
  apply PrimeCurveInclusionLift.picardRestrictionDegree_pullback_eq_zero
    (exceptionalPrimeCurveSPn q n a ha i (.inr PUnit.unit) hproj)
    (exceptionalCurveι q n a i (.inr PUnit.unit))
    (coe_exceptionalPrimeCurveSPn q n a ha i (.inr PUnit.unit) hproj)
    (towerProjection (q + 1) n a i ≫ (translatedInitial (q + 1) (a i)).stepProjection q)
    (exceptionalCurveToComponent q n a i (.inr PUnit.unit) ≫
      PointBlowupGluing.globalCenterFiberToCenter
        ((translatedInitial (q + 1) (a i)).stage q).chart (originPoint (k := k))
        ((translatedInitial (q + 1) (a i)).stage q).center_closed)
    (PointBlowupGluing.closedCenterInclusion
      ((translatedInitial (q + 1) (a i)).stage q).chart (originPoint (k := k))) _ p.toMul
  rw [← Category.assoc, exceptionalCurve_condition, Category.assoc, Category.assoc]
  congr 1
  exact CategoryTheory.Limits.pullback.condition

/-- Every original base-product Picard class has degree zero on the newest curve. -/
theorem newestPairing_base_pullback (p : Additive (projectiveProduct k).Pic) :
    newestPairing q n a ha hproj i
      ((schemePicardPullbackHom (multiProjection (q + 1) n a)).toAdditive p) = 0 := by
  have hπ : multiProjection (q + 1) n a = towerProjection (q + 1) n a i ≫
      ((translatedInitial (q + 1) (a i)).stepProjection q ≫ selectedProjection (q + 1) (a i) q) := by
    rw [← towerProjection_projection (q + 1) n a i]
    rfl
  change (exceptionalPrimeCurveSPn q n a ha i (.inr PUnit.unit) hproj).picardRestrictionDegree
    (schemePicardPullbackHom (multiProjection (q + 1) n a) p.toMul) = 0
  rw [hπ, schemePicardPullbackHom_comp, schemePicardPullbackHom_comp]
  exact newestPairing_pullback_step q n a ha hproj i
    ((schemePicardPullbackHom (selectedProjection (q + 1) (a i) q)).toAdditive p)

/-- The negative class of every actual base-line pullback also has degree zero. -/
theorem newestPairing_base_inverse_line (L : InvertibleSheaf (projectiveProduct k)) :
    newestPairing q n a ha hproj i
      (-Additive.ofMul (pullbackInvertibleSheaf (multiProjection (q + 1) n a) L).toPic) = 0 := by
  rw [map_neg]
  change -((exceptionalPrimeCurveSPn q n a ha i (.inr PUnit.unit) hproj).picardRestrictionDegree
    (pullbackInvertibleSheaf (multiProjection (q + 1) n a) L).toPic) = 0
  rw [← schemePicardPullbackHom_toPic]
  change -(newestPairing q n a ha hproj i
    ((schemePicardPullbackHom (multiProjection (q + 1) n a)).toAdditive (Additive.ofMul L.toPic))) = 0
  rw [newestPairing_base_pullback, neg_zero]

theorem newestPairing_firstFiber :
    newestPairing q n a ha hproj i (multiFirstFiberClass (q + 1) n a) = 0 :=
  newestPairing_base_inverse_line q n a ha hproj i (verticalFiberIdealLine (k := k))

theorem newestPairing_secondFiber :
    newestPairing q n a ha hproj i (multiSecondFiberClass (q + 1) n a) = 0 :=
  newestPairing_base_inverse_line q n a ha hproj i (graphIdealLine (k := k) 0)

/-- Every earlier total exceptional class in this tower is a last-step pullback. -/
theorem newestPairing_total_castSucc (j : Fin q) :
    newestPairing q n a ha hproj i (exceptionalClass (q + 1) n a i j.castSucc) = 0 := by
  rw [exceptionalClass_eq_pullback]
  change (exceptionalPrimeCurveSPn q n a ha i (.inr PUnit.unit) hproj).picardRestrictionDegree
    (schemePicardPullbackHom (towerProjection (q + 1) n a i)
      (schemePicardPullbackHom (between (translatedInitial (q + 1) (a i)) j.castSucc.isLt)
        (translatedStepExceptionalClass (q + 1) (a i) j.val).toMul)) = 0
  rw [between_succ (translatedInitial (q + 1) (a i)) j.isLt, schemePicardPullbackHom_comp]
  exact newestPairing_pullback_step q n a ha hproj i
    ((schemePicardPullbackHom (between (translatedInitial (q + 1) (a i)) j.isLt)).toAdditive
      (translatedStepExceptionalClass (q + 1) (a i) j.val))

/-- The actual foreign exceptional kernel lines have degree zero, by original support disjointness. -/
theorem newestPairing_foreign_kernel (i' : Fin n) (hii' : i ≠ i') (idx : FinalIndex.{0} q) :
    newestPairing q n a ha hproj i
      (-Additive.ofMul (exceptionalKernelLine q n a ha i' idx).toPic) = 0 := by
  apply restrictionDegreeHom_neg_kernel_zero (multiSurfaceSurface (q + 1) n a ha hproj)
    (exceptionalPrimeCurveSPn q n a ha i (.inr PUnit.unit) hproj)
    (exceptionalCurveι q n a i' idx) (exceptionalKernelLine q n a ha i' idx) rfl
  rw [PrimeCurve.range_inclusion, coe_exceptionalPrimeCurveSPn]
  exact exceptionalSupport_disjoint_of_ne q n a ha hii' (.inr PUnit.unit) idx

/-- The original consecutive-component relations give degree zero for every foreign total class. -/
theorem newestPairing_foreign_total (i' : Fin n) (hii' : i ≠ i') (j : Fin (q + 1)) :
    newestPairing q n a ha hproj i (exceptionalClass (q + 1) n a i' j) = 0 := by
  refine Fin.reverseInduction ?_ (fun r hr => ?_) j
  · have h := newestPairing_foreign_kernel q n a ha hproj i i' hii' (.inr PUnit.unit)
    rwa [newestClass_SPn] at h
  · have h := newestPairing_foreign_kernel q n a ha hproj i i' hii' (.inl r)
    have hC : -Additive.ofMul (exceptionalKernelLine q n a ha i' (.inl r)).toPic =
        exceptionalClass (q + 1) n a i' r.castSucc - exceptionalClass (q + 1) n a i' r.succ :=
      chainClass_SPn q n a ha i' r
    rwa [hC, map_sub, hr, sub_zero] at h

/-- The actual newest curve paired with every original total exceptional class. -/
theorem newestPairing_total (i' : Fin n) (j : Fin (q + 1)) :
    newestPairing q n a ha hproj i (exceptionalClass (q + 1) n a i' j) =
      if i' = i then if j = Fin.last q then -1 else 0 else 0 := by
  classical
  by_cases hi : i' = i
  · subst i'
    rw [if_pos rfl]
    rcases Fin.eq_castSucc_or_eq_last j with ⟨r, rfl⟩ | rfl
    · rw [if_neg (Fin.castSucc_lt_last r).ne]
      exact newestPairing_total_castSucc q n a ha hproj i r
    · rw [if_pos rfl]
      exact newestPairing_total_last q n a ha hproj i
  · rw [if_neg hi]
    exact newestPairing_foreign_total q n a ha hproj i i' (Ne.symm hi) j

/-- The full original exceptional sum has degree minus one on the newest curve. -/
theorem newestPairing_sum_total :
    newestPairing q n a ha hproj i
      (∑ i' : Fin n, ∑ j : Fin (q + 1), exceptionalClass (q + 1) n a i' j) = -1 := by
  classical
  simp only [map_sum, newestPairing_total]
  simp

end KltDP.Examples.FrobeniusMultiCentreNewestExceptionalRows

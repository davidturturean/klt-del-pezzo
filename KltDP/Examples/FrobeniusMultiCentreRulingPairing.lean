import KltDP.Geometry.IsomorphismLocusPullbackPairing
import KltDP.Examples.FrobeniusMultiCentreGraphExceptionalPairing
import KltDP.Examples.FrobeniusRulingPairingValues

/-!
# The actual ruling pairing on the multi-centre surface

Choose an actual vertical or horizontal fibre avoiding the finite selected
centres. The original multi-projection is an isomorphism over that fibre.
The proved kernel base-change and curve-degree transport therefore
compute its pairing with every base-pulled class as the corresponding
pairing on the original projective product. The accepted product rows
give `a² = b² = 0` and `a.b = b.a = 1` on the original multi-surface.
No characteristic restriction or separate tower projectivity is needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreRulingPairing

open KltDP.Geometry KltDP.Geometry.IsomorphismLocusPullbackPairing
open FrobeniusProjectivePoints FrobeniusUnaffectedFibers FrobeniusContactTowerSelectedPoint
  FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassFiberClasses
  FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral FrobeniusMultiCentreGraphFiber
  FrobeniusMultiCentreGraphExceptionalPairing FrobeniusStageZeroProjective
  ProjectiveProductFiberClassInvariance FrobeniusRulingClassPairing FrobeniusRulingPairingValues

variable {k : Type u} [Field k] [IsAlgClosed k]
  (p n : ℕ) (a : Fin n → k)

/-- The original first ruling is the Picard pullback of the original product ruling. -/
theorem pullback_firstFiberClass :
    (schemePicardPullbackHom (multiProjection p n a)).toAdditive firstFiberClass =
      multiFirstFiberClass p n a := by
  unfold firstFiberClass multiFirstFiberClass
  rw [map_neg]
  change -Additive.ofMul (schemePicardPullbackHom (multiProjection p n a)
    (verticalFiberIdealLine (k := k)).toPic) = _
  rw [schemePicardPullbackHom_toPic]

/-- The original second ruling is the Picard pullback of the original product ruling. -/
theorem pullback_secondFiberClass :
    (schemePicardPullbackHom (multiProjection p n a)).toAdditive secondFiberClass =
      multiSecondFiberClass p n a := by
  unfold secondFiberClass multiSecondFiberClass
  rw [map_neg]
  change -Additive.ofMul (schemePicardPullbackHom (multiProjection p n a)
    (graphIdealLine (k := k) 0).toPic) = _
  rw [schemePicardPullbackHom_toPic]

/-- An actual vertical fibre avoiding all selected first coordinates lies in the isomorphism open. -/
theorem verticalRange_subset_centersComplement (c : k) (hc : ∀ i, c ≠ a i) :
    Set.range (verticalFiberMorphismAt c).base ⊆ (centersComplement p n a : Set (projectiveProduct k)) := by
  rintro _ ⟨y, rfl⟩
  change (verticalFiberMorphismAt c).base y ∈ centersComplement p n a
  rw [mem_centersComplement_iff]
  intro i
  simpa only [selected_center] using verticalFiber_avoids_center p (a i) c (hc i) y

/-- The analogous actual horizontal fibre lies in the same isomorphism open. -/
theorem horizontalRange_subset_centersComplement (c : k) (hc : ∀ i, c ≠ a i ^ p) :
    Set.range (FrobeniusGraphPicardClassZeroFiber.horizontalFiberMorphism c).base ⊆ (centersComplement p n a : Set (projectiveProduct k)) := by
  rintro _ ⟨y, rfl⟩
  change (FrobeniusGraphPicardClassZeroFiber.horizontalFiberMorphism c).base y ∈ centersComplement p n a
  rw [mem_centersComplement_iff]
  intro i
  simpa only [selected_center] using horizontalFiber_avoids_center p (a i) c (hc i) y

variable (ha : Function.Injective a) (hproj : IsProjectiveOverField (multiStructure p n a))

/-- Pairing with the original first ruling commutes with every original base Picard pullback. -/
theorem multiPairing_first_pullback (z : Additive (projectiveProduct k).Pic) :
    multiPairing p n a ha hproj (multiFirstFiberClass p n a)
      ((schemePicardPullbackHom (multiProjection p n a)).toAdditive z) =
      basePairing firstFiberClass z := by
  classical
  obtain ⟨c, hc⟩ := Infinite.exists_not_mem_finset (Finset.univ.image a)
  have hc' : ∀ i, c ≠ a i := by
    intro i hi
    exact hc (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.symm⟩)
  letI := multiProjection_restrict_centersComplement_isIso p n a
  have h := pairing_pullback_projectiveLine_kernel
    (multiSurfaceSurface p n a ha hproj) (projectiveProductSurface (k := k))
    (multiSurfaceSurface_regularPoints p n a ha hproj) baseRegular
    (multiProjection p n a) rfl (verticalFiberMorphismAt c) (centersComplement p n a)
    (verticalRange_subset_centersComplement p n a c hc') (verticalFiberKernel_isInvertible c) z
  change multiPairing p n a ha hproj
    ((schemePicardPullbackHom (multiProjection p n a)).toAdditive
      (-Additive.ofMul (verticalFiberLine c).toPic))
    ((schemePicardPullbackHom (multiProjection p n a)).toAdditive z) =
      basePairing (-Additive.ofMul (verticalFiberLine c).toPic) z at h
  rw [verticalFiberClass_eq_firstFiberClass, pullback_firstFiberClass] at h
  exact h

set_option maxHeartbeats 800000 in
/-- Pairing with the original second ruling commutes with every original base Picard pullback. -/
theorem multiPairing_second_pullback (z : Additive (projectiveProduct k).Pic) :
    multiPairing p n a ha hproj (multiSecondFiberClass p n a)
      ((schemePicardPullbackHom (multiProjection p n a)).toAdditive z) =
      basePairing secondFiberClass z := by
  classical
  obtain ⟨c, hc⟩ := Infinite.exists_not_mem_finset (Finset.univ.image (fun i => a i ^ p))
  have hc' : ∀ i, c ≠ a i ^ p := by
    intro i hi
    exact hc (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.symm⟩)
  letI := multiProjection_restrict_centersComplement_isIso p n a
  have h := pairing_pullback_projectiveLine_kernel
    (multiSurfaceSurface p n a ha hproj) (projectiveProductSurface (k := k))
    (multiSurfaceSurface_regularPoints p n a ha hproj) baseRegular
    (multiProjection p n a) rfl (FrobeniusGraphPicardClassZeroFiber.horizontalFiberMorphism c) (centersComplement p n a)
    (horizontalRange_subset_centersComplement p n a c hc')
    (FrobeniusMultiCentreIsoOpenClasses.horizontalFiberKernel_isInvertible c) z
  change multiPairing p n a ha hproj
    ((schemePicardPullbackHom (multiProjection p n a)).toAdditive
      (-Additive.ofMul (FrobeniusMultiCentreIsoOpenClasses.horizontalFiberLine c).toPic))
    ((schemePicardPullbackHom (multiProjection p n a)).toAdditive z) =
      basePairing (-Additive.ofMul (FrobeniusMultiCentreIsoOpenClasses.horizontalFiberLine c).toPic) z at h
  rw [horizontalFiberClass_eq_secondFiberClass, pullback_secondFiberClass] at h
  exact h

theorem multiPairing_first_self_zero :
    multiPairing p n a ha hproj (multiFirstFiberClass p n a) (multiFirstFiberClass p n a) = 0 := by
  have h := multiPairing_first_pullback p n a ha hproj firstFiberClass
  rw [pullback_firstFiberClass] at h
  exact h.trans basePairing_first_self_zero

theorem multiPairing_second_self_zero :
    multiPairing p n a ha hproj (multiSecondFiberClass p n a) (multiSecondFiberClass p n a) = 0 := by
  have h := multiPairing_second_pullback p n a ha hproj secondFiberClass
  rw [pullback_secondFiberClass] at h
  exact h.trans basePairing_second_self_zero

theorem multiPairing_first_second_one :
    multiPairing p n a ha hproj (multiFirstFiberClass p n a) (multiSecondFiberClass p n a) = 1 := by
  have h := multiPairing_first_pullback p n a ha hproj secondFiberClass
  rw [pullback_secondFiberClass] at h
  exact h.trans basePairing_first_second_one

theorem multiPairing_second_first_one :
    multiPairing p n a ha hproj (multiSecondFiberClass p n a) (multiFirstFiberClass p n a) = 1 := by
  rw [multiPairing_symm]
  exact multiPairing_first_second_one p n a ha hproj

end KltDP.Examples.FrobeniusMultiCentreRulingPairing

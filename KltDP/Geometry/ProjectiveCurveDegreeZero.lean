import KltDP.Geometry.CurveGloballyGeneratedDegreeZero
import KltDP.Geometry.ProjectiveMapTrivialPullback

/-!
# Degree zero forces an original projective map of a proper integral curve to be constant

The pulled original homogeneous sections generate the actual pullback of
O(1). If its original Euler degree is zero, the degree-zero Cartier
argument gives an actual unit frame. The original map therefore factors
through a point over the original base field.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.ProjectiveCurveDegreeZero

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSectionNonvanishingOpen InvertibleSectionNonvanishingPullback
open ProjectiveSpaceDegreeOneSheaf ProjectiveCoordinateSectionBasicOpen

variable {k : Type u} [Field k] {Y : Scheme.{u}} {n : ℕ}

/-- Pulling back the actual homogeneous sections generates the original pulled line. -/
theorem pullback_degreeOne_isGloballyGenerated (g : Y ⟶ projectiveSpace k n) :
    Positivity.IsGloballyGenerated (pullbackInvertibleSheaf g (degreeOne k n)).obj := by
  let L := pullbackInvertibleSheaf g (degreeOne k n)
  let s : ULift.{u} (Fin (n + 1)) → L.obj.sections :=
    fun i => InvertibleSheafSectionPowersPullback.pullbackSection g
      (degreeOne k n).obj (homogeneousSection k n i.down)
  have hs (i : ULift.{u} (Fin (n + 1))) :
      nonvanishingOpen Y L (s i) = g ⁻¹ᵁ standardOpen k n i.down :=
    (nonvanishingOpen_pullback g (degreeOne k n) (homogeneousSection k n i.down)).trans
      (congrArg (fun U => g ⁻¹ᵁ U) (nonvanishingOpen_homogeneousSection k n i.down))
  have hcover : (⨆ i, nonvanishingOpen Y L (s i)) = ⊤ :=
    (iSup_congr hs).trans
      (g.preimage_iSup_eq_top (ProjectiveSpaceDegreeOneSheaf.chart_cover k n))
  exact ⟨ULift.{u} (Fin (n + 1)), L.obj.freeHomEquiv.symm s,
    FiniteGeneratingSections.epi_of_nonvanishing_cover L s hcover⟩

variable [IsAlgClosed k] [IsIntegral Y]
  (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]
  (hdim : topologicalKrullDim Y ≤ 1)

include hdim in
/-- Original Euler degree zero forces the given original map to factor through a k-point. -/
theorem factors_through_structure_of_degree_zero (g : Y ⟶ projectiveSpace k n)
    (hgf : g ≫ projectiveSpaceToSpec k n = f)
    (hdeg : eulerCharacteristic f (pullbackInvertibleSheaf g (degreeOne k n)).obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf) = 0) :
    ∃ p : Spec (CommRingCat.of k) ⟶ projectiveSpace k n,
      g = f ≫ p ∧ p ≫ projectiveSpaceToSpec k n = 𝟙 _ := by
  let e := CurveGloballyGeneratedDegreeZero.unitIso_of_globallyGenerated_degree_zero
    f hdim (pullbackInvertibleSheaf g (degreeOne k n)) hdeg
    (pullback_degreeOne_isGloballyGenerated g)
  exact ProjectiveMapTrivialPullback.factors_through_structure f g e hgf

end KltDP.Geometry.ProjectiveCurveDegreeZero

import KltDP.Geometry.ProperCurveDegreeZeroNonvanishing
import KltDP.Geometry.ProperIntegralAffineImage
import KltDP.Geometry.ProjectiveLineDegreeOneSections
import KltDP.Geometry.InvertibleSectionNonvanishingPullback
import KltDP.Geometry.ProjectiveProper

/-!
# Degree-zero coordinate pullback forces an actual constant ruling image

One original homogeneous coordinate is nonvanishing at the image of the
generic point. The degree-zero pullback makes that same coordinate
nonvanishing everywhere. Thus the whole image lies in its original
affine chart, and the proper integral affine-image theorem gives one
point. For an original morphism over the base field this point is closed.

The proof applies over any field, and in particular over an algebraically
closed field. No constant-map, fiber, or verticality hypothesis is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.ProjectiveLineDegreeZeroImage

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open RationalTreePicard ProjectiveLineComparison ProjectiveLineDegreeOneSections
open InvertibleSectionNonvanishingOpen InvertibleSectionNonvanishingPullback

variable {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y]
  (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]
  (hdim : topologicalKrullDim Y ≤ 1)
  (g : Y ⟶ projectiveSpace k 1)
  (hdeg : eulerCharacteristic f (pullbackInvertibleSheaf g (monomialLineBundle k 1)).obj -
    eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf) = 0)

include f hdim g hdeg

/-- Degree zero places the actual image in one of the two original
standard affine charts, using its original pulled coordinate section. -/
theorem exists_standard_chart :
    ∃ i : ULift.{u} (Fin 2), Set.range g.base ⊆ chartOpen k i.down := by
  obtain ⟨i, hi⟩ := ProjectiveLineCanonicalFrame.chartOpen_cover k
    (g.base (genericPoint Y))
  let L := pullbackInvertibleSheaf g (monomialLineBundle k 1)
  let s := InvertibleSheafSectionPowersPullback.pullbackSection g
    (monomialLineBundle k 1).obj (standardSection k i)
  have hopen : nonvanishingOpen Y L s = g ⁻¹ᵁ chartOpen k i.down := by
    exact (nonvanishingOpen_pullback g (monomialLineBundle k 1) (standardSection k i)).trans
      (congrArg (fun U => g ⁻¹ᵁ U) (nonvanishingOpen_standardSection k i))
  have htop : nonvanishingOpen Y L s = ⊤ := by
    apply ProperCurveDegreeZeroNonvanishing.nonvanishingOpen_eq_top_of_nonempty
      f hdim L hdeg s
    refine ⟨genericPoint Y, ?_⟩
    rw [hopen]
    exact hi
  refine ⟨i, ?_⟩
  rintro _ ⟨y, rfl⟩
  have hy : y ∈ nonvanishingOpen Y L s := by rw [htop]; trivial
  rwa [hopen] at hy

/-- Zero degree of the original coordinate pullback forces the actual
underlying projective-line image to have at most one point. -/
theorem range_subsingleton : (Set.range g.base).Subsingleton := by
  obtain ⟨i, hi⟩ := exists_standard_chart f hdim g hdeg
  exact ProperIntegralAffineImage.range_subsingleton_of_affine_open f g
    (chartOpen k i.down) (chartOpen_isAffineOpen k i.down) hi

/-- An original degree-zero ruling map over the original base field
has exactly one closed image point. The point is its actual generic image. -/
theorem exists_closed_point_range_eq_singleton
    (hbase : g ≫ projectiveSpaceToSpec k 1 = f) :
    ∃ q : projectiveSpace k 1, IsClosed ({q} : Set (projectiveSpace k 1)) ∧
      Set.range g.base = {q} := by
  haveI : IsProper (g ≫ projectiveSpaceToSpec k 1) := by rw [hbase]; infer_instance
  haveI : IsProper g := IsProper.of_comp_of_isSeparated g (projectiveSpaceToSpec k 1)
  have hs := range_subsingleton f hdim g hdeg
  have hrange : Set.range g.base = {g.base (genericPoint Y)} := by
    ext q
    constructor
    · intro hq
      exact Set.mem_singleton_iff.mpr (hs hq (Set.mem_range_self (genericPoint Y)))
    · rintro rfl
      exact Set.mem_range_self (genericPoint Y)
  refine ⟨g.base (genericPoint Y), ?_, hrange⟩
  rw [← hrange]
  exact g.isClosedMap.isClosed_range

end KltDP.Geometry.ProjectiveLineDegreeZeroImage

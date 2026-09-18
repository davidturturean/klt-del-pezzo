import KltDP.Examples.FrobeniusMultiCentreContractingNef
import KltDP.Geometry.ProjectiveLineDegreeZeroImage

/-!
# Actual null curves of M are vertical away from the strict graph

The proved all-prime positivity argument identifies zero M-degree off the
graph with disjointness from that graph and zero degree against the original
second ruling. The actual degree-zero image theorem then proves that the
original curve maps to one closed point under the original second ruling.
No fiber classification or constancy premise is introduced.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Examples.FrobeniusMultiCentreContractingNullRuling

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusGraphClosed FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusMultiCentreGraphExceptionalPairing
open FrobeniusMultiCentreRulingNefClasses FrobeniusMultiCentreRulingNef
open FrobeniusMultiCentreContractingClass FrobeniusMultiCentreContractingNef

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))
  (C : (multiSurfaceSurface (q + 1) n a ha hproj).PrimeCurve)

/-- The original curve's morphism to the original second projective-line ruling. -/
def rulingMap : C.toScheme ⟶ projectiveSpace k 1 :=
  C.inclusion ≫ (multiProjection (q + 1) n a ≫ secondProjection)

/-- This actual ruling morphism respects the original field structures. -/
theorem rulingMap_structure :
    rulingMap q n a ha hproj C ≫ projectiveSpaceToSpec k 1 = C.toSpec := by
  simp only [rulingMap, Category.assoc]
  change C.inclusion ≫ multiProjection (q + 1) n a ≫
    secondProjection ≫ projectiveSpaceToSpec k 1 =
    C.inclusion ≫ multiProjection (q + 1) n a ≫
      firstProjection ≫ projectiveSpaceToSpec k 1
  rw [show firstProjection ≫ projectiveSpaceToSpec k 1 =
    secondProjection ≫ projectiveSpaceToSpec k 1 from pullback.condition]

/-- The exact geometric criterion for an off-graph prime to have zero M-degree. -/
theorem null_iff_disjoint_and_ruling_degree_zero (hn : 2 < n)
    (hC : C ≠ graphPrimeCurve q n a ha hproj) :
    (multiSurfaceSurface (q + 1) n a ha hproj).picardRestrictionDegreeHom C
        (contractingClass q n a ha) = 0 ↔
      Disjoint (C : Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme)
        (graphPrimeCurve q n a ha hproj : Set _) ∧
      (multiSurfaceSurface (q + 1) n a ha hproj).picardRestrictionDegreeHom C
        (Additive.ofMul (secondRulingLine (q + 1) n a).toPic) = 0 := by
  rw [contractingClass_eq_curveNefSum q n a ha hproj hn.le]
  exact PrimeCurveNefSum.degree_eq_zero_iff_of_ne _ _ _ _ _
    (by omega) (secondRulingLine_isNef (q + 1) n a ha hproj) C hC

/-- Every actual off-graph M-null prime has a single closed original ruling image. -/
theorem null_curve_has_closed_ruling_image (hn : 2 < n)
    (hC : C ≠ graphPrimeCurve q n a ha hproj)
    (hnull : (multiSurfaceSurface (q + 1) n a ha hproj).picardRestrictionDegreeHom C
      (contractingClass q n a ha) = 0) :
    ∃ z : projectiveSpace k 1, IsClosed ({z} : Set (projectiveSpace k 1)) ∧
      Set.range (rulingMap q n a ha hproj C).base = {z} := by
  have hz := ((null_iff_disjoint_and_ruling_degree_zero q n a ha hproj C hn hC).mp hnull).2
  change C.picardRestrictionDegree (secondRulingLine (q + 1) n a).toPic = 0 at hz
  rw [C.picardRestrictionDegree_toPic] at hz
  letI : IsProper C.toSpec := C.toSpec_isProper
  have hdim : topologicalKrullDim C.toScheme ≤ 1 := le_of_eq C.dimension_one_toScheme
  have hpull : C.lineDegree (pullbackInvertibleSheaf C.inclusion
      (secondRulingLine (q + 1) n a)) =
      C.lineDegree (pullbackInvertibleSheaf (rulingMap q n a ha hproj C)
        (RationalTreePicard.monomialLineBundle k 1)) :=
    C.lineDegree_eq_of_iso ((schemeModulePullbackCompIso C.inclusion
      (multiProjection (q + 1) n a ≫ secondProjection)).app
        (RationalTreePicard.monomialLineBundle k 1).obj)
  have hdegree : ModuleCohomology.eulerCharacteristic C.toSpec
      (pullbackInvertibleSheaf (rulingMap q n a ha hproj C)
        (RationalTreePicard.monomialLineBundle k 1)).obj -
      ModuleCohomology.eulerCharacteristic C.toSpec
        (_root_.SheafOfModules.unit C.toScheme.ringCatSheaf) = 0 :=
    hpull.symm.trans hz
  exact ProjectiveLineDegreeZeroImage.exists_closed_point_range_eq_singleton
    C.toSpec hdim (rulingMap q n a ha hproj C) hdegree
    (rulingMap_structure q n a ha hproj C)

end KltDP.Examples.FrobeniusMultiCentreContractingNullRuling

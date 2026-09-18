import KltDP.Geometry.LinearSystemRationalMap
import KltDP.Geometry.LinearSystemNonBaseNonempty
import KltDP.Geometry.ProperInvertibleSectionBasis
import KltDP.Geometry.CompleteLinearSystemSectionTuple

/-!
# The actual rational map of the complete linear system

The coordinates are exactly `positiveBasisSections`: the original
base-field basis of all H0, reindexed to a tuple of its exact dimension.
Its original top values form `positiveTopSectionBasis`, as proved by
`positiveBasisSections_top`; their independence and spanning are proved
in the imported producer. No coordinate is added or discarded.

A nonzero basis entry makes the actual non-base open nonempty. On an
integral source this open is dense, yielding the existing partial and
rational maps over the original field. The actual projective degree-one
sheaf pulls back to the original line on this open. No global generation
or birationality is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.CompleteLinearSystemMap

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open CompleteLinearSystemSections InvertibleSectionNonvanishingOpen

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (L : InvertibleSheaf X)
  [IsProper f] [IsIntegral X] (hpos : 0 < dimension f L)

/-- The original non-base open of the whole original H0 basis. -/
def nonBaseOpen : X.Opens :=
  LinearSystemRationalMap.nonBaseOpen L (positiveBasisSections f L hpos)

/-- The original first basis section proves that this open is nonempty. -/
theorem nonBaseOpen_nonempty : (nonBaseOpen f L hpos : Set X).Nonempty :=
  LinearSystemRationalMap.nonBaseOpen_nonempty_of_top_ne_zero
    L (positiveBasisSections f L hpos) 0
    (positiveBasisSections_top_ne_zero f L hpos 0)

/-- The actual non-base open is dense in the original integral source. -/
theorem nonBaseOpen_dense : Dense (nonBaseOpen f L hpos : Set X) :=
  LinearSystemRationalMap.nonBaseOpen_dense L (positiveBasisSections f L hpos)
    (nonBaseOpen_nonempty f L hpos)

/-- The original complete-system morphism on its actual non-base open. -/
def morphism : (nonBaseOpen f L hpos).toScheme ⟶
    projectiveSpace k (dimension f L - 1) :=
  LinearSystemRationalMap.morphism L (positiveBasisSections f L hpos) f

/-- The complete-system morphism preserves the original field structure. -/
theorem morphism_structure :
    morphism f L hpos ≫ projectiveSpaceToSpec k (dimension f L - 1) =
      (nonBaseOpen f L hpos).ι ≫ f :=
  LinearSystemRationalMap.morphism_structure L (positiveBasisSections f L hpos) f

/-- The actual degree-one pullback is the original line restricted to the non-base open. -/
def pullbackDegreeOneIso :
    (pullbackInvertibleSheaf (morphism f L hpos)
      (ProjectiveSpaceDegreeOneSheaf.degreeOne k (dimension f L - 1))).obj ≅
        (pullbackInvertibleSheaf (nonBaseOpen f L hpos).ι L).obj :=
  LinearSystemRationalMap.pullbackDegreeOneIso L (positiveBasisSections f L hpos) f

/-- Each projective coordinate retains the nonvanishing locus of its actual basis section. -/
theorem morphism_preimage_coordinateChart (i : Fin ((dimension f L - 1) + 1)) :
    morphism f L hpos ⁻¹ᵁ
      (ProjectiveChart.coordinateChartMorphism k (dimension f L - 1) i).opensRange =
        (nonBaseOpen f L hpos).ι ⁻¹ᵁ
          nonvanishingOpen X L (positiveBasisSections f L hpos i) :=
  LinearSystemRationalMap.morphism_preimage_coordinateChart
    L (positiveBasisSections f L hpos) f i

/-- Mathlib's original partial map for the complete system of all original H0. -/
def partialMap : X.PartialMap (projectiveSpace k (dimension f L - 1)) :=
  LinearSystemRationalMap.partialMap L (positiveBasisSections f L hpos) f
    (nonBaseOpen_nonempty f L hpos)

/-- Its domain is the actual non-base open of the whole original basis. -/
theorem partialMap_domain : (partialMap f L hpos).domain = nonBaseOpen f L hpos := rfl

/-- The original complete linear system as Mathlib's rational-map class. -/
def rationalMap : X ⤏ projectiveSpace k (dimension f L - 1) :=
  LinearSystemRationalMap.rationalMap L (positiveBasisSections f L hpos) f
    (nonBaseOpen_nonempty f L hpos)

/-- This rational map is over the original field in the existing rational-map quotient. -/
theorem rationalMap_structure :
    (rationalMap f L hpos).compHom (projectiveSpaceToSpec k (dimension f L - 1)) =
      f.toRationalMap :=
  LinearSystemRationalMap.rationalMap_structure L (positiveBasisSections f L hpos) f
    (nonBaseOpen_nonempty f L hpos)

end KltDP.Geometry.CompleteLinearSystemMap

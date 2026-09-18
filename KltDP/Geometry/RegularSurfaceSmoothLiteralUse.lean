import KltDP.Literature.RegularSmoothLociLiteral
import KltDP.Literature.SmoothStandardCoverLiteral
import KltDP.Geometry.RegularSurfaceSmoothConditional

/-! Original-morphism consumers of the two separately admitted source statements. -/
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry

/-- Regular reduced locally finite type schemes over the original perfect field
are smooth for their original structure morphism. -/
theorem isSmooth_of_regularPoints_perfectField
    {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hreg : ∀ x, RegularPoint X x) : IsSmooth f :=
  RegularSchemeSmoothConditional.isSmooth_of_regularPoints
    Literature.Stacks.regular_smooth_loci_perfect_literal
    Literature.Stacks.smooth_standardSmooth_cover_literal f hreg

/-- The original regular normal projective surface is smooth of relative dimension two. -/
theorem NormalProjectiveSurface.isSmoothOfRelativeDimension_two_of_regularPoints
    {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
    (hreg : ∀ x, RegularPoint X.toScheme x) :
    IsSmoothOfRelativeDimension 2 X.structureMorphism :=
  X.isSmoothOfRelativeDimension_two_of_regularPoints_of_native_sources
    Literature.Stacks.regular_smooth_loci_perfect_literal
    Literature.Stacks.smooth_standardSmooth_cover_literal hreg

end KltDP.Geometry
#check @KltDP.Geometry.isSmooth_of_regularPoints_perfectField
#print axioms KltDP.Geometry.isSmooth_of_regularPoints_perfectField
#check @KltDP.Geometry.NormalProjectiveSurface.isSmoothOfRelativeDimension_two_of_regularPoints
#print axioms KltDP.Geometry.NormalProjectiveSurface.isSmoothOfRelativeDimension_two_of_regularPoints

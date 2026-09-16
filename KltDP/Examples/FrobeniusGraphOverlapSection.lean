import KltDP.Geometry.TransitionUnitSections
import KltDP.Geometry.RationalFunctionSheaf
import KltDP.Geometry.CartierEquationUnits
import KltDP.Examples.FrobeniusProjectivePoints
import KltDP.Examples.FrobeniusProjectiveMorphism
import KltDP.Examples.FrobeniusGraphPicardClassIntegral
import KltDP.Examples.FrobeniusGraphPicardClassFrames
import KltDP.Examples.FrobeniusGraphPicardClassRational
import KltDP.Examples.FrobeniusGraphPicardClassRulingCoordinates
import KltDP.Examples.FrobeniusGraphPicardClassRulingDivisors
import KltDP.Examples.FrobeniusGraphPicardClassCoordinateComparison
import KltDP.Examples.FrobeniusStrictTransformFiberRowsExponents
import KltDP.Examples.FrobeniusGraphOverlapUnit

/-!
# Step (b) at section level: the atlas unit is `−y⁻¹` as an actual section

`FrobeniusGraphOverlapUnit` computes the graph atlas transition unit at the **generic point**:
`germ(g₀₁) = −(rationalX)⁻¹^q · (rationalY)⁻¹`, so at `q = 0` it is `−(rationalY)⁻¹`. A germ identity
is not enough for the remaining step, because `pullbackUnits` — the object the accepted Laurent
machinery consumes — applies `(projectiveGraphMorphism p).app` to the **section**. This module
descends the germ identity to an equality of actual sections on the overlap of the two diagonal
charts, which is what a pullback can be applied to.

Everything is accepted input plus the queued step (b):

* `diagonalOverlap_le_rulingOverlap` : `diagonalOpen 0 ⊓ diagonalOpen 1 ≤ rulingOverlap 1`, from the
  accepted `diagonalOpen_le_rulingChart` and `rulingOpen d i = rulingProjection d ⁻¹ᵁ chartOpen k i`;
* `graphOverlapCoordinateUnit`, the accepted `rulingOverlapCoordinateUnit 1` (the `y` coordinate as a
  genuine section unit) restricted to that overlap, with `graphOverlapCoordinateUnit_germ` computing
  its germ as `rulingCoordinateUnit 1` — the pattern of the accepted `reciprocal_cartier_class_zero`;
* **`graphAtlasUnits_val_eq`** : on the overlap, the atlas transition unit of `graphIdealLine 0` is
  literally `−y⁻¹` as a section, by injectivity of the generic-point germ on an integral scheme.

The inverse is taken in the **unit group** `Γ(X, W)ˣ` and then coerced: `Γ(X, W)` is a commutative
ring with no `Inv` instance, so `(u⁻¹ : Γ(X, W))` does not elaborate at all.

**Why this is the useful form.** `projectiveGraphMorphism p ≫ secondProjection =
projectivePowerMorphism p` (accepted `projectiveGraphMorphism_snd`), and the unit here is a pullback
along `rulingProjection 1 = secondProjection`. So pulling it back along the graph section reduces to
the accepted power morphism acting on the line coordinate — the route to `−t^{−p}`.

**Deliberately not proved here.** No pullback is taken and no Laurent form is claimed: step (c)
still needs `(projectiveGraphMorphism p).app` on this unit, which the accepted tree nowhere computes.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Examples.FrobeniusGraphOverlapSection

open KltDP.Geometry KltDP.Geometry.TransitionUnitGluing
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGraphPicardClassIntegral FrobeniusGraphPicardClassFrames
open FrobeniusGraphPicardClassRational FrobeniusGraphPicardClassRulingCoordinates
open FrobeniusGraphPicardClassRulingDivisors FrobeniusGraphPicardClassCoordinateComparison
open FrobeniusStrictTransformFiberRowsExponents FrobeniusGraphOverlapUnit

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

local instance overlapSectionProductIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

local instance diagonalOverlapSection_nonempty :
    Nonempty ((diagonalOpen (k := k) 0 ⊓ diagonalOpen (k := k) 1 : (projectiveProduct k).Opens)) :=
  ⟨⟨genericPoint (projectiveProduct k),
    genericPoint_mem_nonempty_open (projectiveProduct k) (diagonalOpen 0),
    genericPoint_mem_nonempty_open (projectiveProduct k) (diagonalOpen 1)⟩⟩

/-- The overlap of the two diagonal charts lies in the overlap of the second ruling. -/
theorem diagonalOverlap_le_rulingOverlap :
    (diagonalOpen (k := k) 0 ⊓ diagonalOpen (k := k) 1) ≤ rulingOverlap (k := k) 1 :=
  le_inf (inf_le_left.trans (diagonalOpen_le_rulingChart 1 0))
    (inf_le_right.trans (diagonalOpen_le_rulingChart 1 1))

/-- The `y` coordinate as an actual section unit on the diagonal overlap. -/
def graphOverlapCoordinateUnit :
    Γ(projectiveProduct k, diagonalOpen (k := k) 0 ⊓ diagonalOpen (k := k) 1)ˣ :=
  Units.map ((projectiveProduct k).presheaf.map
      (homOfLE (diagonalOverlap_le_rulingOverlap (k := k))).op).hom.toMonoidHom
    (rulingOverlapCoordinateUnit 1)

/-- Its generic-point germ is the accepted second ruling coordinate. -/
theorem graphOverlapCoordinateUnit_germ :
    Units.map ((projectiveProduct k).germToFunctionField
          (diagonalOpen (k := k) 0 ⊓ diagonalOpen (k := k) 1)).hom.toMonoidHom
        (graphOverlapCoordinateUnit (k := k)) =
      rulingCoordinateUnit 1 :=
  (germToFunctionField_map_unit_restriction (projectiveProduct k)
    (diagonalOverlap_le_rulingOverlap (k := k)) (rulingOverlapCoordinateUnit 1)).trans
      (rulingOverlapCoordinateUnit_image 1)

/-- The germ of the inverse section unit is `y⁻¹` as a rational function. -/
theorem graphOverlapCoordinateUnit_inv_germ :
    (projectiveProduct k).germToFunctionField
        (diagonalOpen (k := k) 0 ⊓ diagonalOpen (k := k) 1)
        ((graphOverlapCoordinateUnit (k := k))⁻¹).val =
      (rationalY (k := k))⁻¹ := by
  have hy : Units.map ((projectiveProduct k).germToFunctionField
        (diagonalOpen (k := k) 0 ⊓ diagonalOpen (k := k) 1)).hom.toMonoidHom
        ((graphOverlapCoordinateUnit (k := k))⁻¹) =
      (rulingCoordinateUnit (k := k) 1)⁻¹ := by
    rw [map_inv, graphOverlapCoordinateUnit_germ]
  refine (congrArg Units.val hy).trans ?_
  rw [rationalY_eq_rulingLeft, ← rulingRight_eq_inverse]
  all_goals rfl

/-- **Step (b) at section level: on the overlap the atlas transition unit is `−y⁻¹`.** -/
theorem graphAtlasUnits_val_eq
    (hW0 : (diagonalOpen (k := k) 0 ⊓ diagonalOpen (k := k) 1) ≤ graphAtlasCover 0 ⟨some 0⟩)
    (hW1 : (diagonalOpen (k := k) 0 ⊓ diagonalOpen (k := k) 1) ≤ graphAtlasCover 0 ⟨some 1⟩) :
    res (projectiveProduct k) (le_inf hW0 hW1)
        (graphAtlasUnits (k := k) 0 ⟨some 0⟩ ⟨some 1⟩) =
      -((graphOverlapCoordinateUnit (k := k))⁻¹).val := by
  apply (projectiveProduct k).germToFunctionField_injective
    (diagonalOpen (k := k) 0 ⊓ diagonalOpen (k := k) 1)
  rw [graphAtlasUnits_germ_eq 0 hW0 hW1, map_neg, graphOverlapCoordinateUnit_inv_germ,
    pow_zero, one_mul]
  all_goals rfl

end KltDP.Examples.FrobeniusGraphOverlapSection

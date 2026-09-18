import KltDP.Geometry.TargetIsomorphismOpen
import KltDP.Geometry.ProperBirationalCodimensionOne
import KltDP.Geometry.PointClosureCurve
import KltDP.Geometry.FiniteClosedPointComplement

/-!
The original target non-isomorphism locus of a proper birational map
from any integral scheme to a normal projective surface is a finite set
of closed points. Prime-curve generic stalks are valuation rings, and
the original surface generic stalk is its function field. The existing
point-closure dichotomy and Noetherian closed-point finiteness finish.

The source is not required to be normal or projective. Regularity and
local dimension two at these closed target points are separate inputs
for the later point-blowup domination application.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ProperBirationalSurface

/-- The target generic point is in the original isomorphism open. -/
theorem genericPoint_mem_targetIsomorphismOpen
    {k : Type u} [Field k] {G : Scheme.{u}} [IsIntegral G]
    (T : NormalProjectiveSurface k) (f : G ⟶ T.toScheme) [IsProper f]
    (hbir : IsBirationalScheme f) :
    genericPoint T.toScheme ∈ targetIsomorphismOpen f := by
  letI : ValuationRing (T.toScheme.presheaf.stalk (genericPoint T.toScheme)) := by
    change ValuationRing T.toScheme.functionField
    infer_instance
  exact ProperBirationalCodimensionOne.exists_isomorphism_open_at_valuation_stalk
    f hbir (genericPoint T.toScheme)

/-- Every point outside the original isomorphism open is closed in the
actual target surface. -/
theorem isClosed_singleton_of_mem_targetNonisomorphismLocus
    {k : Type u} [Field k] {G : Scheme.{u}} [IsIntegral G]
    (T : NormalProjectiveSurface k) (f : G ⟶ T.toScheme) [IsProper f]
    (hbir : IsBirationalScheme f) (x : T.toScheme)
    (hx : x ∈ targetNonisomorphismLocus f) :
    IsClosed ({x} : Set T.toScheme) := by
  by_contra hclosed
  have hgeneric : x ≠ genericPoint T.toScheme := by
    intro heq
    apply hx
    rw [heq]
    exact genericPoint_mem_targetIsomorphismOpen T f hbir
  let C := T.primeCurveOfNonclosedPoint x hgeneric hclosed
  obtain ⟨U, hxU, hU⟩ :=
    ProperBirationalCodimensionOne.exists_isomorphism_open_at_primeCurve T f hbir C
  have hxU' : x ∈ U := by
    simpa only [C, NormalProjectiveSurface.primeCurveOfNonclosedPoint_genericPoint] using hxU
  exact hx ⟨U, hxU', hU⟩

/-- The original bad target locus is finite, with no hypothesis on the
source beyond integrality and the original proper birational map. -/
theorem targetNonisomorphismLocus_finite
    {k : Type u} [Field k] {G : Scheme.{u}} [IsIntegral G]
    (T : NormalProjectiveSurface k) (f : G ⟶ T.toScheme) [IsProper f]
    (hbir : IsBirationalScheme f) :
    (targetNonisomorphismLocus f).Finite :=
  finite_of_isClosed_of_closedPoints (isClosed_targetNonisomorphismLocus f)
    (isClosed_singleton_of_mem_targetNonisomorphismLocus T f hbir)

/-- This finite set has the exact original complement restriction needed
by the point-blowup domination interface. -/
theorem isIso_finiteClosedPointComplement_targetNonisomorphismLocus
    {k : Type u} [Field k] {G : Scheme.{u}} [IsIntegral G]
    (T : NormalProjectiveSurface k) (f : G ⟶ T.toScheme) [IsProper f]
    (hbir : IsBirationalScheme f) :
    IsIso (f ∣_ finiteClosedPointComplement T.toScheme (targetNonisomorphismLocus f)
      (targetNonisomorphismLocus_finite T f hbir)
      (isClosed_singleton_of_mem_targetNonisomorphismLocus T f hbir)) := by
  have hU : finiteClosedPointComplement T.toScheme (targetNonisomorphismLocus f)
      (targetNonisomorphismLocus_finite T f hbir)
      (isClosed_singleton_of_mem_targetNonisomorphismLocus T f hbir) =
      targetIsomorphismOpen f := by
    ext x
    change (¬¬ x ∈ targetIsomorphismOpen f) ↔ x ∈ targetIsomorphismOpen f
    exact not_not
  rw [hU]
  exact isIso_targetIsomorphismOpen f

end KltDP.Geometry.ProperBirationalSurface

import KltDP.Geometry.EffectiveWeilPrimeSupport
import KltDP.Geometry.NefPositiveSquareKodaira
import KltDP.Geometry.ProjectiveAmpleCartierWitness

/-!
# Finiteness of the actual degree-zero curves of a nef divisor

On the original smooth projective surface, a nef Cartier divisor of
positive square has an effective representative of nD-H for an actual
ample H. All its degree-zero primes lie in that finite divisor support.
Their union is therefore already closed, without taking its closure.
No finiteness, section, or effective-representative hypothesis is assumed.
-/

noncomputable section

open AlgebraicGeometry
open KltDP.Geometry.NormalProjectiveSurface

universe u

namespace KltDP.Geometry.NefNullCurveFiniteness

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  [IsSmoothOfRelativeDimension 2 X.structureMorphism]

local instance source_isSmooth : IsSmooth X.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 X.structureMorphism

/-- A nef Cartier divisor of positive square has only finitely many
degree-zero prime curves on the original smooth projective surface. -/
theorem finite_null_curves (D : CartierDivisor X.toScheme)
    (hD : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme D))
    (hDD : 0 < intersectionPairing X X.regularPoints_of_isSmooth D D) :
    {C : X.PrimeCurve | C.intersectionNumber D = 0}.Finite := by
  obtain ⟨H, hH⟩ := X.exists_isAmple_cartier
  obtain ⟨n, _, E, hE, hED⟩ :=
    NefPositiveSquareKodaira.exists_effective_sub_ample X D H hD hDD hH
  apply E.support.finite_toSet.subset
  intro C hC
  exact EffectiveWeilPrimeSupport.mem_support_of_degree_zero X
    X.regularPoints_of_isSmooth D H hH n E hE hED C hC

/-- The union of those actual prime curves is a closed subset of the
original surface. This is a geometric union, not a finite set of points. -/
theorem isClosed_union_null_curves (D : CartierDivisor X.toScheme)
    (hD : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme D))
    (hDD : 0 < intersectionPairing X X.regularPoints_of_isSmooth D D) :
    IsClosed (⋃ C ∈ {C : X.PrimeCurve | C.intersectionNumber D = 0},
      (C : Set X.toScheme)) :=
  (finite_null_curves X D hD hDD).isClosed_biUnion (fun C _ => C.isClosed)

/-- Taking the closure adds no points to the union of the degree-zero
curves of the original nef divisor of positive square. -/
theorem closure_union_null_curves (D : CartierDivisor X.toScheme)
    (hD : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme D))
    (hDD : 0 < intersectionPairing X X.regularPoints_of_isSmooth D D) :
    closure (⋃ C ∈ {C : X.PrimeCurve | C.intersectionNumber D = 0},
      (C : Set X.toScheme)) =
      ⋃ C ∈ {C : X.PrimeCurve | C.intersectionNumber D = 0}, (C : Set X.toScheme) :=
  (isClosed_union_null_curves X D hD hDD).closure_eq

end KltDP.Geometry.NefNullCurveFiniteness

import KltDP.Geometry.CurvePositiveDegreeBig
import KltDP.Geometry.Positivity

/-!
# Bigness and exceptionalness on the original prime curves

The proper integral curve bigness theorem applies to the original reduced
prime-curve scheme and the original restriction of the surface line bundle.
For a nef line bundle, its exceptional prime curves are exactly its curves
of degree zero in the existing Euler-degree and exceptional-locus definitions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.PrimeCurveBigness

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

/-- On each original prime curve, the restriction of a nef surface
line bundle is big exactly when its original restriction degree is positive. -/
theorem isBig_restriction_iff_degree_pos (L : InvertibleSheaf X.toScheme)
    (hnef : Positivity.IsNef X.structureMorphism L) (C : X.PrimeCurve) :
    Positivity.IsBig C.toSpec (pullbackInvertibleSheaf C.inclusion L) ↔
      0 < C.restrictionDegree L := by
  letI : IsProper C.toSpec := C.toSpec_isProper
  exact CurvePositiveDegreeBig.isBig_iff_degree_pos_of_nonneg C.toSpec
    C.dimension_one_toScheme (pullbackInvertibleSheaf C.inclusion L)
    ((Positivity.isNef_iff_forall_primeCurve X L).mp hnef C)

/-- Each actual exceptional prime curve of a nef surface line bundle
is exactly an actual prime of restriction degree zero. -/
theorem isExceptional_iff_degree_zero (L : InvertibleSheaf X.toScheme)
    (hnef : Positivity.IsNef X.structureMorphism L) (C : X.PrimeCurve) :
    Positivity.IsExceptionalSubvariety X.structureMorphism L C.1 ↔
      C.restrictionDegree L = 0 := by
  change (0 < topologicalKrullDim (C : Set X.toScheme) ∧
    ¬ Positivity.IsBig C.toSpec (pullbackInvertibleSheaf C.inclusion L)) ↔ _
  rw [C.dimension_one, and_iff_right (by norm_num),
    isBig_restriction_iff_degree_pos X L hnef C]
  have hnonneg := (Positivity.isNef_iff_forall_primeCurve X L).mp hnef C
  omega

/-- The same bigness comparison in the original irreducible-closed-subvariety
interface used by the existing surface null-locus theorem. -/
theorem isBig_subvariety_iff_degree_pos (L : InvertibleSheaf X.toScheme)
    (hnef : Positivity.IsNef X.structureMorphism L)
    (Z : IrreducibleCloseds X.toScheme)
    (hZ : topologicalKrullDim (Z : Set X.toScheme) = 1) :
    Positivity.IsBig (Positivity.inclusion Z ≫ X.structureMorphism)
        (pullbackInvertibleSheaf (Positivity.inclusion Z) L) ↔
      0 < Positivity.subvarietyDegree X.structureMorphism L Z :=
  isBig_restriction_iff_degree_pos X L hnef (⟨Z, hZ⟩ : X.PrimeCurve)

end KltDP.Geometry.PrimeCurveBigness

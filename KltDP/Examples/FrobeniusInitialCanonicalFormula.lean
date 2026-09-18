import KltDP.Geometry.ProjectiveProductCanonicalFormula
import KltDP.Examples.FrobeniusInitialCanonicalFiberClasses
import KltDP.Examples.FrobeniusContactTowerCanonicalIteration

/-!
# The original initial canonical class has coefficients minus two

The original smooth product canonical sheaf has been identified with the
two original pulled canonical factors. Their already proved Cartier
pullback computations identify their classes with minus twice the existing
first and second fiber classes. The final statement retains the original
initial canonical class used by the compiled contact-tower iteration.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusInitialCanonicalFormula

open KltDP.Geometry KltDP.Geometry.ProjectiveProductCanonicalFormula
open KltDP.Geometry.SmoothSurfaceKaehlerAtlas
open FrobeniusProjectivePoints FrobeniusGraphPicardClassFiberClasses
open FrobeniusContactTowerCanonicalIteration FrobeniusInitialCanonicalFiberClasses

variable {k : Type u} [Field k]

/-- The canonical class of the original product is minus twice its two original fiber classes. -/
theorem canonicalPicard_eq_fiberClasses :
    Additive.ofMul
        (canonicalSheafOfSmoothSurface (projectiveProductToSpec (k := k))).toPic =
      (-2 : ℤ) • firstFiberClass + (-2 : ℤ) • secondFiberClass := by
  rw [canonical_toPic]
  exact canonicalFactorPicard_eq_fiberClasses

/-- This is the actual initial class in the original all-depth canonical iteration. -/
theorem originalCanonicalClass_zero :
    originalCanonicalClass (k := k) 0 =
      (-2 : ℤ) • firstFiberClass + (-2 : ℤ) • secondFiberClass :=
  canonicalPicard_eq_fiberClasses

end KltDP.Examples.FrobeniusInitialCanonicalFormula

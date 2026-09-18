import KltDP.Examples.FrobeniusMultiCentreCanonicalPicard
import KltDP.Examples.FrobeniusInitialCanonicalFormula

/-!
# The explicit canonical class of the original finite-centre surface

Substitute the actual initial-product canonical formula into the original
global finite-centre formula. The ruling pullbacks, surface and full double
exceptional sum are the original objects in those two constructions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCanonicalExplicit

open KltDP.Geometry
open FrobeniusMultiCentreSurface FrobeniusMultiCentreCanonicalOpenComparison
open FrobeniusMultiCentreCanonicalPicard FrobeniusInitialCanonicalFormula
open FrobeniusGraphPicardClassFiberClasses

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The original canonical class has coefficients minus two on the two pulled
rulings and coefficient one on every original total exceptional class. -/
theorem multiCanonicalClass_eq_fibers_exceptionals
    (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a) :
    multiCanonicalClass (q + 1) n a ha =
      (-2 : ℤ) • (schemePicardPullbackHom (multiProjection (q + 1) n a)).toAdditive
          firstFiberClass +
        (-2 : ℤ) • (schemePicardPullbackHom (multiProjection (q + 1) n a)).toAdditive
          secondFiberClass +
        ∑ i : Fin n, ∑ j : Fin (q + 1), exceptionalClass (q + 1) n a i j := by
  rw [multiCanonicalClass_formula, originalCanonicalClass_zero,
    map_add, map_zsmul, map_zsmul]

end KltDP.Examples.FrobeniusMultiCentreCanonicalExplicit

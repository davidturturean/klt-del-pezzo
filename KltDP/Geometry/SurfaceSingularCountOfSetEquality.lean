import KltDP.Geometry.SurfaceFiniteness
import Mathlib.Data.Set.Card

/-!
# Exact counts from the actual singular set

These are set and cardinality adapters. They require an established equality
with the actual singular-point set; they prove no reverse singularity
inclusion and impose no geometric substitute for that missing proof.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- A set proved equal to the actual singular-point set is finite. -/
theorem finite_of_singularPoints_set_eq (Z : Set X.Point)
    (hZ : (X.singularPoints : Set X.Point) = Z) : Z.Finite :=
  hZ ▸ X.singularPoints.finite_toSet

/-- Transport the exact actual singular-point count across a proved set equality. -/
theorem singularPoints_card_eq_natCard_of_set_eq (Z : Set X.Point)
    (hZ : (X.singularPoints : Set X.Point) = Z) :
    X.singularPoints.card = Nat.card Z := by
  rw [Set.Nat.card_coe_set_eq, ← Set.ncard_coe_Finset X.singularPoints, hZ]

/-- The manuscript's singular-point-count definition has the same exact value. -/
theorem singularPointCount_eq_of_set_eq (Z : Set X.Point)
    (hZ : (X.singularPoints : Set X.Point) = Z) (r : ℕ) (hcard : Nat.card Z = r) :
    X.singularPointCount = r :=
  (X.singularPoints_card_eq_natCard_of_set_eq Z hZ).trans hcard

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.singularPoints_card_eq_natCard_of_set_eq
#print axioms KltDP.Geometry.NormalProjectiveSurface.singularPointCount_eq_of_set_eq

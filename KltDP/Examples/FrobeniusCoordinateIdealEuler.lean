import KltDP.Geometry.RationalPointIdealExact
import KltDP.Geometry.PicardEulerValue
import KltDP.Examples.FrobeniusProjectiveCoordinatePicard

/-!
# The original coordinate ideal and the Euler difference

The point is the original rational coordinate point `[1:0]`. Its section
identity proves that its original ideal sequence is short exact. Applying
the existing Euler additivity theorem identifies the Euler difference of
that very invertible ideal with minus the Euler characteristic of the
original pushed-forward point structure sheaf.

The finite-dimensionality and common vanishing bound of these actual
cohomology groups remain explicit. The expression on the left is the
expression used for line-bundle degree in Stacks Definition 33.44.1 (0AYR),
whose geometric scope is proper schemes of dimension at most one. This file
does not define a new degree, assert the point's Euler characteristic is one,
or identify a surface intersection number.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusCoordinateIdealEuler

open KltDP.Geometry KltDP.Geometry.ModuleCohomology
open FrobeniusProjectiveCoordinateIdeal FrobeniusProjectiveCoordinatePicard

variable {k : Type u} [Field k]

/-- This is the short complex of the original coordinate point and its original kernel. -/
abbrev coordinateIdealSequence : ShortComplex (projectiveSpace k 1).Modules :=
  RationalPointIdeal.idealSequence (coordinatePoint (k := k))

/-- The actual rational section identity proves short exactness; it is not an input. -/
theorem coordinateIdealSequence_shortExact :
    (coordinateIdealSequence (k := k)).ShortExact :=
  RationalPointIdeal.idealSequence_shortExact coordinatePoint (projectiveSpaceToSpec k 1)
    (FrobeniusProjectivePoints.pointMorphism_over_base (0 : k))

/-- The Euler difference for the original invertible point ideal follows from
its actual short exact sequence, once the actual cohomology is finite and bounded. -/
theorem coordinateIdeal_euler_difference (N : ℕ)
    (hfinite₁ : ∀ n, FiniteDimensional k
      ((baseFunctor (projectiveSpaceToSpec k 1) n).obj (coordinateIdealSequence (k := k)).X₁))
    (hfinite₂ : ∀ n, FiniteDimensional k
      ((baseFunctor (projectiveSpaceToSpec k 1) n).obj (coordinateIdealSequence (k := k)).X₂))
    (hfinite₃ : ∀ n, FiniteDimensional k
      ((baseFunctor (projectiveSpaceToSpec k 1) n).obj (coordinateIdealSequence (k := k)).X₃))
    (hvanish₁ : ∀ n, N < n → Subsingleton (H (coordinateIdealSequence (k := k)).X₁ n))
    (hvanish₂ : ∀ n, N < n → Subsingleton (H (coordinateIdealSequence (k := k)).X₂ n))
    (hvanish₃ : ∀ n, N < n → Subsingleton (H (coordinateIdealSequence (k := k)).X₃ n)) :
    picardEulerValue (projectiveSpaceToSpec k 1) (coordinateIdealLine (k := k)).toPic -
        picardEulerValue (projectiveSpaceToSpec k 1) (1 : (projectiveSpace k 1).Pic) =
      -eulerCharacteristic (projectiveSpaceToSpec k 1)
        ((schemeModulePushforward (coordinatePoint (k := k))).obj
          (_root_.SheafOfModules.unit (Spec (CommRingCat.of k)).ringCatSheaf)) := by
  rw [picardEulerValue_toPic, picardEulerValue_one]
  have h := eulerCharacteristic_additive (projectiveSpaceToSpec k 1)
    coordinateIdealSequence coordinateIdealSequence_shortExact N
    hfinite₁ hfinite₂ hfinite₃ hvanish₁ hvanish₂ hvanish₃
  change eulerCharacteristic (projectiveSpaceToSpec k 1)
      (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) =
    eulerCharacteristic (projectiveSpaceToSpec k 1) (coordinateIdealLine (k := k)).obj +
      eulerCharacteristic (projectiveSpaceToSpec k 1)
        ((schemeModulePushforward (coordinatePoint (k := k))).obj
          (_root_.SheafOfModules.unit (Spec (CommRingCat.of k)).ringCatSheaf)) at h
  omega

end KltDP.Examples.FrobeniusCoordinateIdealEuler

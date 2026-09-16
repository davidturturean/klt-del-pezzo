import KltDP.Examples.FrobeniusMultiCentrePicardRealization
import KltDP.Examples.FrobeniusSevenNodes

/-!
# Integral coordinates and divisibility for actual global Picard classes

The original intersection rows extract integral coordinates from every Picard
class. On the realized manuscript lattice this is a left inverse. Thus an
integer multiple equation for a realized vector in the actual Picard group
is equivalent to the corresponding equation in the integral lattice; this
does not require surjectivity of the realization map. In particular, parity
classifications can be transported without assuming a Picard basis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentrePicardCoordinates

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreGraphExceptionalPairing
  FrobeniusMultiCentreGraphFiberNumericalValues
  FrobeniusMultiCentrePicardRealization

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
  [Fact (q + 1).Prime] [CharP k (q + 1)]
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- Actual integral intersection numbers extract the manuscript's coordinates. -/
def coordinates : Additive (multiSurface (q + 1) n a).Pic →+
    FrobeniusPicard.PicardVector (q + 1) n where
  toFun c :=
    (multiPairingHom q n a ha hproj (multiSecondFiberClass (q + 1) n a) c,
      multiPairingHom q n a ha hproj (multiFirstFiberClass (q + 1) n a) c,
      fun ij => -(multiPairingHom q n a ha hproj
        (exceptionalClass (q + 1) n a ij.1 ij.2) c))
  map_zero' := by
    apply Prod.ext
    · exact map_zero _
    · apply Prod.ext
      · exact map_zero _
      · funext ij
        simp only [map_zero, neg_zero, Pi.zero_apply]
        rfl
  map_add' x y := by
    apply Prod.ext
    · exact map_add _ _ _
    · apply Prod.ext
      · exact map_add _ _ _
      · funext ij
        simp only [map_add, neg_add, Pi.add_apply]
        rfl

/-- The computed geometric matrix makes coordinate extraction a left inverse. -/
theorem coordinates_realization (x : FrobeniusPicard.PicardVector (q + 1) n) :
    coordinates q n a ha hproj (realization q n a x) = x := by
  apply Prod.ext
  · exact realization_pairing_second q n a ha hproj x
  · apply Prod.ext
    · exact realization_pairing_first q n a ha hproj x
    · funext ij
      change -(multiPairing (q + 1) n a ha hproj (realization q n a x)
        (exceptionalClass (q + 1) n a ij.1 ij.2)) = x.2.2 ij
      rw [realization_pairing_exceptional, neg_neg]

include ha hproj in
/-- An integer multiple equation in the actual Picard group is detected on the integral lattice. -/
theorem realization_divisible_iff (m : ℤ) (x : FrobeniusPicard.PicardVector (q + 1) n) :
    (∃ c : Additive (multiSurface (q + 1) n a).Pic, m • c = realization q n a x) ↔
      ∃ y : FrobeniusPicard.PicardVector (q + 1) n, m • y = x := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨coordinates q n a ha hproj c, ?_⟩
    have h := congrArg (coordinates q n a ha hproj) hc
    rwa [map_zsmul, coordinates_realization] at h
  · rintro ⟨y, hy⟩
    refine ⟨realization q n a y, ?_⟩
    rw [← map_zsmul, hy]

include ha hproj in
/-- Divisibility by two in the actual Picard group is precisely parity of every coordinate. -/
theorem realization_two_divisible_iff (x : FrobeniusPicard.PicardVector (q + 1) n) :
    (∃ c : Additive (multiSurface (q + 1) n a).Pic, (2 : ℤ) • c = realization q n a x) ↔
      Even x.1 ∧ Even x.2.1 ∧ ∀ ij, Even (x.2.2 ij) := by
  rw [realization_divisible_iff q n a ha hproj]
  exact FrobeniusSevenNodes.two_divisible_iff_even_coordinates x

end KltDP.Examples.FrobeniusMultiCentrePicardCoordinates

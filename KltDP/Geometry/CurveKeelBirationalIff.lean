import KltDP.Geometry.CurveKeelBirationalPositive
import KltDP.Geometry.KeelCompleteSystemBigness
import KltDP.Geometry.CurvePositiveDegreeBig

/-!
# Eventual complete-system birationality, positive degree, and bigness on original curves

For the original integral projective curve and a line bundle of nonnegative
original Euler degree, the shared eventual-birationality predicate is
equivalent both to positive degree and to unchanged section-growth bigness.
Algebraic closedness is retained for the existing degree-zero non-bigness
theorem; the separate positive-degree forward theorem works over any field.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.CurveKeelBirational

private theorem natDim_pos_of_dimension_one {X : Scheme.{u}}
    (hdim : topologicalKrullDim X = 1) : 0 < Positivity.natDim X := by
  have hnat : Positivity.natDim X = 1 := by
    unfold Positivity.natDim
    rw [hdim]
    rfl
  rw [hnat]
  exact Nat.zero_lt_one

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k)) (hf : IsProjectiveOverField f)
  (hdim : topologicalKrullDim X = 1) (L : InvertibleSheaf X)
  (hdeg : 0 ≤ eulerCharacteristic f L.obj -
    eulerCharacteristic f (_root_.SheafOfModules.unit X.ringCatSheaf))

include hdim hdeg

/-- The actual eventual complete system is birational exactly at positive original degree. -/
theorem eventuallyBirational_iff_degree_pos_of_nonneg :
    letI : IsProper f := hf.isProper
    KeelCompleteSystem.EventuallyBirational f L ↔
      0 < eulerCharacteristic f L.obj -
        eulerCharacteristic f (_root_.SheafOfModules.unit X.ringCatSheaf) := by
  letI : IsProper f := hf.isProper
  constructor
  · intro h
    exact (CurvePositiveDegreeBig.isBig_iff_degree_pos_of_nonneg f hdim L hdeg).mp
      (KeelCompleteSystem.isBig_of_eventuallyBirational f L
        (natDim_pos_of_dimension_one hdim) h)
  · exact eventuallyBirational_of_degree_pos f hf hdim L

/-- On the same original curve and nonnegative-degree line, the shared source predicate
is equivalent to the unchanged original growth-bigness predicate. -/
theorem eventuallyBirational_iff_isBig_of_nonneg :
    letI : IsProper f := hf.isProper
    KeelCompleteSystem.EventuallyBirational f L ↔ Positivity.IsBig f L := by
  letI : IsProper f := hf.isProper
  exact (eventuallyBirational_iff_degree_pos_of_nonneg f hf hdim L hdeg).trans
    (CurvePositiveDegreeBig.isBig_iff_degree_pos_of_nonneg f hdim L hdeg).symm

/-- Failure of the actual eventual-birationality predicate is exactly original degree zero. -/
theorem not_eventuallyBirational_iff_degree_zero_of_nonneg :
    letI : IsProper f := hf.isProper
    ¬ KeelCompleteSystem.EventuallyBirational f L ↔
      eulerCharacteristic f L.obj -
        eulerCharacteristic f (_root_.SheafOfModules.unit X.ringCatSheaf) = 0 := by
  letI : IsProper f := hf.isProper
  rw [eventuallyBirational_iff_degree_pos_of_nonneg f hf hdim L hdeg]
  omega

end KltDP.Geometry.CurveKeelBirational

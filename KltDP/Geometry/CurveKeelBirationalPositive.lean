import KltDP.Geometry.KeelCompleteSystemBirational
import KltDP.Geometry.CurveCompleteSystemBirational

/-!
# Positive original curve degree gives eventual birationality of the complete system

The shared predicate uses the actual complete-system map on its original
non-base open and the actual factor to its original schematic image.
The existing positive-degree theorem supplies all sufficiently large
systems. The shared packaging supplies the required positive threshold.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.CurveKeelBirational

/-- Positive original Euler degree gives the shared eventual-birationality predicate
on the original integral projective curve, over an arbitrary field. -/
theorem eventuallyBirational_of_degree_pos
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) (hf : IsProjectiveOverField f)
    (hdim : topologicalKrullDim X = 1) (L : InvertibleSheaf X)
    (hdeg : 0 < eulerCharacteristic f L.obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit X.ringCatSheaf)) :
    letI : IsProper f := hf.isProper
    KeelCompleteSystem.EventuallyBirational f L := by
  letI : IsProper f := hf.isProper
  exact KeelCompleteSystem.eventuallyBirational_of_eventually_toImage f L
    (CurveCompleteSystemBirational.eventually_toImage_isBirationalScheme_of_degree_pos
      f hf hdim L hdeg)

end KltDP.Geometry.CurveKeelBirational

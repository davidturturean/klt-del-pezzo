import KltDP.Literature.ProperCurvePullbackDegreeLiteral
import KltDP.Geometry.ProperBirationalCurvePullbackDegreeConditional

/-! Original birational curve degree transport using the full reviewed source. -/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open KltDP.Geometry.ModuleCohomology
universe u
namespace KltDP.Geometry.ProperBirationalCurveDegree

theorem eulerDifference_pullback
    {k : Type u} [Field k] {C D : Scheme.{u}} [IsIntegral C] [IsIntegral D]
    (σC : C ⟶ Spec (CommRingCat.of k)) [IsProper σC]
    (σD : D ⟶ Spec (CommRingCat.of k)) [IsProper σD]
    (hdimC : topologicalKrullDim C = 1) (hdimD : topologicalKrullDim D = 1)
    (f : C ⟶ D) (hf : f ≫ σD = σC) (hbir : IsBirationalScheme f)
    (E : D.Modules) (n : ℕ) (hE : IsLocallyFreeOfRankOn D E n) :
    eulerCharacteristic σC ((schemeModulePullback f).obj E) -
        (n : ℤ) * eulerCharacteristic σC (_root_.SheafOfModules.unit C.ringCatSheaf) =
      eulerCharacteristic σD E -
        (n : ℤ) * eulerCharacteristic σD (_root_.SheafOfModules.unit D.ringCatSheaf) :=
  eulerDifference_pullback_of_birational
    Literature.Stacks.proper_curve_pullback_degree_literal
    σC σD hdimC hdimD f hf hbir E n hE

end KltDP.Geometry.ProperBirationalCurveDegree
#check @KltDP.Geometry.ProperBirationalCurveDegree.eulerDifference_pullback
#print axioms KltDP.Geometry.ProperBirationalCurveDegree.eulerDifference_pullback

import KltDP.Geometry.ProperBirationalCurveDegreeData
import KltDP.Geometry.NonconstantCurveGenericPoint
import KltDP.Geometry.RankIndexedCurveDegree
import KltDP.Geometry.SchemeInvertibleSheafPullback

/-!
The complete Stacks0AYZ degree formula for nonconstant proper curve maps,
with the finite-rank Euler degree of0AYR unfolded on the original sheaves.
The field degree of02NY uses the original generic stalk map.
Root admission and the frozen source/definition dictionary are separate.
-/
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace KltDP.Geometry
open KltDP.Geometry.ModuleCohomology
universe u
namespace KltDP.Literature.Stacks

axiom proper_curve_pullback_degree_literal :
    ∀ {k : Type u} [instField : Field k]
      {C D : Scheme.{u}} [instIntegralC : IsIntegral C] [instIntegralD : IsIntegral D]
      (σC : C ⟶ Spec (CommRingCat.of k)) [instProperC : IsProper σC]
      (σD : D ⟶ Spec (CommRingCat.of k)) [instProperD : IsProper σD]
      (hdimC : topologicalKrullDim C = 1) (hdimD : topologicalKrullDim D = 1)
      (f : C ⟶ D) (hf : f ≫ σD = σC)
      (hnonconstant : ¬ ∃ y : D, ∀ x : C, f.base x = y)
      (E : D.Modules) (n : ℕ) (hE : IsLocallyFreeOfRankOn D E n),
      letI : IsNoetherian D := isNoetherian_of_finiteType_toSpec σD
      letI : GenericPointPreserving f :=
        ProperNonconstantCurve.genericPointPreserving_of_nonconstant_base
          f hdimD.le hnonconstant
      letI : Algebra D.functionField C.functionField :=
        (functionFieldMap f).hom.toAlgebra
      eulerCharacteristic σC ((schemeModulePullback f).obj E) -
          (n : ℤ) * eulerCharacteristic σC (_root_.SheafOfModules.unit C.ringCatSheaf) =
        (Module.finrank D.functionField C.functionField : ℤ) *
          (eulerCharacteristic σD E -
            (n : ℤ) * eulerCharacteristic σD (_root_.SheafOfModules.unit D.ringCatSheaf))

end KltDP.Literature.Stacks
#check @KltDP.Literature.Stacks.proper_curve_pullback_degree_literal
#print axioms KltDP.Literature.Stacks.proper_curve_pullback_degree_literal

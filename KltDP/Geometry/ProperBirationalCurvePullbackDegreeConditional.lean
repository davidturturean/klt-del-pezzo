import KltDP.Geometry.ProperBirationalCurveDegreeData
import KltDP.Geometry.NonconstantCurveGenericPoint
import KltDP.Geometry.RankIndexedCurveDegree
import KltDP.Geometry.SchemeInvertibleSheafPullback

/-!
# Conditional original birational curve degree transport

The entire finite-rank statement of Stacks 0AYZ is an explicit hypothesis
below. No new literature declaration is activated. The original proper
curve maps, sheaf pullback, field-map scalar action, and Euler values are
retained. The conditional consequence derives nonconstancy and degree one
from the original birational map; it assumes no isomorphism of whole curves.

The source contract, full published TeX, license and correspondence are
recorded in this directory's Markdown and source manifest. In particular,
the source is not weakened to its rank-one or birational specialization.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open KltDP.Geometry.ModuleCohomology
universe u

namespace KltDP.Geometry.ProperBirationalCurveDegree

/-- Conditional on the full published pullback-degree formula, the
original birational map preserves every original finite-rank Euler degree. -/
theorem eulerDifference_pullback_of_birational
    (hsource : ∀ {k : Type u} [instField : Field k]
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
            (n : ℤ) * eulerCharacteristic σD (_root_.SheafOfModules.unit D.ringCatSheaf)))
    {k : Type u} [Field k] {C D : Scheme.{u}} [IsIntegral C] [IsIntegral D]
    (σC : C ⟶ Spec (CommRingCat.of k)) [IsProper σC]
    (σD : D ⟶ Spec (CommRingCat.of k)) [IsProper σD]
    (hdimC : topologicalKrullDim C = 1) (hdimD : topologicalKrullDim D = 1)
    (f : C ⟶ D) (hf : f ≫ σD = σC) (hbir : IsBirationalScheme f)
    (E : D.Modules) (n : ℕ) (hE : IsLocallyFreeOfRankOn D E n) :
    eulerCharacteristic σC ((schemeModulePullback f).obj E) -
        (n : ℤ) * eulerCharacteristic σC (_root_.SheafOfModules.unit C.ringCatSheaf) =
      eulerCharacteristic σD E -
        (n : ℤ) * eulerCharacteristic σD (_root_.SheafOfModules.unit D.ringCatSheaf) := by
  letI : IsProper (f ≫ σD) := by rw [hf]; infer_instance
  letI : IsProper f := IsProper.of_comp_of_isSeparated f σD
  have hnonconstant := not_constant_of_birational f hbir hdimD
  letI : IsNoetherian D := isNoetherian_of_finiteType_toSpec σD
  letI : GenericPointPreserving f :=
    ProperNonconstantCurve.genericPointPreserving_of_nonconstant_base
      f hdimD.le hnonconstant
  letI : Algebra D.functionField C.functionField :=
    (functionFieldMap f).hom.toAlgebra
  have h := hsource σC σD hdimC hdimD f hf hnonconstant E n hE
  have hdegree : Module.finrank D.functionField C.functionField = 1 :=
    functionField_finrank_eq_one f hbir
  simpa only [hdegree, Nat.cast_one, one_mul] using h

end KltDP.Geometry.ProperBirationalCurveDegree

#check @KltDP.Geometry.ProperBirationalCurveDegree.eulerDifference_pullback_of_birational
#print axioms KltDP.Geometry.ProperBirationalCurveDegree.eulerDifference_pullback_of_birational

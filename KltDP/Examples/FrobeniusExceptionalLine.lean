import KltDP.Examples.FrobeniusExceptionalProjectiveLine
import KltDP.Examples.FrobeniusExceptionalConormal
import KltDP.Geometry.AffineBlowupExceptionalFiber
import KltDP.Geometry.AffineBlowupExceptionalInvertible
import KltDP.Geometry.SchemeInvertibleSheafPullback
import KltDP.Geometry.ProjectiveLineTransitionExponent

/-!
# The original exceptional conormal line on the original projective line

The line below is the pullback of the actual global exceptional conormal
along the inverse of the constructed exceptional-scheme/P1 isomorphism.
Its chart comparison retains the original exceptional chart inclusions.

The actual quotient-overlap ratio is also transported to the existing P1
overlap section ring, and has exponent one in the existing convention.
Identifying this section with the transition extracted from trivializations
of the transported global line remains the next frame-comparison theorem;
it is not built into the line's definition.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Examples.FrobeniusExceptionalLine

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusExceptionalProjectiveLine
open FrobeniusExceptionalOverlap

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

/-- The actual glued exceptional scheme is the original projective line. -/
def exceptionalProjectiveLineIso : exceptionalScheme (centerIdeal (k := k)) ≅
    projectiveSpace k 1 :=
  exceptionalFiberIso centerIdeal ≪≫ exceptionalFiberProjectiveLineIso

/-- The conormal on P1 is the transported original global conormal line. -/
def conormalLine : InvertibleSheaf (projectiveSpace k 1) :=
  pullbackInvertibleSheaf exceptionalProjectiveLineIso.inv
    (exceptionalConormalLine centerIdeal)

/-- Its underlying module is exactly the actual inverse-image module sheaf. -/
theorem conormalLine_obj :
    (conormalLine (k := k)).obj =
      (schemeModulePullback exceptionalProjectiveLineIso.inv).obj
        (exceptionalConormalSheaf centerIdeal) := rfl

/-- The original exceptional chart, now mapping to the original glued
exceptional scheme through the constructed fiber comparison. -/
def chartToExceptional (a : centerIdeal (k := k)) :
    exceptionalChart centerIdeal a ⟶ exceptionalScheme (centerIdeal (k := k)) :=
  exceptionalChartToFiber centerIdeal a ≫ (exceptionalFiberIso centerIdeal).inv

instance (a : centerIdeal (k := k)) : IsOpenImmersion (chartToExceptional a) := by
  unfold chartToExceptional
  infer_instance

/-- The transported chart retains its original morphism into the blowup. -/
theorem chartToExceptional_ι (a : centerIdeal (k := k)) :
    chartToExceptional a ≫ exceptionalι centerIdeal = exceptionalChartToBlowup centerIdeal a := by
  rw [chartToExceptional, Category.assoc, exceptionalFiberIso_inv_ι,
    exceptionalChartToFiber_ι]

/-- The first chart of the actual glued exceptional scheme is the original
first projective chart under the constructed comparison. -/
theorem chartToExceptional_left :
    chartToExceptional (centerU (k := k)) ≫ exceptionalProjectiveLineIso.hom =
      leftToProjectiveLine := by
  simp only [chartToExceptional, exceptionalProjectiveLineIso, Iso.trans_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  exact exceptionalFiberProjectiveLineIso_hom_left

/-- The second chart maps to the original second projective chart. -/
theorem chartToExceptional_right :
    chartToExceptional (centerV (k := k)) ≫ exceptionalProjectiveLineIso.hom =
      rightToProjectiveLine := by
  simp only [chartToExceptional, exceptionalProjectiveLineIso, Iso.trans_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  exact exceptionalFiberProjectiveLineIso_hom_right

/-- The actual inverse comparison on the first chart. -/
theorem leftToProjectiveLine_inv :
    leftToProjectiveLine (k := k) ≫ exceptionalProjectiveLineIso.inv =
      chartToExceptional centerU := by
  rw [← chartToExceptional_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The actual inverse comparison on the second chart. -/
theorem rightToProjectiveLine_inv :
    rightToProjectiveLine (k := k) ≫ exceptionalProjectiveLineIso.inv =
      chartToExceptional centerV := by
  rw [← chartToExceptional_right, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Pulling the transported line back to the first chart gives the
pullback of the original global conormal to the original exceptional chart. -/
def leftConormalPullbackIso :
    (schemeModulePullback (leftToProjectiveLine (k := k))).obj conormalLine.obj ≅
      (schemeModulePullback (chartToExceptional centerU)).obj
        (exceptionalConormalSheaf centerIdeal) :=
  (schemeModulePullbackCompIso leftToProjectiveLine exceptionalProjectiveLineIso.inv).app _ ≪≫
    (eqToIso (congrArg schemeModulePullback leftToProjectiveLine_inv)).app _

/-- The analogous exact comparison on the second chart. -/
def rightConormalPullbackIso :
    (schemeModulePullback (rightToProjectiveLine (k := k))).obj conormalLine.obj ≅
      (schemeModulePullback (chartToExceptional centerV)).obj
        (exceptionalConormalSheaf centerIdeal) :=
  (schemeModulePullbackCompIso rightToProjectiveLine exceptionalProjectiveLineIso.inv).app _ ≪≫
    (eqToIso (congrArg schemeModulePullback rightToProjectiveLine_inv)).app _

/-- The original overlap inclusion into the glued exceptional scheme. -/
def overlapToExceptional :
    exceptionalOverlapScheme centerIdeal (centerU (k := k)) centerV ⟶
      exceptionalScheme (centerIdeal (k := k)) :=
  exceptionalOverlapLeftMorphism centerIdeal centerU centerV ≫ chartToExceptional centerU

/-- Both original exceptional chart maps give the same actual overlap map. -/
theorem overlapToExceptional_right :
    overlapToExceptional (k := k) =
      exceptionalOverlapRightMorphism centerIdeal centerU centerV ≫
        chartToExceptional centerV := by
  simp only [overlapToExceptional, chartToExceptional, ← Category.assoc]
  rw [exceptionalOverlap_morphism_condition]

/-- The overlap comparison follows the original left projective chart restriction. -/
theorem overlapToExceptional_projective :
    overlapToExceptional (k := k) ≫ exceptionalProjectiveLineIso.hom =
      overlapIso.hom ≫
        Spec.map (CommRingCat.ofHom (ProjectiveLineComparison.toOverlapLeft k)) ≫
          ProjectiveLineComparison.chartImmersion k 0 := by
  rw [overlapToExceptional, Category.assoc, chartToExceptional_left,
    leftToProjectiveLine, ← Category.assoc, overlapIso_left, Category.assoc]

/-- The actual exceptional overlap ring maps to the original P1 overlap
section ring through the two already proved Laurent coordinate equivalences. -/
def overlapToSectionsEquiv :
    exceptionalOverlapRing centerIdeal (centerU (k := k)) centerV ≃+*
      Γ(projectiveSpace k 1, ProjectiveLineSections.overlapOpen k) :=
  exceptionalOverlapLaurentEquiv.trans (ProjectiveLineSections.overlapSectionsEquiv k).symm

/-- This ring equivalence agrees with the actual projective overlap-ring
comparison followed by its original structure-sheaf section map. -/
theorem overlapToSectionsEquiv_overlapRing (r : ProjectiveLineComparison.overlapRing k) :
    overlapToSectionsEquiv (overlapRingEquiv r) =
      (Proj.awayToSection (ProjectiveLineComparison.grading k)
        ((MvPolynomial.X 0 : ProjectiveLineComparison.homogeneousRing k) *
          MvPolynomial.X 1)).hom r := by
  apply (ProjectiveLineSections.overlapSectionsEquiv k).injective
  simp only [overlapToSectionsEquiv, overlapRingEquiv, RingEquiv.trans_apply,
    RingEquiv.apply_symm_apply]
  exact (ProjectiveLineSections.overlapSectionsEquiv_awayToSection k r).symm

/-- The original ratio unit, now an actual section unit on the original
P1 overlap. No line-bundle transition is supplied as a hypothesis. -/
def conormalRatioSection : Γ(projectiveSpace k 1, ProjectiveLineSections.overlapOpen k)ˣ :=
  Units.map (overlapToSectionsEquiv (k := k)).toRingHom.toMonoidHom
    (exceptionalOverlapTransitionUnit (centerIdeal (k := k)) centerU centerV)

/-- In the shared P1 section coordinates the actual ratio is T. -/
theorem conormalRatioSection_coordinate :
    ProjectiveLineSections.overlapSectionsEquiv k
      (conormalRatioSection (k := k) :
        Γ(projectiveSpace k 1, ProjectiveLineSections.overlapOpen k)) =
      LaurentPolynomial.T 1 := by
  change ProjectiveLineSections.overlapSectionsEquiv k
    ((ProjectiveLineSections.overlapSectionsEquiv k).symm
      ((exceptionalOverlapLaurentEquiv (k := k))
        (exceptionalOverlapTransitionUnit (centerIdeal (k := k)) centerU centerV))) = _
  rw [RingEquiv.apply_symm_apply]
  exact FrobeniusExceptionalConormal.transitionUnit_image

/-- The shared section-unit exponent of the transported actual ratio is one. -/
theorem conormalRatioSection_exponent :
    ProjectiveLineTransitionExponent.overlapExponent k (conormalRatioSection (k := k)) = 1 := by
  apply ProjectiveLineTransitionExponent.unitExponent_eq_of_monomial k _ 1 1
  change ProjectiveLineSections.overlapSectionsEquiv k
    (conormalRatioSection (k := k) :
      Γ(projectiveSpace k 1, ProjectiveLineSections.overlapOpen k)) = _
  rw [conormalRatioSection_coordinate, Units.val_one, map_one, one_mul]

end KltDP.Examples.FrobeniusExceptionalLine

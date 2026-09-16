import KltDP.Examples.FrobeniusExceptionalProjectiveLine

/-!
# The actual exceptional-fiber comparison preserves the coefficient field

The center is identified with `Spec k` through its proved origin quotient,
and the whole fiber receives the corresponding actual structure morphism.
The projective-line comparison preserves this morphism, by its exact chart
restriction formulas and the actual open cover of the fiber.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusExceptionalBaseField

open KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusExceptionalCharts
open FrobeniusExceptionalProjectiveLine

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

/-- The actual inverse center-quotient map sends a scalar to its original constant class. -/
@[simp] theorem originQuotientEquiv_symm (r : k) :
    originQuotientEquiv.symm r = Ideal.Quotient.mk centerIdeal (planeConstants r) := by
  apply originQuotientEquiv.injective
  rw [originQuotientEquiv.apply_symm_apply, originQuotientEquiv_mk, originEvaluation_constants]

/-- The actual center's structure morphism, through the proved field quotient isomorphism. -/
def centerToField : Spec (CommRingCat.of (planeRing k ⧸ centerIdeal)) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom originQuotientEquiv.symm.toRingHom)

/-- The actual coefficient-field structure morphism of the entire center fiber. -/
def fiberStructure : centerFiber (centerIdeal (k := k)) ⟶ Spec (CommRingCat.of k) :=
  centerFiberToCenter centerIdeal ≫ centerToField

/-- Restricting the fiber structure morphism gives the actual original scalar map in the quotient. -/
theorem exceptionalChartToFiber_structure (a : centerIdeal (k := k)) :
    exceptionalChartToFiber centerIdeal a ≫ fiberStructure =
      Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (chartCenterIdeal centerIdeal a)).comp (chartConstants a))) := by
  rw [fiberStructure, ← Category.assoc, exceptionalChartToFiber_toCenter,
    exceptionalChartToCenter, centerToField, ← Spec.map_comp]
  apply congrArg (fun f : k →+* exceptionalChartRing centerIdeal a =>
    Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro r
  change exceptionalChartBaseQuotientMap centerIdeal a (originQuotientEquiv.symm r) =
    Ideal.Quotient.mk (chartCenterIdeal centerIdeal a) (chartConstants a r)
  rw [originQuotientEquiv_symm, exceptionalChartBaseQuotientMap_mk]
  rfl

/-- The first projective chart comparison preserves the actual original scalar map. -/
theorem leftToProjectiveLine_structure :
    leftToProjectiveLine (k := k) ≫ KltDP.Geometry.projectiveSpaceToSpec k 1 =
      Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (chartCenterIdeal (centerIdeal (k := k)) centerU)).comp
          (chartConstants (centerU (k := k))))) := by
  rw [leftToProjectiveLine, Category.assoc,
    KltDP.Geometry.ProjectiveLineComparison.chartImmersion_structureMap]
  change Spec.map (CommRingCat.ofHom (leftRingEquiv (k := k)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (KltDP.Geometry.ProjectiveLineComparison.chartConstants k 0)) = _
  rw [← Spec.map_comp]
  apply congrArg (fun f : k →+* exceptionalChartRing centerIdeal centerU =>
    Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro r
  change uExceptionalEquiv.symm
      (KltDP.Geometry.ProjectiveLineComparison.firstChartPolynomialEquiv k
        (KltDP.Geometry.ProjectiveLineComparison.chartConstants k 0 r)) =
    Ideal.Quotient.mk (chartCenterIdeal (centerIdeal (k := k)) centerU) (chartConstants centerU r)
  rw [KltDP.Geometry.ProjectiveLineComparison.firstChartPolynomialEquiv_constants]
  apply uExceptionalEquiv.injective
  rw [uExceptionalEquiv.apply_symm_apply, uExceptionalEquiv_constants]

/-- The second projective chart comparison preserves the same actual scalar map. -/
theorem rightToProjectiveLine_structure :
    rightToProjectiveLine (k := k) ≫ KltDP.Geometry.projectiveSpaceToSpec k 1 =
      Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (chartCenterIdeal (centerIdeal (k := k)) centerV)).comp
          (chartConstants (centerV (k := k))))) := by
  rw [rightToProjectiveLine, Category.assoc,
    KltDP.Geometry.ProjectiveLineComparison.chartImmersion_structureMap]
  change Spec.map (CommRingCat.ofHom (rightRingEquiv (k := k)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (KltDP.Geometry.ProjectiveLineComparison.chartConstants k 1)) = _
  rw [← Spec.map_comp]
  apply congrArg (fun f : k →+* exceptionalChartRing centerIdeal centerV =>
    Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro r
  change vExceptionalEquiv.symm
      (KltDP.Geometry.ProjectiveLineComparison.secondChartPolynomialEquiv k
        (KltDP.Geometry.ProjectiveLineComparison.chartConstants k 1 r)) =
    Ideal.Quotient.mk (chartCenterIdeal (centerIdeal (k := k)) centerV) (chartConstants centerV r)
  rw [KltDP.Geometry.ProjectiveLineComparison.secondChartPolynomialEquiv_constants]
  apply vExceptionalEquiv.injective
  rw [vExceptionalEquiv.apply_symm_apply, vExceptionalEquiv_constants]

/-- The constructed whole-fiber isomorphism is over the original coefficient field. -/
theorem exceptionalFiberProjectiveLineIso_hom_structure :
    (exceptionalFiberProjectiveLineIso (k := k)).hom ≫
      KltDP.Geometry.projectiveSpaceToSpec k 1 = fiberStructure := by
  let 𝒰 := exceptionalOpenCover centerIdeal (centerGenerator (k := k)) span_centerGenerator
  let 𝒱 : Scheme.OpenCover.{u} (centerFiber (centerIdeal (k := k))) :=
    { J := ULift.{u} 𝒰.J
      obj i := 𝒰.obj i.down
      map i := 𝒰.map i.down
      f x := ⟨𝒰.f x⟩
      covers x := 𝒰.covers x
      map_prop i := 𝒰.map_prop i.down }
  apply 𝒱.hom_ext
  rintro ⟨i⟩
  cases i
  · change exceptionalChartToFiber centerIdeal centerU ≫
        (exceptionalFiberProjectiveLineIso.hom ≫ KltDP.Geometry.projectiveSpaceToSpec k 1) =
      exceptionalChartToFiber centerIdeal centerU ≫ fiberStructure
    rw [← Category.assoc, exceptionalFiberProjectiveLineIso_hom_left,
      leftToProjectiveLine_structure, exceptionalChartToFiber_structure]
  · change exceptionalChartToFiber centerIdeal centerV ≫
        (exceptionalFiberProjectiveLineIso.hom ≫ KltDP.Geometry.projectiveSpaceToSpec k 1) =
      exceptionalChartToFiber centerIdeal centerV ≫ fiberStructure
    rw [← Category.assoc, exceptionalFiberProjectiveLineIso_hom_right,
      rightToProjectiveLine_structure, exceptionalChartToFiber_structure]

end KltDP.Examples.FrobeniusExceptionalBaseField

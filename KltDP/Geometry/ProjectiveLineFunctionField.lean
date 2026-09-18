import KltDP.Geometry.ProjectiveSpaceAffineRationality
import KltDP.Geometry.BirationalFunctionFieldStalkAlgebra
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.AlgebraicGeometry.FunctionField

/-! The original projective-line function field is RatFunc over the original
ground field. The equivalence restricts through the actual first chart and
extends its original polynomial coordinate equivalence to fraction fields. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ProjectiveLineFunctionField

open ProjectiveChart IntrinsicNodal

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

local instance line_integral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

local instance chart_domain : IsDomain (chartRing k 1) := chartRing_isDomain k 1

local instance chart_genericPointPreserving : GenericPointPreserving (chartMorphism k 1) :=
  ⟨genericPoint_eq_of_isOpenImmersion (chartMorphism k 1)⟩

/-- The original first chart, with its coordinate indexed by Fin 1. -/
abbrev chartScheme : Scheme.{u} := Spec (CommRingCat.of (chartRing k 1))

-- These are the original affine generic-stalk localization instances.
local instance chart_functionFieldAlgebra :
    Algebra (chartRing k 1) (chartScheme k).functionField :=
  (StructureSheaf.toStalk (CommRingCat.of (chartRing k 1))
    (genericPoint (chartScheme k))).hom.toAlgebra

local instance chart_functionFieldIsFractionRing :
    IsFractionRing (chartRing k 1) (chartScheme k).functionField :=
  functionField_isFractionRing_of_affine (CommRingCat.of (chartRing k 1))

local instance line_baseAlgebra : Algebra k (projectiveSpace k 1).functionField :=
  stalkAlgebra (projectiveSpaceToSpec k 1) (genericPoint (projectiveSpace k 1))

local instance chart_baseAlgebra : Algebra k (chartScheme k).functionField :=
  stalkAlgebra (Spec.map (CommRingCat.ofHom (constants k 1)))
    (genericPoint (chartScheme k))

/-- The actual dehomogenization equivalence followed by the one-variable dictionary. -/
def polynomialCoordinates : chartRing k 1 ≃+* Polynomial k :=
  (coordinateRingEquiv k 1).trans
    ((MvPolynomial.renameEquiv k (Equiv.equivPUnit (Fin 1) : Fin 1 ≃ PUnit.{1})).trans
      (MvPolynomial.pUnitAlgEquiv k)).toRingEquiv

@[simp]
theorem polynomialCoordinates_constants (r : k) :
    polynomialCoordinates k (constants k 1 r) = Polynomial.C r := by
  let e := (MvPolynomial.renameEquiv k (Equiv.equivPUnit (Fin 1) : Fin 1 ≃ PUnit.{1})).trans
    (MvPolynomial.pUnitAlgEquiv k)
  change e (coordinateRingEquiv k 1 (constants k 1 r)) = Polynomial.C r
  rw [coordinateRingEquiv_constants]
  exact e.commutes r

/-- Extend the exact original chart ring equivalence to its actual generic stalk. -/
def chartFractionFieldEquiv : (chartScheme k).functionField ≃+* RatFunc k :=
  IsFractionRing.ringEquivOfRingEquiv (polynomialCoordinates k)

@[simp]
theorem chartFractionFieldEquiv_algebraMap (a : chartRing k 1) :
    chartFractionFieldEquiv k (algebraMap (chartRing k 1) (chartScheme k).functionField a) =
      algebraMap (Polynomial k) (RatFunc k) (polynomialCoordinates k a) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (polynomialCoordinates k) a

/-- The original affine structure map supplies precisely the original coefficient embedding. -/
theorem chart_baseToStalkMap :
    baseToStalkMap (Spec.map (CommRingCat.ofHom (constants k 1)))
        (genericPoint (chartScheme k)) =
      CommRingCat.ofHom (constants k 1) ≫
        CommRingCat.ofHom (algebraMap (chartRing k 1) (chartScheme k).functionField) := by
  apply Spec.map_injective
  rw [Spec_map_baseToStalkMap, Spec.map_comp, Scheme.Spec_fromSpecStalk']
  rfl

/-- The fraction-field dictionary preserves the intrinsic scalars of the original affine map. -/
def chartFractionFieldAlgEquiv :
    letI := stalkAlgebra (Spec.map (CommRingCat.ofHom (constants k 1)))
      (genericPoint (chartScheme k))
    (chartScheme k).functionField ≃ₐ[k] RatFunc k := by
  letI := stalkAlgebra (Spec.map (CommRingCat.ofHom (constants k 1)))
    (genericPoint (chartScheme k))
  refine { chartFractionFieldEquiv k with commutes' := ?_ }
  intro r
  change chartFractionFieldEquiv k
    ((baseToStalkMap (Spec.map (CommRingCat.ofHom (constants k 1)))
      (genericPoint (chartScheme k))).hom r) = algebraMap k (RatFunc k) r
  rw [chart_baseToStalkMap]
  change chartFractionFieldEquiv k
    (algebraMap (chartRing k 1) (chartScheme k).functionField (constants k 1 r)) = _
  rw [chartFractionFieldEquiv_algebraMap, polynomialCoordinates_constants]
  exact RatFunc.algebraMap_C r

/-- Restriction is the original generic-stalk map of the actual first chart. -/
def chartRestriction :
    letI := stalkAlgebra (projectiveSpaceToSpec k 1) (genericPoint (projectiveSpace k 1))
    letI := stalkAlgebra (Spec.map (CommRingCat.ofHom (constants k 1)))
      (genericPoint (chartScheme k))
    (projectiveSpace k 1).functionField ≃ₐ[k] (chartScheme k).functionField :=
  BirationalFunctionFieldStalkAlgebra.equiv
    (Spec.map (CommRingCat.ofHom (constants k 1))) (projectiveSpaceToSpec k 1)
    (chartMorphism k 1) (coordinateChartMorphism_over_base k 1 0)
    ⟨genericPoint_eq_of_isOpenImmersion (chartMorphism k 1), inferInstance⟩

/-- The restriction equivalence uses exactly the original function-field map. -/
theorem chartRestriction_apply (a : (projectiveSpace k 1).functionField) :
    chartRestriction k a = functionFieldMap (chartMorphism k 1) a := by
  exact congrArg (fun g : (projectiveSpace k 1).functionField →+*
      (chartScheme k).functionField => g a)
    (BirationalFunctionFieldStalkAlgebra.equiv_toRingHom
      (Spec.map (CommRingCat.ofHom (constants k 1))) (projectiveSpaceToSpec k 1)
      (chartMorphism k 1) (coordinateChartMorphism_over_base k 1 0)
      ⟨genericPoint_eq_of_isOpenImmersion (chartMorphism k 1), inferInstance⟩)

/-- The actual projective-line function field over its original ground field. -/
def equiv :
    letI := stalkAlgebra (projectiveSpaceToSpec k 1) (genericPoint (projectiveSpace k 1))
    (projectiveSpace k 1).functionField ≃ₐ[k] RatFunc k := by
  letI := stalkAlgebra (projectiveSpaceToSpec k 1) (genericPoint (projectiveSpace k 1))
  letI := stalkAlgebra (Spec.map (CommRingCat.ofHom (constants k 1)))
    (genericPoint (chartScheme k))
  exact (chartRestriction k).trans (chartFractionFieldAlgEquiv k)

/-- No replacement generic map occurs in the construction. -/
theorem equiv_apply (a : (projectiveSpace k 1).functionField) :
    equiv k a = chartFractionFieldEquiv k (functionFieldMap (chartMorphism k 1) a) := by
  change chartFractionFieldEquiv k (chartRestriction k a) = _
  rw [chartRestriction_apply]

/-- The equivalence sends an original chart polynomial to that same polynomial in RatFunc. -/
theorem equiv_chart_algebraMap (a : chartRing k 1) :
    equiv k ((chartRestriction k).symm
      (algebraMap (chartRing k 1) (chartScheme k).functionField a)) =
        algebraMap (Polynomial k) (RatFunc k) (polynomialCoordinates k a) := by
  change (chartFractionFieldAlgEquiv k) ((chartRestriction k) ((chartRestriction k).symm
    (algebraMap (chartRing k 1) (chartScheme k).functionField a))) = _
  rw [AlgEquiv.apply_symm_apply]
  exact chartFractionFieldEquiv_algebraMap k a

/-- The actual dehomogenized chart coordinate maps to the rational-function variable. -/
theorem equiv_chart_coordinate :
    equiv k ((chartRestriction k).symm
      (algebraMap (chartRing k 1) (chartScheme k).functionField
        ((polynomialCoordinates k).symm Polynomial.X))) = RatFunc.X := by
  rw [equiv_chart_algebraMap, RingEquiv.apply_symm_apply]
  rfl

end KltDP.Geometry.ProjectiveLineFunctionField

#check @KltDP.Geometry.ProjectiveLineFunctionField.equiv
#print axioms KltDP.Geometry.ProjectiveLineFunctionField.equiv
#print axioms KltDP.Geometry.ProjectiveLineFunctionField.equiv_chart_coordinate

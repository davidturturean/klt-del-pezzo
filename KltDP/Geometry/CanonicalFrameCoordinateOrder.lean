import KltDP.Geometry.CanonicalCoordinateNormalization

/-!
# The actual coordinates of a fixed canonical frame have equal model orders

For two Cartier identifications with the same original module and the same
target Weil normalization, the actual coordinate of the original D-frame
under the E-identification is nonzero and has the same original model order
as its D-coordinate. The coordinate unit is constructed from the proved
scalar of those identifications, rather than supplied as a comparison input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.CanonicalNormalization

open CartierRationalCoordinate

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] integralSchemeStalk_isDomain

variable {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) (U : X.toScheme.Opens) [Nonempty U.toScheme]

local instance : Nonempty U := ⟨Classical.choice inferInstance⟩
local instance : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

/-- The same original frame has coordinates of equal order on every
original integral model, including models that are not proper. -/
theorem exists_frame_coordinate_unit_order_eq_on_models
    (hU : ∀ C : X.PrimeCurve, C.genericPoint ∈ U)
    (D E : CartierDivisor U.toScheme) (M : U.toScheme.Modules)
    (eD : cartierDivisorModule U.toScheme D ≅ M)
    (eE : cartierDivisorModule U.toScheme E ≅ M)
    (hext : OpenCartierWeil.restrictedWeilHom U D =
      OpenCartierWeil.restrictedWeilHom U E)
    (c : CartierEquationChart U.toScheme D) :
    ∃ r : U.toScheme.functionFieldˣ,
      (r : U.toScheme.functionField) =
        rationalFunctionModuleSectionsEquiv U.toScheme c.openSet
          ((coordinate U.toScheme E M eE).val.app (op c.openSet)
            (frame U.toScheme D M eD c)) ∧
      ∀ (V : Scheme.{u}) [IsIntegral V] (v : V ⟶ X.toScheme)
        [GenericPointPreserving v] (x : V)
        [IsDiscreteValuationRing (V.presheaf.stalk x)],
        stalkDivisorOrder V x
          (Units.map (functionFieldMap v).hom.toMonoidHom
            (OpenCartierWeil.transportUnit U r)) =
        stalkDivisorOrder V x
          (Units.map (functionFieldMap v).hom.toMonoidHom
            (OpenCartierWeil.transportUnit U c.equation⁻¹)) := by
  obtain ⟨q, _, hcoordinate, horder⟩ :=
    exists_coordinate_scalar_order_zero_on_models X U hU D E M eD eE hext
  have hvalue := congrArg (fun a : M ⟶ rationalFunctionModule U.toScheme =>
    rationalFunctionModuleSectionsEquiv U.toScheme c.openSet
      (a.val.app (op c.openSet) (frame U.toScheme D M eD c))) hcoordinate
  have hmul := rationalFunctionMulIso_hom_app_field U.toScheme q c.openSet
    ((coordinate U.toScheme D M eD).val.app (op c.openSet)
      (frame U.toScheme D M eD c))
  rw [coordinate_frame_value] at hmul
  refine ⟨q * c.equation⁻¹, ?_, ?_⟩
  · exact (hvalue.trans hmul).symm
  · intro V hV v hv x hx
    rw [OpenCartierWeil.transportUnit_mul, map_mul, stalkDivisorOrder_mul,
      horder V v x, zero_add]

end KltDP.Geometry.CanonicalNormalization

#check @KltDP.Geometry.CanonicalNormalization.exists_frame_coordinate_unit_order_eq_on_models
#print axioms KltDP.Geometry.CanonicalNormalization.exists_frame_coordinate_unit_order_eq_on_models

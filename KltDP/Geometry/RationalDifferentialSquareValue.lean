import KltDP.Geometry.RationalOpenPullbackAdjoint
import KltDP.Geometry.CartierDivisorPullbackComp
import KltDP.Geometry.CartierOrderOpenRestriction
import KltDP.Geometry.CartierFrames
import KltDP.Geometry.SchemeModuleAdjunctionCompSections

/-!
# Evaluating the original rational square on an original section

This is the section-level consequence of a square of actual module maps.
The square will be supplied by the proved normalization witness, while
this lemma uses the original adjunction units and original field maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.RationalDifferentialSquareValue

open OpenImmersionRational

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance openGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : A ⟶ B) [IsOpenImmersion i] : GenericPointPreserving i :=
  ⟨genericPoint_eq_of_isOpenImmersion i⟩

section AdjointSquare

attribute [local irreducible] schemeModulePullbackPushforwardAdjunction
  schemeModulePullbackCompIso

/-- Naturality for one original open pullback, kept opaque before it is
inserted into the composite adjunction expression. -/
private theorem adjoint_rational_map
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (c : M ⟶ rationalFunctionModule X) :
    (schemeModulePullbackPushforwardAdjunction f).homEquiv M
        (rationalFunctionModule Y)
        ((schemeModulePullback f).map c ≫ (rationalModulePullbackIso f).hom) =
      c ≫ rationalOpenAdjoint f := by
  rw [(schemeModulePullbackPushforwardAdjunction f).homEquiv_naturality_left
    c (rationalModulePullbackIso f).hom, rationalModulePullbackIso_adjoint]

/-- The left-hand naturality calculation under the two original
adjunctions, with no composite right-hand expression unfolded here. -/
private theorem adjoint_left_rational_map
    {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (p : Y ⟶ X) (l : Z ⟶ Y) [IsOpenImmersion l]
    (M : X.Modules) (a : (schemeModulePullback p).obj M ⟶ rationalFunctionModule Y) :
    (schemeModulePullbackPushforwardAdjunction p).homEquiv M
        ((schemeModulePushforward l).obj (rationalFunctionModule Z))
        ((schemeModulePullbackPushforwardAdjunction l).homEquiv
          ((schemeModulePullback p).obj M) (rationalFunctionModule Z)
          ((schemeModulePullback l).map a ≫ (rationalModulePullbackIso l).hom)) =
      (schemeModulePullbackPushforwardAdjunction p).homEquiv M
          (rationalFunctionModule Y) a ≫
        (schemeModulePushforward p).map (rationalOpenAdjoint l) := by
  rw [(schemeModulePullbackPushforwardAdjunction l).homEquiv_naturality_left
    a (rationalModulePullbackIso l).hom, rationalModulePullbackIso_adjoint,
    (schemeModulePullbackPushforwardAdjunction p).homEquiv_naturality_right
      a (rationalOpenAdjoint l)]

/-- Evaluate the original square before comparing the iterated and
composite pushforward carriers. The explicit comparison is discharged by
the proved original section formula, not by reducing whole module objects. -/
private theorem adjoint_open_square_app
    {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (p : Y ⟶ X) [GenericPointPreserving p]
    (l : Z ⟶ Y) [IsOpenImmersion l] [IsOpenImmersion (l ≫ p)]
    (M : X.Modules)
    (a : (schemeModulePullback p).obj M ⟶ rationalFunctionModule Y)
    (c : M ⟶ rationalFunctionModule X)
    (h : (schemeModulePullback l).map a ≫ (rationalModulePullbackIso l).hom =
      (schemeModulePullbackCompIso l p).hom.app M ≫
        (schemeModulePullback (l ≫ p)).map c ≫ (rationalModulePullbackIso (l ≫ p)).hom)
    (U : X.Opens) (s : M.val.obj (op U)) :
    ((schemeModulePullbackPushforwardAdjunction p).homEquiv M
        (rationalFunctionModule Y) a ≫
      (schemeModulePushforward p).map (rationalOpenAdjoint l)).val.app (op U) s =
    (c ≫ rationalOpenAdjoint (l ≫ p)).val.app (op U) s := by
  have heq := congrArg
    (fun b => ((schemeModulePullbackPushforwardAdjunction p).homEquiv M
      ((schemeModulePushforward l).obj (rationalFunctionModule Z))
      ((schemeModulePullbackPushforwardAdjunction l).homEquiv
        ((schemeModulePullback p).obj M) (rationalFunctionModule Z) b)).val.app (op U) s) h
  have hleft := congrArg
    (fun b : M ⟶ (schemeModulePushforward p).obj
        ((schemeModulePushforward l).obj (rationalFunctionModule Z)) =>
      b.val.app (op U) s) (adjoint_left_rational_map p l M a)
  have hcomp := schemeModulePullbackCompIso_homEquiv_app l p M
    (rationalFunctionModule Z)
    ((schemeModulePullback (l ≫ p)).map c ≫ (rationalModulePullbackIso (l ≫ p)).hom) U s
  have hright := congrArg
    (fun b : M ⟶ (schemeModulePushforward (l ≫ p)).obj (rationalFunctionModule Z) =>
      b.val.app (op U) s) (adjoint_rational_map (l ≫ p) M c)
  exact hleft.symm.trans (heq.trans (hcomp.trans hright))

end AdjointSquare

/-- Evaluation of an actual pullback square is the original function-field
map, proved by the original composite-adjunction normalization. -/
theorem field_value_of_open_square
    {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (p : Y ⟶ X) [GenericPointPreserving p]
    (l : Z ⟶ Y) [IsOpenImmersion l] [IsOpenImmersion (l ≫ p)]
    (M : X.Modules)
    (a : (schemeModulePullback p).obj M ⟶ rationalFunctionModule Y)
    (c : M ⟶ rationalFunctionModule X)
    (h : (schemeModulePullback l).map a ≫ (rationalModulePullbackIso l).hom =
      (schemeModulePullbackCompIso l p).hom.app M ≫
        (schemeModulePullback (l ≫ p)).map c ≫ (rationalModulePullbackIso (l ≫ p)).hom)
    (U : X.Opens) [Nonempty U] (s : M.val.obj (op U)) :
    rationalFunctionModuleSectionsEquiv Y (p ⁻¹ᵁ U)
        (a.val.app (op (p ⁻¹ᵁ U)) (pullbackSection p M U s)) =
      functionFieldMap p
        (rationalFunctionModuleSectionsEquiv X U (c.val.app (op U) s)) := by
  have hsection := adjoint_open_square_app p l M a c h U s
  have hv := congrArg (rationalFunctionModuleSectionsEquiv Z ((l ≫ p) ⁻¹ᵁ U)) hsection
  let t := a.val.app (op (p ⁻¹ᵁ U)) (pullbackSection p M U s)
  change rationalFunctionModuleSectionsEquiv Z (l ⁻¹ᵁ (p ⁻¹ᵁ U))
      ((rationalOpenAdjoint l).val.app (op (p ⁻¹ᵁ U)) t) =
    rationalFunctionModuleSectionsEquiv Z ((l ≫ p) ⁻¹ᵁ U)
      ((rationalOpenAdjoint (l ≫ p)).val.app (op U) (c.val.app (op U) s)) at hv
  have hleft := rationalOpenAdjoint_field l (p ⁻¹ᵁ U) t
  have hright := rationalOpenAdjoint_field (l ≫ p) U (c.val.app (op U) s)
  have hfield := hleft.symm.trans (hv.trans hright)
  apply (functionFieldIso l).hom.hom.injective
  change functionFieldMap l
      (rationalFunctionModuleSectionsEquiv Y (p ⁻¹ᵁ U) t) =
    functionFieldMap l (functionFieldMap p
      (rationalFunctionModuleSectionsEquiv X U (c.val.app (op U) s)))
  change functionFieldMap l
      (rationalFunctionModuleSectionsEquiv Y (p ⁻¹ᵁ U) t) =
    functionFieldMap (l ≫ p)
      (rationalFunctionModuleSectionsEquiv X U (c.val.app (op U) s)) at hfield
  exact hfield.trans (ConcreteCategory.congr_hom
    (CartierDivisorPullbackComp.functionFieldMap_comp l p)
      (rationalFunctionModuleSectionsEquiv X U (c.val.app (op U) s)))

end KltDP.Geometry.RationalDifferentialSquareValue

#check @KltDP.Geometry.RationalDifferentialSquareValue.field_value_of_open_square
#print axioms KltDP.Geometry.RationalDifferentialSquareValue.field_value_of_open_square

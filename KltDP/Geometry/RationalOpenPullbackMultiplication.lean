import KltDP.Geometry.RationalOpenPullbackAdjoint
import KltDP.Geometry.CartierPrincipalShift

/-!
# Rational multiplication under the original open pullback

The pullback of multiplication by a rational unit is multiplication by
its original generic-stalk image. The proof compares the actual adjoints
on every section, including the actual zero module of an empty open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.OpenImmersionRational

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsOpenImmersion f] (q : X.functionFieldˣ)

/-- Rational multiplication commutes with the actual adjoint field map. -/
theorem rationalOpenAdjoint_mul :
    (rationalFunctionMulIso X q).hom ≫ rationalOpenAdjoint f =
      rationalOpenAdjoint f ≫ (schemeModulePushforward f).map
        (rationalFunctionMulIso Y
          (Units.map (functionFieldIso f).hom.hom.toMonoidHom q)).hom := by
  apply _root_.SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  classical
  by_cases hU : Nonempty U.unop
  · letI := hU
    letI := preimage_nonempty f U.unop
    apply (rationalFunctionModuleSectionsEquiv Y (f ⁻¹ᵁ U.unop)).injective
    change rationalFunctionModuleSectionsEquiv Y (f ⁻¹ᵁ U.unop)
        ((rationalOpenAdjoint f).val.app U
          ((rationalFunctionMulIso X q).hom.val.app U s)) =
      rationalFunctionModuleSectionsEquiv Y (f ⁻¹ᵁ U.unop)
        ((rationalFunctionMulIso Y
          (Units.map (functionFieldIso f).hom.hom.toMonoidHom q)).hom.val.app
            (op (f ⁻¹ᵁ U.unop)) ((rationalOpenAdjoint f).val.app U s))
    rw [rationalOpenAdjoint_field, rationalFunctionMulIso_hom_app_field,
      rationalFunctionMulIso_hom_app_field, rationalOpenAdjoint_field]
    exact (functionFieldIso f).hom.hom.map_mul _ _
  · have hV : ¬ Nonempty (f ⁻¹ᵁ U.unop) := by
      rintro ⟨⟨y, hy⟩⟩
      exact hU ⟨⟨f.base y, hy⟩⟩
    letI := sectionRing_subsingleton_of_empty (f ⁻¹ᵁ U.unop) hV
    letI : Subsingleton ((rationalFunctionModule Y).val.obj
        (op (f ⁻¹ᵁ U.unop))) := Module.subsingleton Γ(Y, f ⁻¹ᵁ U.unop) _
    exact @Subsingleton.elim
      ((rationalFunctionModule Y).val.obj (op (f ⁻¹ᵁ U.unop))) inferInstance _ _

/-- The original rational-module pullback intertwines the actual
multiplication maps, with the actual original field transport. -/
theorem rationalModulePullbackIso_mul :
    (schemeModulePullback f).map (rationalFunctionMulIso X q).hom ≫
        (rationalModulePullbackIso f).hom =
      (rationalModulePullbackIso f).hom ≫ (rationalFunctionMulIso Y
        (Units.map (functionFieldIso f).hom.hom.toMonoidHom q)).hom := by
  apply ((schemeModulePullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    rationalModulePullbackIso_adjoint]
  exact rationalOpenAdjoint_mul f q

end KltDP.Geometry.OpenImmersionRational

#check @KltDP.Geometry.OpenImmersionRational.rationalModulePullbackIso_mul
#print axioms KltDP.Geometry.OpenImmersionRational.rationalModulePullbackIso_mul

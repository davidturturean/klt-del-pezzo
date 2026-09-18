import KltDP.Geometry.RationalOpenPullbackAdjoint

/-!
# Composition of the original rational-module pullbacks

Two successive original open immersions act on rational functions by
the composite original generic-stalk map. The original scheme-module
pullback comparison therefore identifies their actual module maps.
Empty opens are handled by their actual zero section modules.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.OpenImmersionRational

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : Z ⟶ Y) (g : Y ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]

/-- The section equality is assembled from the three already proved field
formulas, without rewriting large sheaf expressions. -/
private theorem rationalOpenAdjoint_comp_field (U : X.Opens) [Nonempty U]
    (s : (rationalFunctionModule X).val.obj (op U)) :
    letI := preimage_nonempty g U
    letI := preimage_nonempty f (g ⁻¹ᵁ U)
    letI := preimage_nonempty (f ≫ g) U
    rationalFunctionModuleSectionsEquiv Z (f ⁻¹ᵁ (g ⁻¹ᵁ U))
        ((rationalOpenAdjoint f).val.app (op (g ⁻¹ᵁ U))
          ((rationalOpenAdjoint g).val.app (op U) s)) =
      rationalFunctionModuleSectionsEquiv Z ((f ≫ g) ⁻¹ᵁ U)
        ((rationalOpenAdjoint (f ≫ g)).val.app (op U) s) := by
  letI := preimage_nonempty g U
  letI := preimage_nonempty f (g ⁻¹ᵁ U)
  letI := preimage_nonempty (f ≫ g) U
  have hf := rationalOpenAdjoint_field f (g ⁻¹ᵁ U)
    ((rationalOpenAdjoint g).val.app (op U) s)
  have hg := congrArg (fun t : Y.functionField => (functionFieldIso f).hom t)
    (rationalOpenAdjoint_field g U s)
  have hc := ConcreteCategory.congr_hom (functionFieldIso_comp_hom g f)
    (rationalFunctionModuleSectionsEquiv X U s)
  have hfg := rationalOpenAdjoint_field (f ≫ g) U s
  exact hf.trans (hg.trans (hc.symm.trans hfg.symm))

/-- The original adjoint rational maps compose on the original sections. -/
theorem rationalOpenAdjoint_comp :
    rationalOpenAdjoint g ≫
        (schemeModulePushforward g).map (rationalOpenAdjoint f) =
      rationalOpenAdjoint (f ≫ g) := by
  apply _root_.SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  classical
  by_cases hU : Nonempty U.unop
  · letI := hU
    letI := preimage_nonempty g U.unop
    letI := preimage_nonempty f (g ⁻¹ᵁ U.unop)
    letI := preimage_nonempty (f ≫ g) U.unop
    apply (rationalFunctionModuleSectionsEquiv Z ((f ≫ g) ⁻¹ᵁ U.unop)).injective
    change rationalFunctionModuleSectionsEquiv Z (f ⁻¹ᵁ (g ⁻¹ᵁ U.unop))
        ((rationalOpenAdjoint f).val.app (op (g ⁻¹ᵁ U.unop))
          ((rationalOpenAdjoint g).val.app U s)) =
      rationalFunctionModuleSectionsEquiv Z ((f ≫ g) ⁻¹ᵁ U.unop)
        ((rationalOpenAdjoint (f ≫ g)).val.app U s)
    exact rationalOpenAdjoint_comp_field f g U.unop s
  · have hV : ¬ Nonempty ((f ≫ g) ⁻¹ᵁ U.unop) := by
      rintro ⟨⟨z, hz⟩⟩
      exact hU ⟨⟨(f ≫ g).base z, hz⟩⟩
    letI := sectionRing_subsingleton_of_empty ((f ≫ g) ⁻¹ᵁ U.unop) hV
    letI : Subsingleton ((rationalFunctionModule Z).val.obj
        (op ((f ≫ g) ⁻¹ᵁ U.unop))) :=
      Module.subsingleton Γ(Z, (f ≫ g) ⁻¹ᵁ U.unop) _
    exact @Subsingleton.elim
      ((rationalFunctionModule Z).val.obj (op ((f ≫ g) ⁻¹ᵁ U.unop)))
      inferInstance _ _

/-- The original two-step rational pullback equals the original composite
pullback through the original scheme-module composition isomorphism. -/
theorem rationalModulePullbackIso_comp :
    (schemeModulePullback f).map (rationalModulePullbackIso g).hom ≫
        (rationalModulePullbackIso f).hom =
      (schemeModulePullbackCompIso f g).hom.app (rationalFunctionModule X) ≫
        (rationalModulePullbackIso (f ≫ g)).hom := by
  apply ((schemeModulePullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply ((schemeModulePullbackPushforwardAdjunction g).homEquiv _ _).injective
  rw [schemeModulePullbackCompIso_homEquiv,
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    rationalModulePullbackIso_adjoint, rationalModulePullbackIso_adjoint,
    rationalModulePullbackIso_adjoint]
  exact rationalOpenAdjoint_comp f g

end KltDP.Geometry.OpenImmersionRational

#check @KltDP.Geometry.OpenImmersionRational.rationalModulePullbackIso_comp
#print axioms KltDP.Geometry.OpenImmersionRational.rationalModulePullbackIso_comp

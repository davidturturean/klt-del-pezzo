import KltDP.Geometry.FunctionFieldIntegralClosureRestriction
import KltDP.Geometry.FunctionFieldNormalizationGenericMap

/-!
# Normalization in the original function field, by actual affine charts

The property below describes an actual scheme morphism by spectra of the
integral closures of its target's original affine section rings in its
original generic stalk.  Its charts commute with the original projections
and with the literal integral-closure restriction maps.  It contains no
finiteness, regularity, projectivity, completion or resolution assertion.

Comparison with the Stacks generic-point relative-normalization
construction, and admission of any literature theorem, remain separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

open NormalSchemeAffineNormalization

/-- Actual inverse-image chart isomorphisms for a morphism to an integral scheme. -/
abbrev FunctionFieldNormalizationCharts {N X : Scheme.{u}} [IsIntegral X]
    (ν : N ⟶ X) :=
  ∀ (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U],
    (ν ⁻¹ᵁ U).toScheme ≅ chart X U

/-- An actual morphism is described by the original function-field
integral-closure spectra, their projections, and their restriction maps. -/
def IsNormalizationInFunctionField {N X : Scheme.{u}} [IsIntegral X]
    (ν : N ⟶ X) : Prop :=
  ∃ e : FunctionFieldNormalizationCharts ν,
    (∀ (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U],
      (e U hU).hom ≫ projection X U ≫ hU.fromSpec = (ν ⁻¹ᵁ U).ι ≫ ν) ∧
    (∀ (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
        [Nonempty U] [Nonempty V] (hVU : V ≤ U),
      N.homOfLE (ν.preimage_le_preimage_of_le hVU) ≫ (e U hU).hom =
        (e V hV).hom ≫ Spec.map (CommRingCat.ofHom (restriction X hVU)))

namespace NormalSchemeAffineNormalization

/-- The original normal-open isomorphisms respect the actual open inclusions. -/
theorem originalOpenIso_naturality (X : Scheme.{u}) [IsIntegral X]
    (hnormal : IsNormalScheme X) (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    [Nonempty U] [Nonempty V] (hVU : V ≤ U) :
    X.homOfLE hVU ≫ (originalOpenIso X hnormal U hU).hom =
      (originalOpenIso X hnormal V hV).hom ≫
        Spec.map (CommRingCat.ofHom (restriction X hVU)) := by
  letI : IsIso (projection X U) := projection_isIso X hnormal U
  apply (cancel_mono (projection X U ≫ hU.fromSpec)).mp
  calc
    _ = X.homOfLE hVU ≫ U.ι := by
      simp only [Category.assoc, originalOpenIso_projection, Category.comp_id]
    _ = V.ι := X.homOfLE_ι hVU
    _ = ((originalOpenIso X hnormal V hV).hom ≫
        Spec.map (CommRingCat.ofHom (restriction X hVU))) ≫
          (projection X U ≫ hU.fromSpec) := by
      simp only [Category.assoc, restriction_projection_assoc,
        hU.map_fromSpec hV (homOfLE hVU).op, originalOpenIso_projection, Category.comp_id]

end NormalSchemeAffineNormalization

/-- The identity of the original integral normal scheme has the actual
function-field normalization charts, with all projection and overlap diagrams. -/
theorem isNormalizationInFunctionField_id (X : Scheme.{u}) [IsIntegral X]
    (hnormal : IsNormalScheme X) : IsNormalizationInFunctionField (𝟙 X) := by
  let e : FunctionFieldNormalizationCharts (𝟙 X) := fun U hU hne => by
    letI : Nonempty U := hne
    exact originalOpenIso X hnormal U hU
  refine ⟨e, ?_, ?_⟩
  · intro U hU hne
    letI : Nonempty U := hne
    exact originalOpenIso_projection X hnormal U hU
  · intro U V hU hV hneU hneV hVU
    letI : Nonempty U := hneU
    letI : Nonempty V := hneV
    exact originalOpenIso_naturality X hnormal U V hU hV hVU

namespace IsNormalizationInFunctionField

/-- The chart property supplies a factorization of the canonical generic-point
map itself.  The generic map is constructed, not an additional input. -/
theorem exists_generic_map {N X : Scheme.{u}} [IsIntegral X] {ν : N ⟶ X}
    (hν : IsNormalizationInFunctionField ν) :
    ∃ γ : Spec X.functionField ⟶ N,
      γ ≫ ν = X.fromSpecStalk (genericPoint X) := by
  obtain ⟨e, hprojection, _⟩ := hν
  let U : X.Opens := (X.affineCover.map (genericPoint X)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.map (genericPoint X))
  letI : Nonempty U := ⟨⟨genericPoint X, X.affineCover.covers (genericPoint X)⟩⟩
  refine ⟨genericToChart X U ≫ (e U hU).inv ≫ (ν ⁻¹ᵁ U).ι, ?_⟩
  simp only [Category.assoc]
  rw [← hprojection U hU, Iso.inv_hom_id_assoc]
  exact genericToChart_to_original X U hU

end IsNormalizationInFunctionField

end KltDP.Geometry

#print axioms KltDP.Geometry.isNormalizationInFunctionField_id
#print axioms KltDP.Geometry.IsNormalizationInFunctionField.exists_generic_map

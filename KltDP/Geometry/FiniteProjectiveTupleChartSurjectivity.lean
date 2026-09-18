import KltDP.Geometry.FiniteProjectiveSectionTuple
import KltDP.Geometry.LinearSystemChartSurjectivity

/-!
# Actual surjective chart maps for the finite-source projective tuple

The original common-power generator theorem supplies all the sections and
all their literal equations. Their named tuple positions recover the
original chart generators under the original linear-system appLE. Hence
the selected original app maps are surjective. Only the original finite
map and the original closed projective embedding are assumed in the final
existence theorem; proper local-to-global closed immersion is separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.FiniteProjectiveSectionTuple

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance sectionModule {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Module Γ(X, U) (M.val.obj (op U)) := (M.val.obj (op U)).isModule

open FiniteProjectiveChartGenerators FiniteProjectivePowerGenerators
  InvertibleSheafSectionPowers InvertibleSectionNonvanishingOpen
  ProjectiveCoordinateSectionBasicOpen PowerSectionFunctionExtension

variable {k : Type u} [Field k] {n : ℕ} {Y Z : Scheme.{u}}
  (π : Z ⟶ Y) (i : Y ⟶ projectiveSpace k n) (q : ℕ)
  (r : Fin (n + 1) → ℕ)
  (t : ∀ j, Fin (r j) → (power (line π i) q).obj.sections) (hq : 0 < q)

include hq in
theorem denominator_nonvanishing (j : Fin (n + 1)) :
    nonvanishingOpen Z (power (line π i) q)
      (sections r π i q t (denominatorIndex r j)) = chartOpen π i j := by
  rw [sections_denominator,
    InvertibleSectionNonvanishingPowers.nonvanishingOpen_power _ _ hq,
    nonvanishing_coordinateSection]

/-- This is the original appLE on the literal original preimage chart. -/
def chartApp (j : Fin (n + 1)) :
    Γ(projectiveSpace k (Fintype.card (SectionIndex r)),
      standardOpen k (Fintype.card (SectionIndex r)) (denominatorIndex r j)) ⟶
        Γ(Z, chartOpen π i j) :=
  LinearSystemMorphism.appOnNonvanishing (power (line π i) q) (sections r π i q t)
    (structureMap π i) (sections_cover r π i q t hq) (denominatorIndex r j)
    (by rw [denominator_nonvanishing π i q r t hq])

/-- Every cleared generator section has its original generator as coordinate ratio. -/
theorem chartApp_coordinate (j : Fin (n + 1)) (a : Fin (r j))
    (b : Γ(Z, chartOpen π i j))
    (ht : sectionValue (power (line π i) q).obj (t j a) (chartOpen π i j) =
      b • sectionValue (power (line π i) q).obj
        (powerSection (line π i) (FiniteProjectivePowerGenerators.coordinateSection π i j) q)
          (chartOpen π i j)) :
    chartApp π i q r t hq j (ProjectiveCoordinateSectionBasicOpen.coordinateSection k
      (Fintype.card (SectionIndex r)) (denominatorIndex r j) (numeratorIndex r j a)) = b := by
  apply LinearSystemMorphism.appOnNonvanishing_coordinateSection_of_eq
  simpa only [sections_numerator, sections_denominator] using ht

variable [IsFinite π] [IsClosedImmersion i]

/-- Original polynomial chart generators force the original appLE to be surjective. -/
theorem chartApp_surjective (j : Fin (n + 1))
    (b : Fin (r j) → Γ(Z, chartOpen π i j))
    (hb : Function.Surjective (MvPolynomial.eval₂Hom (chartScalars π i j) b))
    (ht : ∀ a, sectionValue (power (line π i) q).obj (t j a) (chartOpen π i j) =
      b a • sectionValue (power (line π i) q).obj
        (powerSection (line π i) (FiniteProjectivePowerGenerators.coordinateSection π i j) q)
          (chartOpen π i j)) :
    Function.Surjective (chartApp π i q r t hq j).hom := by
  apply LinearSystemMorphism.appOnNonvanishing_surjective_of_generators
    (power (line π i) q) (sections r π i q t) (structureMap π i)
    (sections_cover r π i q t hq) (denominatorIndex r j) (chartOpen_isAffine π i j)
    (by rw [denominator_nonvanishing π i q r t hq]) (numeratorIndex r j) b hb
  intro a
  simpa only [sections_numerator, sections_denominator] using ht a

private theorem surjective_app_of_appLE {X T : Scheme.{u}} (g : X ⟶ T)
    (V : T.Opens) (U : X.Opens) (hU : U = g ⁻¹ᵁ V)
    (h : Function.Surjective (g.appLE V U hU.le).hom) :
    Function.Surjective (g.app V).hom := by
  subst U
  have hi : X.presheaf.map (𝟙 (op (g ⁻¹ᵁ V))) = 𝟙 _ := X.presheaf.map_id _
  simp only [Scheme.Hom.appLE, homOfLE_refl, op_id] at h
  rw [hi, Category.comp_id] at h
  exact h

/-- The actual original app, rather than a chosen replacement chart map,
is surjective on every selected standard chart. -/
theorem app_denominator_surjective (j : Fin (n + 1))
    (b : Fin (r j) → Γ(Z, chartOpen π i j))
    (hb : Function.Surjective (MvPolynomial.eval₂Hom (chartScalars π i j) b))
    (ht : ∀ a, sectionValue (power (line π i) q).obj (t j a) (chartOpen π i j) =
      b a • sectionValue (power (line π i) q).obj
        (powerSection (line π i) (FiniteProjectivePowerGenerators.coordinateSection π i j) q)
          (chartOpen π i j)) :
    Function.Surjective ((morphism r π i q t hq).app
      (standardOpen k (Fintype.card (SectionIndex r)) (denominatorIndex r j))).hom :=
  surjective_app_of_appLE _ _ _ (morphism_preimage_denominator r π i q t hq j).symm
    (chartApp_surjective π i q r t hq j b hb ht)

/-- Every original finite map to an original closed projective subscheme
admits this actual covering tuple with surjective selected original apps.
All denominator-clearing and generator witnesses are derived internally. -/
theorem exists_tuple_with_surjective_chartMaps :
    ∃ (q : ℕ) (hq : 0 < q) (r : Fin (n + 1) → ℕ)
      (t : ∀ j, Fin (r j) → (power (line π i) q).obj.sections),
      ∀ j, Function.Surjective ((morphism r π i q t hq).app
        (standardOpen k (Fintype.card (SectionIndex r)) (denominatorIndex r j))).hom := by
  obtain ⟨q, hq, r, b, t, hb, ht⟩ := exists_common_power_generators π i
  exact ⟨q, hq, r, t, fun j => app_denominator_surjective π i q r t hq j (b j) (hb j) (ht j)⟩

end KltDP.Geometry.FiniteProjectiveSectionTuple

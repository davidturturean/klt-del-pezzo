import KltDP.Geometry.FiniteProjectivePowerGenerators
import KltDP.Geometry.FiniteSectionTuples
import KltDP.Geometry.LinearSystemNonvanishingPreimage

/-!
# The original common-power sections as one projective tuple

Enumerate every original denominator power and every denominator-cleared
generator section, adjoining a zero section as in `FiniteSectionTuples`.
Their named positions retain the original sections exactly. The denominator
positions already cover the source and have the original coordinate-chart
preimages under the original linear-system morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.FiniteProjectiveSectionTuple

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open FiniteProjectiveChartGenerators FiniteProjectivePowerGenerators
  InvertibleSheafSectionPowers InvertibleSectionNonvanishingOpen
  ProjectiveCoordinateSectionBasicOpen

variable {n : ℕ} (r : Fin (n + 1) → ℕ)

/-- One index for each original denominator and each original chart generator. -/
abbrev SectionIndex := Fin (n + 1) ⊕ ((j : Fin (n + 1)) × Fin (r j))

/-- The original finite family, with the same additional zero used by the
existing finite-section tuple construction. -/
def indexEquiv : Option (SectionIndex r) ≃ Fin (Fintype.card (SectionIndex r) + 1) :=
  (Fintype.equivFin (Option (SectionIndex r))).trans (finCongr Fintype.card_option)

def denominatorIndex (j : Fin (n + 1)) : Fin (Fintype.card (SectionIndex r) + 1) :=
  indexEquiv r (some (.inl j))

def numeratorIndex (j : Fin (n + 1)) (a : Fin (r j)) :
    Fin (Fintype.card (SectionIndex r) + 1) :=
  indexEquiv r (some (.inr ⟨j, a⟩))

variable {k : Type u} [Field k] {Y Z : Scheme.{u}}
  (π : Z ⟶ Y) (i : Y ⟶ projectiveSpace k n) (q : ℕ)
  (t : ∀ j, Fin (r j) → (power (line π i) q).obj.sections)

/-- The tuple consists of the actual original sections, without frame choices. -/
def sections : Fin (Fintype.card (SectionIndex r) + 1) →
    (power (line π i) q).obj.sections := fun a =>
  match (indexEquiv r).symm a with
  | none => (power (line π i) q).obj.unitHomEquiv 0
  | some (.inl j) => powerSection (line π i) (FiniteProjectivePowerGenerators.coordinateSection π i j) q
  | some (.inr ⟨j, a⟩) => t j a

@[simp] theorem sections_denominator (j : Fin (n + 1)) :
    sections r π i q t (denominatorIndex r j) =
      powerSection (line π i) (FiniteProjectivePowerGenerators.coordinateSection π i j) q := by
  simp only [sections, denominatorIndex, Equiv.symm_apply_apply]

@[simp] theorem sections_numerator (j : Fin (n + 1)) (a : Fin (r j)) :
    sections r π i q t (numeratorIndex r j a) = t j a := by
  simp only [sections, numeratorIndex, Equiv.symm_apply_apply]

/-- The original denominator positions alone prove that the entire tuple covers. -/
theorem sections_cover (hq : 0 < q) :
    (⨆ a, nonvanishingOpen Z (power (line π i) q) (sections r π i q t a)) = ⊤ := by
  apply top_unique
  rw [← powerCoordinateSections_cover π i hq]
  exact iSup_le fun j => by
    simpa only [sections_denominator] using
      (le_iSup (fun a => nonvanishingOpen Z (power (line π i) q)
        (sections r π i q t a)) (denominatorIndex r j))

/-- The original glued linear-system morphism of this exact tuple. -/
def morphism (hq : 0 < q) : Z ⟶ projectiveSpace k (Fintype.card (SectionIndex r)) :=
  LinearSystemMorphism.morphism (power (line π i) q) (sections r π i q t)
    (structureMap π i) (sections_cover r π i q t hq)

theorem morphism_structure (hq : 0 < q) :
    morphism r π i q t hq ≫ projectiveSpaceToSpec k (Fintype.card (SectionIndex r)) =
      structureMap π i :=
  LinearSystemMorphism.morphism_structure _ _ _ _

/-- The selected target-chart preimages are the original finite preimage charts. -/
theorem morphism_preimage_denominator (hq : 0 < q) (j : Fin (n + 1)) :
    morphism r π i q t hq ⁻¹ᵁ
      standardOpen k (Fintype.card (SectionIndex r)) (denominatorIndex r j) =
      chartOpen π i j := by
  have hstd : (ProjectiveChart.coordinateChartMorphism k
      (Fintype.card (SectionIndex r)) (denominatorIndex r j)).opensRange =
      standardOpen k (Fintype.card (SectionIndex r)) (denominatorIndex r j) :=
    ProjectiveChart.coordinateChartMorphism_opensRange k _ _
  rw [morphism, ← hstd,
    LinearSystemMorphism.morphism_preimage_coordinateChart, sections_denominator,
    InvertibleSectionNonvanishingPowers.nonvanishingOpen_power _ _ hq,
    nonvanishing_coordinateSection]

end KltDP.Geometry.FiniteProjectiveSectionTuple

import KltDP.Geometry.SectionLinearCombinations
import KltDP.Geometry.CompleteLinearSystemSectionTuple

/-!
# Exact subsystem expansion in the original complete linear system

Every compatible section, including each image under an actual sheaf map,
is the finite linear combination given by the original H0 basis. These
coefficients retain the original base-field action and compute the same
linear forms in every original invertible frame.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u v

namespace KltDP.Geometry.CompleteLinearSystemExpansion

attribute [local instance] Types.instFunLike Types.instConcreteCategory
open ModuleCohomology CompleteLinearSystemSections SectionLinearCombinations

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (L : InvertibleSheaf X)
  [IsProper f] (hpos : 0 < dimension f L)

/-- The original base-field coordinates of any compatible section in the whole H0 basis. -/
def coefficients (s : L.obj.sections) : Fin ((dimension f L - 1) + 1) → k := by
  letI := baseSectionsModule f L.obj
  exact fun i => (positiveTopSectionBasis f L hpos).repr
    (s.val (op ⊤) : ModuleCohomology.sections L.obj) i

/-- Reconstruct the exact original compatible family, not just its cohomology class. -/
theorem combination_coefficients (s : L.obj.sections) :
    combination f L.obj (positiveBasisSections f L hpos) (coefficients f L hpos s) = s := by
  letI := baseSectionsModule f L.obj
  apply (schemeModuleSectionsEquivTop L.obj).injective
  change (combination f L.obj (positiveBasisSections f L hpos)
    (coefficients f L hpos s)).val (op ⊤) = s.val (op ⊤)
  rw [combination_top]
  exact positiveBasisSections_sum_repr f L hpos (s.val (op ⊤))

/-- Every frame coefficient is the exact corresponding linear form in the whole basis. -/
theorem coefficient_eq_sum (s : L.obj.sections) (i : L.localTrivializations.I)
    {U : X.Opens} (hUi : U ≤ L.localTrivializations.X i) :
    LinearSystemMorphism.coefficient L s i hUi =
      ∑ j, scalarOnOpen f U (coefficients f L hpos s j) *
        LinearSystemMorphism.coefficient L (positiveBasisSections f L hpos j) i hUi := by
  exact (congrArg (fun t => LinearSystemMorphism.coefficient L t i hUi)
    (combination_coefficients f L hpos s).symm).trans
      (coefficient_combination f L (positiveBasisSections f L hpos)
        (coefficients f L hpos s) i hUi)

variable (H : X.Modules) (g : H ⟶ L.obj) {I : Type v} (t : I → H.sections)

/-- The original coefficient matrix of the image of any actual subsystem. -/
def mappedCoefficients (i : I) : Fin ((dimension f L - 1) + 1) → k :=
  coefficients f L hpos (_root_.SheafOfModules.sectionsMap g (t i))

/-- Each actual mapped section is exactly its row of the original coefficient matrix. -/
theorem combination_mappedCoefficients (i : I) :
    combination f L.obj (positiveBasisSections f L hpos)
      (mappedCoefficients f L hpos H g t i) =
        _root_.SheafOfModules.sectionsMap g (t i) :=
  combination_coefficients f L hpos (_root_.SheafOfModules.sectionsMap g (t i))

end KltDP.Geometry.CompleteLinearSystemExpansion

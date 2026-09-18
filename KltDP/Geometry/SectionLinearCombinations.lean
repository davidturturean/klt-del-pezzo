import KltDP.Geometry.BaseFieldCohomology
import KltDP.Geometry.SchemeModulePullbackUnit
import KltDP.Geometry.LinearSystemNormalizedCoordinates

/-!
# Actual finite linear combinations of compatible global sections

Use the original field action on top sections, then take their actual
compatible restriction family. Restriction and every original frame
compute the same finite sum, with scalars restricted from the given
structure morphism. These are the linear forms used to recover a
subsystem from a complete linear system.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u v

namespace KltDP.Geometry.SectionLinearCombinations

attribute [local instance] Types.instFunLike Types.instConcreteCategory
open ModuleCohomology TransitionUnitGluing TransitionUnitExtraction

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))
  {I : Type v} [Fintype I]

/-- The finite combination in the original base-field section module. -/
def combination (M : X.Modules) (s : I → M.sections) (a : I → k) : M.sections := by
  letI := baseSectionsModule f M
  exact (schemeModuleSectionsEquivTop M).symm
    (∑ i, (let vi : ModuleCohomology.sections M := (s i).val (op ⊤);
      a i • vi))

/-- Its original top value is exactly the chosen finite linear combination. -/
theorem combination_top (M : X.Modules) (s : I → M.sections) (a : I → k) :
    letI := baseSectionsModule f M
    (combination f M s a).val (op ⊤) =
      (∑ i, (let vi : ModuleCohomology.sections M := (s i).val (op ⊤);
        a i • vi)) := by
  letI := baseSectionsModule f M
  exact (schemeModuleSectionsEquivTop M).apply_symm_apply _

/-- The original scalar restricted to the indicated original open. -/
def scalarOnOpen (U : X.Opens) (r : k) : Γ(X, U) :=
  res X (le_top : U ≤ ⊤) (baseFieldToGlobalSections f r)

/-- Restriction computes the same finite combination of the original section values. -/
theorem combination_val (M : X.Modules) (s : I → M.sections) (a : I → k)
    (U : X.Opens) :
    (combination f M s a).val (op U) =
      ∑ i, (let vi : M.val.obj (op U) := (s i).val (op U);
        scalarOnOpen f U (a i) • vi) := by
  classical
  letI := baseSectionsModule f M
  change M.val.map (homOfLE (le_top : U ≤ ⊤)).op
    (∑ i, (let vi : M.val.obj (op ⊤) := (s i).val (op ⊤);
      baseFieldToGlobalSections f (a i) • vi)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(M.val.map (homOfLE (le_top : U ≤ ⊤)).op).hom.map_smulₛₗ]
  change scalarOnOpen f U (a i) •
    M.val.map (homOfLE (le_top : U ≤ ⊤)).op ((s i).val (op ⊤)) = _
  exact congrArg (fun v : M.val.obj (op U) => scalarOnOpen f U (a i) • v)
    ((s i).property (homOfLE (le_top : U ≤ ⊤)).op)

/-- Every actual invertible frame computes those same linear forms. -/
theorem coefficient_combination (L : InvertibleSheaf X) (s : I → L.obj.sections)
    (a : I → k) (i : L.localTrivializations.I) {U : X.Opens}
    (hUi : U ≤ L.localTrivializations.X i) :
    LinearSystemMorphism.coefficient L (combination f L.obj s a) i hUi =
      ∑ j, scalarOnOpen f U (a j) *
        LinearSystemMorphism.coefficient L (s j) i hUi := by
  classical
  unfold LinearSystemMorphism.coefficient
  rw [combination_val, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact (chartEquiv X L.obj L.localTrivializations i hUi).map_smul _ _

end KltDP.Geometry.SectionLinearCombinations

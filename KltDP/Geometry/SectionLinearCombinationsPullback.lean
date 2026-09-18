import KltDP.Geometry.SectionLinearCombinations
import KltDP.Geometry.InvertibleSheafSectionPowersPullback
import KltDP.Geometry.SchemeModulePushforwardScalars

/-!
# Original linear combinations commute with actual section transport

The adjunction-unit section map is semilinear for the original scheme
section map. Restricting the original base-field scalar commutes with
that map, so the resulting pullback family is the combination for the
literal composite structure morphism. Ordinary module-sheaf morphisms
preserve the same combinations through their actual linear app maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u v

namespace KltDP.Geometry.SectionLinearCombinations

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) {I : Type v} [Fintype I]

/-- The original scalar on an open pulls back to the scalar for the
literal composite structure morphism, with no compatibility premise. -/
theorem app_scalarOnOpen (h : Y ⟶ X) (U : X.Opens) (r : k) :
    h.app U (scalarOnOpen f U r) = scalarOnOpen (h ≫ f) (h ⁻¹ᵁ U) r := by
  change h.app U
    (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (baseFieldToGlobalSections f r)) =
      Y.presheaf.map (homOfLE (le_top : h ⁻¹ᵁ U ≤ ⊤)).op
        (baseFieldToGlobalSections (h ≫ f) r)
  exact ModuleCohomology.app_restrictGlobal h (baseFieldToGlobalSections f r) U

/-- Actual pullback preserves the finite combination over the original
field, using the exact original composite structure map on the source. -/
theorem pullbackSection_combination (h : Y ⟶ X) (M : X.Modules)
    (s : I → M.sections) (a : I → k) :
    InvertibleSheafSectionPowersPullback.pullbackSection h M (combination f M s a) =
      combination (h ≫ f) ((schemeModulePullback h).obj M)
        (fun i => InvertibleSheafSectionPowersPullback.pullbackSection h M (s i)) a := by
  classical
  apply (schemeModuleSectionsEquivTop ((schemeModulePullback h).obj M)).injective
  change
    (InvertibleSheafSectionPowersPullback.pullbackSection h M
      (combination f M s a)).val (op (h ⁻¹ᵁ (⊤ : X.Opens))) =
      (combination (h ≫ f) ((schemeModulePullback h).obj M)
        (fun i => InvertibleSheafSectionPowersPullback.pullbackSection h M (s i)) a).val
          (op (h ⁻¹ᵁ (⊤ : X.Opens)))
  rw [InvertibleSheafSectionPowersPullback.pullbackSection_val,
    combination_val, combination_val]
  change ((schemeModulePullbackPushforwardAdjunction h).unit.app M).val.app (op ⊤)
    (∑ i, (let vi : M.val.obj (op ⊤) := (s i).val (op ⊤);
      scalarOnOpen f ⊤ (a i) • vi)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change RationalTreePicard.pulledSection h M ⊤
    (let vi : M.val.obj (op ⊤) := (s i).val (op ⊤);
      scalarOnOpen f ⊤ (a i) • vi) =
      (let wi : ((schemeModulePullback h).obj M).val.obj (op (h ⁻¹ᵁ ⊤)) :=
        (InvertibleSheafSectionPowersPullback.pullbackSection h M (s i)).val (op (h ⁻¹ᵁ ⊤));
        scalarOnOpen (h ≫ f) (h ⁻¹ᵁ ⊤) (a i) • wi)
  rw [RationalTreePicard.pulledSection_smul, app_scalarOnOpen,
    InvertibleSheafSectionPowersPullback.pullbackSection_val]

/-- Every actual morphism of original module sheaves preserves these
combinations through its original linear app map. -/
theorem sectionsMap_combination {M N : X.Modules} (φ : M ⟶ N)
    (s : I → M.sections) (a : I → k) :
    _root_.SheafOfModules.sectionsMap φ (combination f M s a) =
      combination f N (fun i => _root_.SheafOfModules.sectionsMap φ (s i)) a := by
  classical
  apply (schemeModuleSectionsEquivTop N).injective
  change φ.val.app (op ⊤) ((combination f M s a).val (op ⊤)) =
    (combination f N (fun i => _root_.SheafOfModules.sectionsMap φ (s i)) a).val (op ⊤)
  rw [combination_val, combination_val, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (φ.val.app (op ⊤)).hom.map_smul (scalarOnOpen f ⊤ (a i)) ((s i).val (op ⊤))

end KltDP.Geometry.SectionLinearCombinations

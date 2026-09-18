import KltDP.Geometry.InvertibleNonzeroSections
import KltDP.Geometry.CompleteLinearSystemSectionTuple
import KltDP.Geometry.InvertibleSectionNonvanishingOpen

/-!
# A nonzero map from a generated line bundle gives positive complete-system dimension

A covering tuple has a nonzero original top section. The already proved
injectivity of a nonzero line-bundle map preserves that section, giving
positive dimension of the actual target H0 on a proper integral scheme.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u

namespace KltDP.Geometry.SubsystemPositiveDimension

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSectionNonvanishingOpen TransitionUnitExtraction ModuleCohomology

/-- A section with zero original top value has empty intrinsic nonvanishing open. -/
theorem nonvanishingOpen_eq_bot_of_top_eq_zero (X : Scheme.{u})
    (L : InvertibleSheaf X) (s : L.obj.sections) (hs : s.val (op ⊤) = 0) :
    nonvanishingOpen X L s = ⊥ := by
  change (⨆ i, X.basicOpen
    (chartCoefficient X L.obj L.localTrivializations s i)) = ⊥
  apply iSup_eq_bot.mpr
  intro i
  let V := L.localTrivializations.X i
  have hres : L.obj.val.map (homOfLE (show V ≤ ⊤ from le_top)).op
      (s.val (op ⊤)) = s.val (op V) :=
    s.property (homOfLE (show V ≤ ⊤ from le_top)).op
  have hv : s.val (op V) = 0 := hres.symm.trans (by
    rw [hs]
    exact map_zero (L.obj.val.map (homOfLE (show V ≤ ⊤ from le_top)).op).hom)
  change X.basicOpen
    (chartEquiv X L.obj L.localTrivializations i le_rfl (s.val (op V))) = ⊥
  rw [hv, map_zero, Scheme.basicOpen_zero]

/-- A tuple covering a nonempty scheme contains an actual nonzero top section. -/
theorem exists_top_ne_zero_of_cover {X : Scheme.{u}} [Nonempty X]
    (H : InvertibleSheaf X) {n : ℕ} (s : Fin (n + 1) → H.obj.sections)
    (hcover : (⨆ i, nonvanishingOpen X H (s i)) = ⊤) :
    ∃ i, (s i).val (op ⊤) ≠ 0 := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hx : x ∈ (⨆ i, nonvanishingOpen X H (s i)) := by
    rw [hcover]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  refine ⟨i, fun hz => ?_⟩
  rw [nonvanishingOpen_eq_bot_of_top_eq_zero X H (s i) hz] at hi
  exact hi

/-- The target of a nonzero original map from a generated line bundle has positive H0 dimension. -/
theorem dimension_pos_of_nonzero_map {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (H L : InvertibleSheaf X) {n : ℕ} (s : Fin (n + 1) → H.obj.sections)
    (hcover : (⨆ i, nonvanishingOpen X H (s i)) = ⊤)
    (g : H.obj ⟶ L.obj) (hg : g ≠ 0) :
    0 < CompleteLinearSystemSections.dimension f L := by
  obtain ⟨i, hi⟩ := exists_top_ne_zero_of_cover H s hcover
  apply CompleteLinearSystemSections.dimension_pos_of_nonzero_top_section f L
    (_root_.SheafOfModules.sectionsMap g (s i))
  intro hz
  apply hi
  apply InvertibleNonzeroSections.globalSections_injective X H L g hg
  change globalSectionsLinearMap g ((s i).val (op ⊤)) = globalSectionsLinearMap g 0
  exact hz.trans (map_zero (globalSectionsLinearMap g)).symm

end KltDP.Geometry.SubsystemPositiveDimension

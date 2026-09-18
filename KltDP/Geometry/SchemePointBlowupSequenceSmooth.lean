import KltDP.Geometry.SchemePointBlowupSourceRegular
import KltDP.Geometry.SchemePointBlowupSequenceProper
import KltDP.Geometry.RegularProperSurface

/-!
An actual finite point-blowup sequence over the original smooth surface
has integral, smooth, regular, two-dimensional source. Every intermediate
scheme is the original one; its surface package is obtained only after
these properties have been proved. Projectivity of that regular proper
surface uses the same isolated Hartshorne dependency as `regularProperSurface`.
No intermediate normality, projectivity, dimension, or smoothness is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.SchemePointBlowup

variable {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    {S : Scheme.{u}} {f : S ⟶ X.toScheme} {U : Set X.toScheme}

/-- The original finite sequence proves all source geometry needed for
the next actual blowup, preserving the original scheme and field map. -/
theorem SequenceAway.source_geometry (h : SequenceAway X.toScheme U S f) :
    IsIntegral S ∧ IsSmooth (f ≫ X.structureMorphism) ∧
      (∀ y : S, RegularPoint S y) ∧ topologicalKrullDim S = 2 := by
  letI : IsProper X.structureMorphism := X.projective.isProper
  induction h with
  | of_isIso f hf =>
      letI := hf
      letI : Nonempty _ := ⟨(inv f).base (genericPoint X.toScheme)⟩
      letI : IsIntegral _ := isIntegral_of_isOpenImmersion f
      letI : IsSmooth (f ≫ X.structureMorphism) := inferInstance
      have hdim : topologicalKrullDim _ = 2 :=
        (IsHomeomorph.topologicalKrullDim_eq
          (asIso f).schemeIsoToHomeo (asIso f).schemeIsoToHomeo.isHomeomorph).trans X.dimension_two
      exact ⟨inferInstance, inferInstance,
        SmoothFieldRegularPoints.regularPoints_of_isSmooth_of_dimension_le_two
          (f ≫ X.structureMorphism) hdim.le, hdim⟩
  | step b g x hb hx hg ih =>
      letI := ih.1
      letI : IsProper g := hg.isProper_over_noetherian_base X.structureMorphism
      let X' := regularProperSurface _ (g ≫ X.structureMorphism) ih.2.2.1 ih.2.2.2
      letI : IsSmooth X'.structureMorphism := ih.2.1
      have hsmooth : IsSmooth ((b ≫ g) ≫ X.structureMorphism) := by
        rw [Category.assoc]
        exact hb.isSmooth_comp_structure X'
      exact ⟨hb.source_isIntegral_of_surface X', hsmooth,
        hb.source_regular X', hb.source_dimension_two X'⟩

/-- Integrality follows for every original sequence, without requiring
a nonempty set of points avoided by its centres. -/
theorem SequenceAway.source_isIntegral_of_surface (h : SequenceAway X.toScheme U S f) :
    IsIntegral S :=
  (h.source_geometry X).1

/-- The source's original composite field structure is smooth. -/
theorem SequenceAway.source_isSmooth (h : SequenceAway X.toScheme U S f) :
    IsSmooth (f ≫ X.structureMorphism) :=
  (h.source_geometry X).2.1

/-- Every stalk of the original final source is regular. -/
theorem SequenceAway.source_regular (h : SequenceAway X.toScheme U S f) :
    ∀ y : S, RegularPoint S y :=
  (h.source_geometry X).2.2.1

/-- The dimension of the original final source is exactly two. -/
theorem SequenceAway.source_dimension_two (h : SequenceAway X.toScheme U S f) :
    topologicalKrullDim S = 2 :=
  (h.source_geometry X).2.2.2

/-- The original final scheme and its exact composite structure map,
equipped with the regular proper surface properties derived from the sequence. -/
def SequenceAway.sourceSurface (h : SequenceAway X.toScheme U S f) :
    NormalProjectiveSurface k := by
  letI : IsIntegral S := h.source_isIntegral_of_surface X
  letI : IsProper X.structureMorphism := X.projective.isProper
  letI : IsProper f := h.isProper_over_noetherian_base X.structureMorphism
  exact regularProperSurface S (f ≫ X.structureMorphism)
    (h.source_regular X) (h.source_dimension_two X)

@[simp] theorem SequenceAway.sourceSurface_toScheme
    (h : SequenceAway X.toScheme U S f) : (h.sourceSurface X).toScheme = S := rfl

@[simp] theorem SequenceAway.sourceSurface_structureMorphism
    (h : SequenceAway X.toScheme U S f) :
    (h.sourceSurface X).structureMorphism = f ≫ X.structureMorphism := rfl

end KltDP.Geometry.SchemePointBlowup

import KltDP.Geometry.BirationalComposition
import KltDP.Geometry.ImmersionBirational

/-!
# Birationality and the original nonempty open restrictions

The original open inclusions are birational. Their composition formulas
transfer birationality between a map and its original source restriction.
For the original target restriction, the given generic-point preservation
makes the preimage nonempty, and the actual restriction square derives
generic-point preservation of the restricted map. The same square and
the two original open inclusions then transfer birationality in both
directions, without a quasi-compactness assumption.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.BirationalRestriction

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) [GenericPointPreserving f]

/-- Restricting the original source to a nonempty open preserves and reflects birationality. -/
theorem isBirationalScheme_open_precompose_iff (U : X.Opens) [Nonempty U] :
    IsBirationalScheme (U.ι ≫ f) ↔ IsBirationalScheme f := by
  letI : GenericPointPreserving U.ι := ⟨genericPoint_eq_of_isOpenImmersion U.ι⟩
  constructor
  · exact BirationalComposition.isBirationalScheme_right_of_comp U.ι f
  · intro hf
    exact (BirationalComposition.isBirationalScheme_comp_iff U.ι f).mpr
      ⟨ImmersionBirational.isBirationalScheme_of_isOpenImmersion U.ι, hf⟩

/-- The actual target restriction preserves the original generic point; this is derived from
the original restriction square and the original map's generic-point preservation. -/
theorem restriction_genericPointPreserving (V : Y.Opens) [Nonempty V] :
    GenericPointPreserving (f ∣_ V) := by
  constructor
  apply V.ι.isOpenEmbedding.injective
  rw [genericPoint_eq_of_isOpenImmersion V.ι]
  have hcomp : V.ι.base ((f ∣_ V).base (genericPoint (f ⁻¹ᵁ V).toScheme)) =
      f.base ((f ⁻¹ᵁ V).ι.base (genericPoint (f ⁻¹ᵁ V).toScheme)) := by
    rw [← Scheme.comp_base_apply, ← Scheme.comp_base_apply, morphismRestrict_ι]
  rw [genericPoint_eq_of_isOpenImmersion (f ⁻¹ᵁ V).ι,
    GenericPointPreserving.base_genericPoint (π := f)] at hcomp
  exact hcomp

/-- Restricting the original target to a nonempty open preserves and reflects birationality. -/
theorem isBirationalScheme_restrict_iff (V : Y.Opens) [Nonempty V] :
    IsBirationalScheme (f ∣_ V) ↔ IsBirationalScheme f := by
  letI := restriction_genericPointPreserving f V
  letI : GenericPointPreserving V.ι := ⟨genericPoint_eq_of_isOpenImmersion V.ι⟩
  calc
    IsBirationalScheme (f ∣_ V) ↔ IsBirationalScheme ((f ∣_ V) ≫ V.ι) := by
      constructor
      · intro hf
        exact (BirationalComposition.isBirationalScheme_comp_iff (f ∣_ V) V.ι).mpr
          ⟨hf, ImmersionBirational.isBirationalScheme_of_isOpenImmersion V.ι⟩
      · exact BirationalComposition.isBirationalScheme_left_of_comp (f ∣_ V) V.ι
    _ ↔ IsBirationalScheme ((f ⁻¹ᵁ V).ι ≫ f) := by rw [morphismRestrict_ι]
    _ ↔ IsBirationalScheme f := isBirationalScheme_open_precompose_iff f (f ⁻¹ᵁ V)

end KltDP.Geometry.BirationalRestriction

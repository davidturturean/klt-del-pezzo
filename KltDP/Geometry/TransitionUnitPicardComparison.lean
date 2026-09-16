import KltDP.Geometry.TransitionUnitPicard
import KltDP.Geometry.TransitionUnitRefinement
import KltDP.Geometry.TransitionUnitRecovery

/-!
# Refinement and recovery of actual transition-unit Picard classes

The constructed refinement isomorphism identifies the Picard classes of
an original cocycle and its restriction to a subordinate open cover.
The constructed recovery isomorphism identifies the class of the cocycle
extracted from an invertible sheaf with that sheaf's original Picard class.

Both comparisons take place in the scheme's actual tensor Picard group.
No quotient by refinements or tensor-compatibility assertion is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.TransitionUnitGluing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u})

/-- Restriction to a subordinate open cover preserves the actual Picard class.
The original covering property is derived from the covering refinement. -/
theorem picardClass_eq_of_refinement {J I : Type u}
    (U : J → X.Opens) (g : ∀ j j' : J, Γ(X, U j ⊓ U j')ˣ)
    (hg : IsCocycle X U g) (V : I → X.Opens) (σ : I → J)
    (hσ : ∀ i : I, V i ≤ U (σ i)) (hV : (⨆ i, V i) = ⊤) :
    picardClass X U g hg (cover_of_refinement X U V σ hσ hV) =
      picardClass X V (refinedUnits X U g V σ hσ)
        (refinedUnits_isCocycle X U g V σ hσ hg) hV := by
  letI := Scheme.Modules.monoidalCategory X
  apply Units.ext
  rw [picardClass_val, picardClass_val]
  exact Quotient.sound ⟨refinementIso X U g V σ hσ hg hV⟩

open TransitionUnitExtraction

/-- The actual cocycle extracted from an invertible sheaf represents its original class. -/
theorem picardClass_eq_toPic_of_extraction (L : InvertibleSheaf X) :
    picardClass X L.localTrivializations.X (invertibleSheafUnits X L)
      (invertibleSheafUnits_isCocycle X L) (invertibleSheafUnits_cover X L) =
        L.toPic := by
  letI := Scheme.Modules.monoidalCategory X
  apply Units.ext
  rw [picardClass_val, InvertibleSheaf.toPic_val]
  exact Quotient.sound ⟨(invertibleSheafRecoveryIso X L).symm⟩

end KltDP.Geometry.TransitionUnitGluing

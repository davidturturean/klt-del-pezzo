import KltDP.Geometry.TwoOpenUnitGlobalSections
import KltDP.Geometry.TransitionUnitGlobalSectionNonvanishing

/-! # Nonvanishing of original two-chart global sections -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.TwoOpenUnitGlobalSections

open TransitionUnitGluing RationalTreePicard InvertibleSectionNonvanishingOpen

variable (X : Scheme.{u}) (U : ULift.{u} (Fin 2) → X.Opens)
  (a : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)ˣ) (hU : (⨆ i, U i) = ⊤)
  (r₀ : Γ(X, U ⟨0⟩)) (r₁ : Γ(X, U ⟨1⟩))
  (h : res X (inf_le_left : U ⟨0⟩ ⊓ U ⟨1⟩ ≤ U ⟨0⟩) r₀ =
    (a : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)) *
      res X (inf_le_right : U ⟨0⟩ ⊓ U ⟨1⟩ ≤ U ⟨1⟩) r₁)

/-- The intrinsic nonvanishing open of the actual glued section is the
union of the original basic opens of its two coordinates. -/
theorem nonvanishingOpen_globalSection :
    nonvanishingOpen X
        (invertibleSheaf X U (twoOpenUnits X U a) (twoOpenUnits_isCocycle X U a) hU)
        (globalSection X U a r₀ r₁ h) = X.basicOpen r₀ ⊔ X.basicOpen r₁ := by
  calc
    _ = ⨆ i, X.basicOpen (coordinates X U r₀ r₁ i) :=
      nonvanishingOpen_globalSectionOfCoordinates X U (twoOpenUnits X U a)
        (twoOpenUnits_isCocycle X U a) hU (coordinates X U r₀ r₁)
        (coordinates_compatible X U a r₀ r₁ h)
    _ = X.basicOpen r₀ ⊔ X.basicOpen r₁ := by
      apply le_antisymm
      · apply iSup_le
        rintro ⟨i⟩
        fin_cases i
        · exact le_sup_left
        · exact le_sup_right
      · apply sup_le
        · exact le_iSup_of_le ⟨0⟩ le_rfl
        · exact le_iSup_of_le ⟨1⟩ le_rfl

end KltDP.Geometry.TwoOpenUnitGlobalSections

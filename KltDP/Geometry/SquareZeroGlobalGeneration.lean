import KltDP.Geometry.SquareZeroSectionCover
import KltDP.Geometry.SquareZeroIndependentSections
import KltDP.Geometry.FiniteGeneratingSections

/-! The original square-zero nef divisor on the original rational
surface is globally generated. Its two original sections, divisor
supports and nonvanishing cover are constructed inside the proof. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.NormalProjectiveSurface
open InvertibleSectionNonvanishingOpen

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
  (K : CartierDivisor X.toScheme)
  (eK : cartierDivisorModule X.toScheme K ≅
    relativeDifferentialExterior X.structureMorphism 2)
  (hrational : Scheme.BirationalOver X.structureMorphism
    (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))

local instance squareZeroGenerationIntegral : IsIntegral X.toScheme := X.integral

include hX eK hrational in
/-- Two constructed original sections generate the actual line sheaf.
No section, base-point-free pencil, or free epimorphism is an input. -/
theorem globallyGenerated_of_nef_squareZero (F : CartierDivisor X.toScheme)
    (hF : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme F))
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2) :
    Positivity.IsGloballyGenerated (cartierDivisorModule X.toScheme F) := by
  obtain ⟨s, hs⟩ := X.exists_two_independent_sections_of_nef_squareZero hX K eK hrational
    F hF hFF hKF
  let L := cartierDivisorInvertibleSheaf X.toScheme F
  let t : ULift.{u} (Fin 2) → L.obj.sections := fun j =>
    schemeModuleSectionOfTop (cartierDivisorModule X.toScheme F) (s j.down)
  have hcover : (⨆ j, nonvanishingOpen X.toScheme L (t j)) = ⊤ := by
    simpa only [t, iSup_ulift] using
      X.independent_sections_cover_of_nef_squareZero hX K eK F hF hFF hKF s hs
  exact ⟨ULift.{u} (Fin 2), L.obj.freeHomEquiv.symm t,
    FiniteGeneratingSections.epi_of_nonvanishing_cover L t hcover⟩

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.globallyGenerated_of_nef_squareZero
#print axioms KltDP.Geometry.NormalProjectiveSurface.globallyGenerated_of_nef_squareZero

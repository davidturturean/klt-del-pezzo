import KltDP.Geometry.RegularSchemeSmoothConditional
import KltDP.Geometry.SmoothSurfaceRelativeDimension
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Conditional relative smoothness of the original regular surface

The source hypotheses are repeated in full. The algebraically closed
field, actual reducedness and finite-type instances are supplied by the
original normal projective surface. The already proved relative-dimension
adapter applies to that very same structure morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

/-- Original regular normal projective surfaces are smooth of relative
dimension two, conditional on the two explicit generic source assertions. -/
theorem isSmoothOfRelativeDimension_two_of_regularPoints_of_native_sources
    (h0B8X : ∀ (k₀ : Type u) [Field k₀] [PerfectField k₀]
      (X₀ : Scheme.{u}) [AlgebraicGeometry.IsReduced X₀]
      (f₀ : X₀ ⟶ Spec (CommRingCat.of k₀)) [LocallyOfFiniteType f₀],
      let L : Set X₀ := {x | AffineSmoothLocalizationTransport.algebraSmoothAt f₀ x}
      let G : Set X₀ := {x | RegularLocalByGenerators (X₀.presheaf.stalk x)}
      L = G ∧ IsOpen L ∧ Dense L)
    (h00TA : ∀ (R A : Type u) [CommRing R] [CommRing A] (φ : R →+* A),
      (letI : Algebra R A := φ.toAlgebra
       Algebra.Smooth R A) →
      ∃ T : Set A, Ideal.span T = ⊤ ∧ ∀ g ∈ T,
        RingHom.IsStandardSmooth ((algebraMap A (Localization.Away g)).comp φ))
    {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
    (hreg : ∀ x, RegularPoint X.toScheme x) :
    IsSmoothOfRelativeDimension 2 X.structureMorphism := by
  letI : LocallyOfFiniteType X.structureMorphism := X.projective.locallyOfFiniteType
  letI : IsSmooth X.structureMorphism :=
    RegularSchemeSmoothConditional.isSmooth_of_regularPoints
      h0B8X h00TA X.structureMorphism hreg
  exact X.isSmoothOfRelativeDimension_two

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.isSmoothOfRelativeDimension_two_of_regularPoints_of_native_sources
#print axioms KltDP.Geometry.NormalProjectiveSurface.isSmoothOfRelativeDimension_two_of_regularPoints_of_native_sources


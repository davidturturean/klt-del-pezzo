import KltDP.Geometry.RationalComponentPrimeCurves

/-!
# The original rational-component prime images are distinct

The carrier of each actual original prime image is the image of the
original irreducible component under the unchanged closed immersion.
Its injectivity on points therefore retains distinct component sets.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.RationalComponentPrimeCurves

open NormalProjectiveSurface RationalTreePicard

variable {k : Type u} [Field k] (S : NormalProjectiveSurface k)
    {C : Scheme.{u}} [NoetherianSpace C]
    (f : C ⟶ S.toScheme) [IsClosedImmersion f]
    (eC : ∀ D : ↥(irreducibleComponents C), componentUnionScheme C {D} ≅ projectiveSpace k 1)

/-- Each original component prime has the original component's literal image as carrier. -/
theorem curve_carrier (D : ↥(irreducibleComponents C)) :
    (curve S f eC D : Set S.toScheme) = f.base '' (D : Set C) := by
  change Set.range (f.base ∘ (componentUnionInclusion C {D}).base) = _
  rw [Set.range_comp, range_componentUnionInclusion, coe_componentClosedUnion_singleton]

/-- Original distinct irreducible components remain distinct original prime curves. -/
theorem curve_injective : Function.Injective (curve S f eC) := by
  intro D F h
  apply Subtype.ext
  apply f.isClosedEmbedding.injective.image_injective
  have hc := congrArg (fun P : S.PrimeCurve => (P : Set S.toScheme)) h
  simpa only [curve_carrier] using hc

end KltDP.Geometry.RationalComponentPrimeCurves

#print axioms KltDP.Geometry.RationalComponentPrimeCurves.curve_injective

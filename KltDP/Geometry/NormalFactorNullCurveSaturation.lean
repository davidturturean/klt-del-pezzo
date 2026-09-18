import KltDP.Geometry.ProperBirationalPointFiber

/-!
The union of the original degree-zero primes is saturated for the same
proper birational map with connected fibers and the actual prime
contraction criterion. This is a consequence of the proved exhaustion
of each relevant point fiber, without a finiteness or support-cover input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.NormalFactorNullCurveSaturation

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k) (L : InvertibleSheaf X.toScheme)
  {Y : Scheme.{u}} [IsIntegral Y]
  (σ : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType σ]
  (π : X.toScheme ⟶ Y) [IsProper π] [Surjective π]
  (hπ : π ≫ σ = X.structureMorphism) (hbir : IsBirationalScheme π)
  (hconnected : ∀ y : Y, IsConnected (π.base ⁻¹' {y}))
  (hcriterion : ∀ C : X.PrimeCurve,
    (∃ p : Spec (CommRingCat.of k) ⟶ Y,
      C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ σ = 𝟙 _) ↔
      C.restrictionDegree L = 0)

include hπ hbir hconnected hcriterion

/-- Every original fiber meeting the zero-degree prime union lies
entirely in that union. All primes through its points are derived. -/
theorem preimage_image_null_curve_union :
    π.base ⁻¹' (π.base '' (⋃ C ∈ {C : X.PrimeCurve | C.restrictionDegree L = 0},
      (C : Set X.toScheme))) =
      ⋃ C ∈ {C : X.PrimeCurve | C.restrictionDegree L = 0}, (C : Set X.toScheme) := by
  ext x
  constructor
  · rintro ⟨z, hz, hzx⟩
    obtain ⟨C, hzero, hzC⟩ := Set.mem_iUnion₂.mp hz
    obtain ⟨p, hC, hp⟩ := (hcriterion C).mpr hzero
    have hzpoint := PrimeCurvePointFiberFactorization.base_eq_on_prime_of_factor
      X C π p hC z hzC
    have hxpoint : π.base x = fieldMorphismPoint p := hzx.symm.trans hzpoint
    have hfiber := ProperBirationalPointFiber.pointFiber_subset_of_contracted_primes
      X σ π hπ hbir
      (⋃ B ∈ {B : X.PrimeCurve | B.restrictionDegree L = 0}, (B : Set X.toScheme))
      (fun B hB z hzB => Set.mem_iUnion₂.mpr ⟨B, (hcriterion B).mp hB, hzB⟩)
      C p hC hp (hconnected (fieldMorphismPoint p))
    exact hfiber hxpoint
  · intro hx
    exact ⟨x, hx, rfl⟩

end KltDP.Geometry.NormalFactorNullCurveSaturation

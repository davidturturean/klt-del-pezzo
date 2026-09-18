import KltDP.Geometry.ContractedPrimePointFiber
import KltDP.Geometry.ProperBirationalDimension

/-!
For the original proper birational surface map the target is nontrivial:
its dimension is two by the compiled original-map dimension comparison.
Thus the fiber-exhaustion consumer has no target-dimension or target-
nontriviality premise in the application to an actual normal factor.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ProperBirationalPointFiber

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k) {Y : Scheme.{u}} [IsIntegral Y]
  (σ : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType σ]
  (π : X.toScheme ⟶ Y) [IsProper π]

include σ

/-- The actual target of the proper birational surface map has more than
one point, as a consequence of its proved dimension two. -/
theorem target_nontrivial (hbir : IsBirationalScheme π) : Nontrivial Y := by
  rcases subsingleton_or_nontrivial Y with hsub | hnontrivial
  · letI : Subsingleton Y := hsub
    have hd := topologicalKrullDim_nonpos_of_subsingleton Y
    rw [target_dimension_two_of_proper_birational X π σ hbir] at hd
    exact ((WithBot.coe_lt_coe.mpr (by simp : (0 : ℕ∞) < 2)).not_le hd).elim
  · exact hnontrivial

/-- The exact all-prime classification exhausts an original connected
fiber of a proper birational surface map. Target dimension, nontriviality,
and an independent fiber-cover hypothesis are all unnecessary inputs. -/
theorem pointFiber_subset_of_contracted_primes [Surjective π]
    (hπ : π ≫ σ = X.structureMorphism) (hbir : IsBirationalScheme π)
    (S : Set X.toScheme)
    (hS : ∀ B : X.PrimeCurve,
      (∃ q : Spec (CommRingCat.of k) ⟶ Y,
        B.inclusion ≫ π = B.toSpec ≫ q ∧ q ≫ σ = 𝟙 _) →
      (B : Set X.toScheme) ⊆ S)
    (C : X.PrimeCurve) (p : Spec (CommRingCat.of k) ⟶ Y)
    (hC : C.inclusion ≫ π = C.toSpec ≫ p) (hp : p ≫ σ = 𝟙 _)
    (hconnected : IsConnected (π.base ⁻¹' {fieldMorphismPoint p})) :
    π.base ⁻¹' {fieldMorphismPoint p} ⊆ S := by
  letI : Nontrivial Y := target_nontrivial X σ π hbir
  exact ContractedPrimePointFiber.pointFiber_subset_of_contracted_primes
    X σ π hπ S hS C p hC hp hconnected

end KltDP.Geometry.ProperBirationalPointFiber

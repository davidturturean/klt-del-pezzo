import KltDP.Geometry.PointFiberPrimeThroughPoint
import KltDP.Geometry.PrimeCurvePointFiberFactorization

/-!
The original closed connected fiber over a contracted prime is exhausted
by original scheme-contracted primes. The curve through each point is
derived from irreducible components, and its field-point factorization
is constructed through an affine neighborhood. An all-prime classification
therefore controls the entire point fiber, not just its known curves.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ContractedPrimePointFiber

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k) {Y : Scheme.{u}} [Nontrivial Y]
  (σ : Y ⟶ Spec (CommRingCat.of k)) (π : X.toScheme ⟶ Y) [Surjective π]
  (hπ : π ≫ σ = X.structureMorphism)

include hπ

/-- Each point of the original connected fiber containing a contracted
prime lies on an actual prime with an actual field-point factorization. -/
theorem exists_contracted_prime_through_point
    (C : X.PrimeCurve) (p : Spec (CommRingCat.of k) ⟶ Y)
    (hC : C.inclusion ≫ π = C.toSpec ≫ p) (hp : p ≫ σ = 𝟙 _)
    (hconnected : IsConnected (π.base ⁻¹' {fieldMorphismPoint p}))
    (x : X.toScheme) (hx : π.base x = fieldMorphismPoint p) :
    ∃ B : X.PrimeCurve, x ∈ (B : Set X.toScheme) ∧
      ∃ q : Spec (CommRingCat.of k) ⟶ Y,
        B.inclusion ≫ π = B.toSpec ≫ q ∧ q ≫ σ = 𝟙 _ := by
  obtain ⟨B, hxB, hB⟩ :=
    ConnectedPointFiberComponents.exists_primeCurve_through_point X π
      (fieldMorphismPoint p) (isClosed_point_of_section σ p hp) hconnected C
      (PrimeCurvePointFiberFactorization.base_eq_on_prime_of_factor X C π p hC) x hx
  obtain ⟨q, hq, hqσ, _⟩ :=
    PrimeCurvePointFiberFactorization.exists_factor_of_constant X B σ π hπ
      (fieldMorphismPoint p) hB
  exact ⟨B, hxB, q, hq, hqσ⟩

/-- A classification of all original scheme-contracted primes exhausts
the whole connected fiber over any one of those primes. -/
theorem pointFiber_subset_of_contracted_primes
    (S : Set X.toScheme)
    (hS : ∀ B : X.PrimeCurve,
      (∃ q : Spec (CommRingCat.of k) ⟶ Y,
        B.inclusion ≫ π = B.toSpec ≫ q ∧ q ≫ σ = 𝟙 _) →
      (B : Set X.toScheme) ⊆ S)
    (C : X.PrimeCurve) (p : Spec (CommRingCat.of k) ⟶ Y)
    (hC : C.inclusion ≫ π = C.toSpec ≫ p) (hp : p ≫ σ = 𝟙 _)
    (hconnected : IsConnected (π.base ⁻¹' {fieldMorphismPoint p})) :
    π.base ⁻¹' {fieldMorphismPoint p} ⊆ S := by
  intro x hx
  obtain ⟨B, hxB, q, hq, hqσ⟩ :=
    exists_contracted_prime_through_point X σ π hπ C p hC hp hconnected x hx
  exact hS B ⟨q, hq, hqσ⟩ hxB

end KltDP.Geometry.ContractedPrimePointFiber

import KltDP.Geometry.CartierSectionMonomialBoxes
import KltDP.Geometry.CartierSectionBaseValues
import KltDP.Geometry.PolynomialEmbeddingDimensionBound
import Mathlib.RingTheory.AlgebraicIndependent.Defs

/-!
# Independent actual homogeneous sections from independent original ratios

The original base-field linear rational-value map, divided by the fixed
denominator power, sends the constructed section box to the existing
independent polynomial monomial box. This proves independence of the
actual sections and computes their actual span dimension.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open KltDP.Geometry.ModuleCohomology
open scoped BigOperators

universe u

namespace KltDP.Geometry.SectionMonomialGrowth

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} [IsIntegral X] {k : Type u} [Field k]
  (f : X ⟶ Spec (CommRingCat.of k))

/-- Normalize the original linear rational-value map by a fixed field value. -/
def normalizedValueBaseLinearMap (D : CartierDivisor X) (c : X.functionField) :
    letI := baseSectionsModule f (cartierDivisorModule X D)
    letI := functionFieldAlgebra f
    sections (cartierDivisorModule X D) →ₗ[k] X.functionField := by
  letI := baseSectionsModule f (cartierDivisorModule X D)
  letI := functionFieldAlgebra f
  exact {
    toFun := fun s => cartierGlobalSectionRationalValue X D s / c
    map_add' := fun s t =>
      (congrArg (fun z : X.functionField => z / c)
        ((rationalValueBaseLinearMap f D).map_add s t)).trans (add_div _ _ _)
    map_smul' := fun a s => by
      change cartierGlobalSectionRationalValue X D (a • s) / c =
        functionFieldScalar f a * (cartierGlobalSectionRationalValue X D s / c)
      rw [rationalValue_base_smul, mul_div_assoc] }

include f

/-- The literal normalized field value is the existing box monomial. -/
theorem ratio_boxSection_aeval (D : CartierDivisor X)
    (s₀ : sections (cartierDivisorModule X D)) (hs₀ : s₀ ≠ 0) {d : ℕ}
    (s : Fin d → sections (cartierDivisorModule X D))
    (q : ℕ) (a : Fin d → Fin (q + 1)) :
    letI := functionFieldAlgebra f
    cartierGlobalSectionRationalValue X ((q * d) • D) (boxSection X D s₀ s q a) /
        cartierGlobalSectionRationalValue X D s₀ ^ (q * d) =
      MvPolynomial.aeval (R := k)
        (fun i => cartierGlobalSectionRationalValue X D (s i) /
          cartierGlobalSectionRationalValue X D s₀)
        (MvPolynomial.monomial (PolynomialEmbeddingDimensionBound.boxExponent d q a) 1) := by
  letI := functionFieldAlgebra f
  rw [MvPolynomial.aeval_monomial, map_one, one_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  exact ratio_boxSection X D s₀ hs₀ s q a

/-- Algebraic independence of the original section ratios proves linear
independence of the constructed original same-degree sections. -/
theorem boxSection_linearIndependent (D : CartierDivisor X)
    (s₀ : sections (cartierDivisorModule X D)) (hs₀ : s₀ ≠ 0) {d : ℕ}
    (s : Fin d → sections (cartierDivisorModule X D))
    (hs : letI := functionFieldAlgebra f
      AlgebraicIndependent k (fun i => cartierGlobalSectionRationalValue X D (s i) /
        cartierGlobalSectionRationalValue X D s₀)) (q : ℕ) :
    letI := baseSectionsModule f (cartierDivisorModule X ((q * d) • D))
    LinearIndependent k (boxSection X D s₀ s q) := by
  letI := baseSectionsModule f (cartierDivisorModule X ((q * d) • D))
  letI := functionFieldAlgebra f
  let r : Fin d → X.functionField := fun i =>
    cartierGlobalSectionRationalValue X D (s i) / cartierGlobalSectionRationalValue X D s₀
  let v := normalizedValueBaseLinearMap f ((q * d) • D)
    (cartierGlobalSectionRationalValue X D s₀ ^ (q * d))
  apply LinearIndependent.of_comp v
  have he : v ∘ boxSection X D s₀ s q =
      (fun a : Fin d → Fin (q + 1) => MvPolynomial.aeval (R := k) r
        (MvPolynomial.monomial (PolynomialEmbeddingDimensionBound.boxExponent d q a) 1)) := by
    funext a
    exact ratio_boxSection_aeval f D s₀ hs₀ s q a
  rw [he]
  exact PolynomialEmbeddingDimensionBound.box_monomials_linearIndependent
    (MvPolynomial.aeval (R := k) r) (algebraicIndependent_iff_injective_aeval.mp hs) q

/-- The original section span has the exact cardinality of the exponent box. -/
theorem boxSectionSpan_finrank (D : CartierDivisor X)
    (s₀ : sections (cartierDivisorModule X D)) (hs₀ : s₀ ≠ 0) {d : ℕ}
    (s : Fin d → sections (cartierDivisorModule X D))
    (hs : letI := functionFieldAlgebra f
      AlgebraicIndependent k (fun i => cartierGlobalSectionRationalValue X D (s i) /
        cartierGlobalSectionRationalValue X D s₀)) (q : ℕ) :
    letI := baseSectionsModule f (cartierDivisorModule X ((q * d) • D))
    Module.finrank k (Submodule.span k (Set.range (boxSection X D s₀ s q))) = (q + 1) ^ d := by
  letI := baseSectionsModule f (cartierDivisorModule X ((q * d) • D))
  rw [finrank_span_eq_card (boxSection_linearIndependent f D s₀ hs₀ s hs q)]
  simp only [Fintype.card_fun, Fintype.card_fin]

end KltDP.Geometry.SectionMonomialGrowth

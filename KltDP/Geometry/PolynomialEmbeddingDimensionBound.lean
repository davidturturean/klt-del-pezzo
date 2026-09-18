import KltDP.Compatibility.PolynomialDimension
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Dimension-bounding polynomial embeddings and independent monomial boxes

Pinned Noether normalization and the accepted polynomial-dimension proof
give an actual polynomial embedding with at least the ring's dimension
many variables. The original monomial basis gives independent finite boxes
of size `(q + 1)^d` in that same original algebra.

This is the algebraic input to a section-growth proof. It does not assert
that these elements already come from sections of a fixed tensor power.
-/

noncomputable section

namespace KltDP.Geometry.PolynomialEmbeddingDimensionBound

variable (k A : Type*) [Field k] [CommRing A] [Algebra k A]

/-- An actual finite-type algebra admits an injective polynomial map
whose variable count bounds its actual Krull dimension. -/
theorem exists_embedding [Nontrivial A] [Algebra.FiniteType k A] :
    ∃ (d : ℕ) (g : MvPolynomial (Fin d) k →ₐ[k] A),
      Function.Injective g ∧ ringKrullDim A ≤ (d : WithBot ℕ∞) := by
  obtain ⟨d, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k A
  exact ⟨d, g, hg,
    (KltDP.Compatibility.ringKrullDim_le_of_integral g.toRingHom hint).trans
      (KltDP.Compatibility.polynomial_ringKrullDim k d).le⟩

variable {k A}

/-- The actual monomials remain independent under an injective algebra map. -/
theorem monomials_linearIndependent {d : ℕ}
    (g : MvPolynomial (Fin d) k →ₐ[k] A) (hg : Function.Injective g) :
    LinearIndependent k (fun a : Fin d →₀ ℕ => g (MvPolynomial.monomial a 1)) := by
  simpa only [Function.comp_def, MvPolynomial.coe_basisMonomials] using
    (MvPolynomial.basisMonomials (Fin d) k).linearIndependent.map' g.toLinearMap
      (LinearMap.ker_eq_bot.mpr hg)

/-- The exponent vector of an actual finite monomial box. -/
def boxExponent (d q : ℕ) (a : Fin d → Fin (q + 1)) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ))

theorem boxExponent_injective (d q : ℕ) : Function.Injective (boxExponent d q) := by
  intro a b hab
  funext i
  apply Fin.ext
  exact congrArg (fun v : Fin d →₀ ℕ => v i) hab

/-- Restricting to the exponent box preserves actual linear independence. -/
theorem box_monomials_linearIndependent {d : ℕ}
    (g : MvPolynomial (Fin d) k →ₐ[k] A) (hg : Function.Injective g) (q : ℕ) :
    LinearIndependent k (fun a : Fin d → Fin (q + 1) =>
      g (MvPolynomial.monomial (boxExponent d q a) 1)) :=
  (monomials_linearIndependent g hg).comp (boxExponent d q) (boxExponent_injective d q)

/-- The original span of this finite box has exactly `(q + 1)^d` dimensions
over the same original field. -/
theorem box_monomialSpan_finrank {d : ℕ}
    (g : MvPolynomial (Fin d) k →ₐ[k] A) (hg : Function.Injective g) (q : ℕ) :
    Module.finrank k (Submodule.span k (Set.range
      (fun a : Fin d → Fin (q + 1) =>
        g (MvPolynomial.monomial (boxExponent d q a) 1)))) = (q + 1) ^ d := by
  rw [finrank_span_eq_card (box_monomials_linearIndependent g hg q)]
  simp only [Fintype.card_fun, Fintype.card_fin]

end KltDP.Geometry.PolynomialEmbeddingDimensionBound

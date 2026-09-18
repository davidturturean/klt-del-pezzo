import KltDP.Geometry.CartierHomogeneousSectionEvaluation

/-!
# Original section witnesses for homogeneous polynomial fractions

A nonzero polynomial denominator evaluated at the original section ratios
gives a nonzero actual same-degree Cartier section. The quotient of the
two constructed sections is the original homogeneous polynomial quotient.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open KltDP.Geometry.ModuleCohomology

universe u v

namespace KltDP.Geometry.SectionMonomialGrowth

variable {X : Scheme.{u}} [IsIntegral X] {k : Type u} [Field k]
  {I : Type v} (f : X ⟶ Spec (CommRingCat.of k))

/-- A nonzero denominator value produces a nonzero original section. -/
theorem homogeneousSection_ne_zero_of_ratio_eval_ne_zero (D : CartierDivisor X)
    (s₀ : sections (cartierDivisorModule X D))
    (s : I → sections (cartierDivisorModule X D))
    (p : MvPolynomial I k) {n : ℕ} (hp : p.IsHomogeneous n)
    (hp₀ : MvPolynomial.eval₂ (functionFieldScalar f)
      (fun i => cartierGlobalSectionRationalValue X D (s i) /
        cartierGlobalSectionRationalValue X D s₀) p ≠ 0) :
    homogeneousSection f D s p hp ≠ 0 := by
  intro hzero
  have h := ratio_homogeneousSection f D s₀ s p hp
  rw [hzero] at h
  have hz : cartierGlobalSectionRationalValue X (n • D) 0 = 0 :=
    map_zero (rationalFunctionModuleSectionsEquiv X ⊤)
  rw [hz, zero_div] at h
  exact hp₀ h.symm

/-- The quotient of the constructed actual same-degree sections is the
original polynomial quotient in the original function-field ratios. -/
theorem homogeneousSection_quotient (D : CartierDivisor X)
    (s₀ : sections (cartierDivisorModule X D)) (hs₀ : s₀ ≠ 0)
    (s : I → sections (cartierDivisorModule X D))
    (p q : MvPolynomial I k) {n : ℕ} (hp : p.IsHomogeneous n) (hq : q.IsHomogeneous n) :
    cartierGlobalSectionRationalValue X (n • D) (homogeneousSection f D s p hp) /
        cartierGlobalSectionRationalValue X (n • D) (homogeneousSection f D s q hq) =
      MvPolynomial.eval₂ (functionFieldScalar f)
          (fun i => cartierGlobalSectionRationalValue X D (s i) /
            cartierGlobalSectionRationalValue X D s₀) p /
        MvPolynomial.eval₂ (functionFieldScalar f)
          (fun i => cartierGlobalSectionRationalValue X D (s i) /
            cartierGlobalSectionRationalValue X D s₀) q := by
  rw [← ratio_homogeneousSection f D s₀ s p hp,
    ← ratio_homogeneousSection f D s₀ s q hq]
  exact (div_div_div_cancel_right₀
    (pow_ne_zero n (cartierGlobalSectionRationalValue_ne_zero X D s₀ hs₀)) _ _).symm

end KltDP.Geometry.SectionMonomialGrowth

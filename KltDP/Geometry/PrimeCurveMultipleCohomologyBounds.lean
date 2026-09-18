import KltDP.Geometry.PrimeCurveTwistCohomologyBounds

/-!
# Uniform actual cohomology bounds along multiples of a prime curve

These bounds iterate the original prime-curve short exact sequences.
They do not need the curve to be smooth or any cohomological duality.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology

universe u

set_option autoImplicit false

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x) (C : X.PrimeCurve)

/-- Iterating the actual prime-curve twist gives both monotonicity bounds. -/
theorem cohomologyDimension_prime_add_nsmul_bounds
    (D : CartierDivisor X.toScheme) (n : ℕ) :
    cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme D) 0 ≤
        cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme
          (D + n • X.primeCurveCartier hregular C)) 0 ∧
      cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme
        (D + n • X.primeCurveCartier hregular C)) 2 ≤
        cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme D) 2 := by
  induction n with
  | zero => simp only [zero_nsmul, add_zero, le_refl, and_self]
  | succ n ih =>
    have hs := X.cohomologyDimension_prime_add_bounds hregular C
      (D + n • X.primeCurveCartier hregular C)
    simpa only [succ_nsmul, add_assoc] using
      And.intro (ih.1.trans hs.1) (hs.2.trans ih.2)

/-- The two original cohomology terms in the RR defect have fixed bounds
independent of n. -/
theorem cohomologyDimension_prime_multiples_bounds
    (K : CartierDivisor X.toScheme) (n : ℕ) :
    cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme
      (K - n • X.primeCurveCartier hregular C)) 0 ≤
        cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme K) 0 ∧
      cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme
        (n • X.primeCurveCartier hregular C)) 2 ≤
        cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme 0) 2 := by
  have h₀ := (X.cohomologyDimension_prime_add_nsmul_bounds hregular C
    (K - n • X.primeCurveCartier hregular C) n).1
  have h₂ := (X.cohomologyDimension_prime_add_nsmul_bounds hregular C 0 n).2
  exact ⟨by simpa only [sub_add_cancel] using h₀,
    by simpa only [zero_add] using h₂⟩

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.cohomologyDimension_prime_add_nsmul_bounds
#print axioms KltDP.Geometry.NormalProjectiveSurface.cohomologyDimension_prime_add_nsmul_bounds
#check @KltDP.Geometry.NormalProjectiveSurface.cohomologyDimension_prime_multiples_bounds
#print axioms KltDP.Geometry.NormalProjectiveSurface.cohomologyDimension_prime_multiples_bounds

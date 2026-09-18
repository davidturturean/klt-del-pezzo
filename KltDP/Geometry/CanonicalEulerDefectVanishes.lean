import KltDP.Geometry.PrimeCurveMultipleCohomologyBounds
import KltDP.Geometry.CartierRiemannRochCohomology

/-!
# Vanishing of the actual canonical Euler defect

For n times an original prime curve, the defect is both n times a fixed
integer and twice a difference of two uniformly bounded actual cohomology
dimensions. Hence that integer vanishes. Actual prime divisors generate
the Cartier group on the regular surface, giving the general formula.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison

universe u

set_option autoImplicit false

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
  (K : CartierDivisor X.toScheme)
  (eK : cartierDivisorModule X.toScheme K ≅
    relativeDifferentialExterior X.structureMorphism 2)

include eK

/-- The original canonical Euler defect vanishes on every actual prime
curve, including singular integral curves. -/
theorem canonicalEulerDefectHom_primeCurve (C : X.PrimeCurve) :
    X.canonicalEulerDefectHom hregular K (X.primeCurveCartier hregular C) = 0 := by
  let a := cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme K) 0
  let b := cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme 0) 2
  let d := X.canonicalEulerDefectHom hregular K (X.primeCurveCartier hregular C)
  have hb : ∀ n : ℕ, -2 * (a : ℤ) ≤ (n : ℤ) * d ∧ (n : ℤ) * d ≤ 2 * (b : ℤ) := by
    intro n
    have he := X.canonicalEulerDefectHom_eq_cohomology hregular K eK
      (n • X.primeCurveCartier hregular C)
    rw [map_nsmul, nsmul_eq_mul] at he
    have hs := X.cohomologyDimension_prime_multiples_bounds hregular C K n
    have hs₀ : (cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme
        (K - n • X.primeCurveCartier hregular C)) 0 : ℤ) ≤ (a : ℤ) := by
      exact_mod_cast hs.1
    have hs₂ : (cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme
        (n • X.primeCurveCartier hregular C)) 2 : ℤ) ≤ (b : ℤ) := by
      exact_mod_cast hs.2
    change (n : ℤ) * d = _ at he
    constructor <;> omega
  have h := hb (2 * (a + b) + 1)
  push_cast at h
  have ha : (0 : ℤ) ≤ a := Nat.cast_nonneg a
  have hb' : (0 : ℤ) ≤ b := Nat.cast_nonneg b
  change d = 0
  rcases lt_trichotomy d 0 with hd | hd | hd
  · have hd' : d ≤ -1 := by omega
    nlinarith [h.1]
  · exact hd
  · have hd' : 1 ≤ d := by omega
    nlinarith [h.2]

/-- The original finite Weil expansion extends the vanishing from actual
prime curves to every actual Cartier divisor. -/
theorem canonicalEulerDefectHom_eq_zero (D : CartierDivisor X.toScheme) :
    X.canonicalEulerDefectHom hregular K D = 0 := by
  rw [X.addMonoidHom_eq_weil_sum hregular
    (X.canonicalEulerDefectHom hregular K) D]
  unfold Finsupp.sum
  apply Finset.sum_eq_zero
  intro C _
  dsimp only
  rw [X.canonicalEulerDefectHom_primeCurve hregular K eK C]
  simp

/-- The Euler form of RR is derived from the existing three-term RR and
the original prime-curve cohomology sequences. -/
theorem cartier_euler_riemannRoch_twice (D : CartierDivisor X.toScheme) :
    2 * eulerCharacteristic X.structureMorphism (cartierDivisorModule X.toScheme D) =
      intersectionPairing X hregular D (D - K) +
        2 * eulerCharacteristic X.structureMorphism
          (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) := by
  have h := X.canonicalEulerDefectHom_eq_zero hregular K eK D
  rw [X.canonicalEulerDefectHom_apply] at h
  omega

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.canonicalEulerDefectHom_primeCurve
#print axioms KltDP.Geometry.NormalProjectiveSurface.canonicalEulerDefectHom_primeCurve
#check @KltDP.Geometry.NormalProjectiveSurface.cartier_euler_riemannRoch_twice
#print axioms KltDP.Geometry.NormalProjectiveSurface.cartier_euler_riemannRoch_twice

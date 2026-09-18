import KltDP.Geometry.CanonicalEulerDefectVanishes

/-!
# The Euler correction for the inverse half-branch line

The previously proved Euler form of surface Riemann--Roch is applied to
the original negative Cartier divisor. This proves the plus sign in
D · (D + K), and the exact Euler value of the two intended cover-algebra
summands. It does not identify this sum with the cover's Euler value;
the actual pushforward decomposition and cohomology comparison remain
separate geometric obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison

universe u

set_option autoImplicit false

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (S : NormalProjectiveSurface k)
  (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)
  (K : CartierDivisor S.toScheme)
  (eK : cartierDivisorModule S.toScheme K ≅
    relativeDifferentialExterior S.structureMorphism 2)

include eK

/-- RR for the actual inverse Cartier line, retaining its correct sign. -/
theorem inverseCartier_euler_riemannRoch_twice (D : CartierDivisor S.toScheme) :
    2 * eulerCharacteristic S.structureMorphism
        (cartierDivisorModule S.toScheme (-D)) =
      intersectionPairing S hregular D (D + K) +
        2 * eulerCharacteristic S.structureMorphism
          (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) := by
  have h := S.cartier_euler_riemannRoch_twice hregular K eK (-D)
  have hneg : -D - K = -(D + K) := by abel
  rw [hneg, S.intersectionPairing_neg_left, S.intersectionPairing_neg_right,
    neg_neg] at h
  exact h

/-- The original unit and inverse Cartier modules have the exact RR
correction used by the double-cover calculation. -/
theorem unit_add_inverseCartier_euler (D : CartierDivisor S.toScheme) :
    (eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) : ℚ) +
      (eulerCharacteristic S.structureMorphism
        (cartierDivisorModule S.toScheme (-D)) : ℚ) =
      2 * (eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) : ℚ) +
        (intersectionPairing S hregular D (D + K) : ℚ) / 2 := by
  have h := S.inverseCartier_euler_riemannRoch_twice hregular K eK D
  have hQ := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at hQ
  linarith only [hQ]

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.unit_add_inverseCartier_euler
#print axioms KltDP.Geometry.NormalProjectiveSurface.unit_add_inverseCartier_euler

import KltDP.Geometry.CartierEulerRiemannRochDefect
import KltDP.Geometry.SurfaceRiemannRochProved
import KltDP.Geometry.SurfaceEulerStructureSheaf

/-!
# The existing three-term Riemann–Roch formula on actual Cartier divisors

The canonical input is the genuine O(K) isomorphism with the original
exterior square. The final equality identifies the additive Euler defect
with twice h2(O(D)) minus twice h0(O(K-D)); it does not assume duality.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SurfaceRiemannRochSource
open KltDP.Geometry.SmoothCanonicalExteriorComparison

universe u

set_option autoImplicit false

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- The published three-term formula, transported through the proved
Cartier–Weil equivalence while retaining the given canonical module. -/
theorem cartier_riemannRoch (K : CartierDivisor X.toScheme)
    (eK : cartierDivisorModule X.toScheme K ≅
      relativeDifferentialExterior X.structureMorphism 2)
    (D : CartierDivisor X.toScheme) :
    (cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme D) 0 : ℚ) -
      (cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme D) 1 : ℚ) +
      (cohomologyDimension X.structureMorphism
        (cartierDivisorModule X.toScheme (K - D)) 0 : ℚ) =
      (intersectionPairing X hregular D (D - K) : ℚ) / 2 +
        (eulerCharacteristic X.structureMorphism
          (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) : ℚ) := by
  let e := X.regularCartierWeilEquiv hregular
  have hK : IsCanonical X hregular (e K) := by
    change Nonempty (cartierDivisorModule X.toScheme (e.symm (e K)) ≅ _)
    rw [e.symm_apply_apply]
    exact ⟨eK⟩
  have hr := SurfaceRiemannRochProved.riemannRoch X hregular (e D) (e K) hK
  have hKD : e K - e D = e (K - D) := (map_sub e K D).symm
  have hDK : e D - e K = e (D - K) := (map_sub e D K).symm
  change _ = (intersectionPairing X hregular (e.symm (e D))
    (e.symm (e D - e K)) : ℚ) / 2 + 1 + (arithmeticGenus X : ℚ) at hr
  simp only [hDimension, divisorModule, hKD, hDK, e.symm_apply_apply] at hr
  have heD : (X.regularCartierWeilEquiv hregular).symm (e D) = D :=
    e.symm_apply_apply D
  have heKD : (X.regularCartierWeilEquiv hregular).symm (e (K - D)) = K - D :=
    e.symm_apply_apply (K - D)
  rw [heD, heKD] at hr
  unfold arithmeticGenus at hr
  push_cast at hr
  linarith only [hr]

/-- The actual difference is bounded once the original top cohomology
and complementary sections are bounded. No top-duality equality is used. -/
theorem canonicalEulerDefectHom_eq_cohomology (K : CartierDivisor X.toScheme)
    (eK : cartierDivisorModule X.toScheme K ≅
      relativeDifferentialExterior X.structureMorphism 2)
    (D : CartierDivisor X.toScheme) :
    X.canonicalEulerDefectHom hregular K D =
      2 * (cohomologyDimension X.structureMorphism
        (cartierDivisorModule X.toScheme D) 2 : ℤ) -
      2 * (cohomologyDimension X.structureMorphism
        (cartierDivisorModule X.toScheme (K - D)) 0 : ℤ) := by
  have hr := X.cartier_riemannRoch hregular K eK D
  have he := normalProjectiveSurface_eulerCharacteristic_eq X
    (cartierDivisorModule X.toScheme D)
  rw [X.canonicalEulerDefectHom_apply]
  have heQ := congrArg (fun z : ℤ => (z : ℚ)) he
  push_cast at heQ
  exact_mod_cast (show
    2 * (eulerCharacteristic X.structureMorphism
      (cartierDivisorModule X.toScheme D) : ℚ) -
      2 * (eulerCharacteristic X.structureMorphism
        (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) : ℚ) -
      (intersectionPairing X hregular D (D - K) : ℚ) =
      2 * (cohomologyDimension X.structureMorphism
        (cartierDivisorModule X.toScheme D) 2 : ℚ) -
      2 * (cohomologyDimension X.structureMorphism
        (cartierDivisorModule X.toScheme (K - D)) 0 : ℚ) by linarith only [hr, heQ])

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.cartier_riemannRoch
#print axioms KltDP.Geometry.NormalProjectiveSurface.cartier_riemannRoch
#check @KltDP.Geometry.NormalProjectiveSurface.canonicalEulerDefectHom_eq_cohomology
#print axioms KltDP.Geometry.NormalProjectiveSurface.canonicalEulerDefectHom_eq_cohomology

import KltDP.Geometry.RationalPicardIntersection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The actual intersection form on the existing numerical quotient

The radical of the Q-bilinear extension of the original Picard intersection
pairing is exactly the existing `numericallyTrivialSubmodule`: vanishing is
tested on every actual prime curve. The accepted Cartier–Weil equivalence
supplies the finite integral prime generators; tensor induction supplies the
Q-linear extension. Two applications of Mathlib's `Submodule.liftQ` descend
the form to the existing `NumericalClassGroup` without choosing representatives.

The descended form is symmetric and nondegenerate, and pairing with the class
of an actual prime curve is its existing descended restriction-degree test.
Neither numerical-space finite dimensionality, Picard injectivity, Hodge index,
Riemann–Roch nor any Euler polynomial is assumed or proved here.
-/

noncomputable section

open AlgebraicGeometry
open scoped TensorProduct BigOperators

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

include hregular

/-- Actual prime Cartier divisors generate the whole Cartier group, so a Q-valued
additive map vanishing on all of them vanishes everywhere. -/
private theorem cartierHom_eq_zero_of_prime (f : CartierDivisor X.toScheme →+ ℚ)
    (hf : ∀ C : X.PrimeCurve, f (X.primeCurveCartier hregular C) = 0)
    (D : CartierDivisor X.toScheme) : f D = 0 := by
  have hD : D = (X.regularCartierWeilEquiv hregular).symm
      ((X.cartierToWeilHom D).sum Finsupp.single) := by
    rw [Finsupp.sum_single, ← X.regularCartierWeilEquiv_apply hregular D,
      AddEquiv.symm_apply_apply]
  rw [hD, map_finsuppSum, map_finsuppSum]
  unfold Finsupp.sum
  refine Finset.sum_eq_zero fun C _ => ?_
  have hsingle : (Finsupp.single C ((X.cartierToWeilHom D) C) : X.WeilDivisor) =
      ((X.cartierToWeilHom D) C) • Finsupp.single C (1 : ℤ) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  change f ((X.regularCartierWeilEquiv hregular).symm
    (Finsupp.single C ((X.cartierToWeilHom D) C))) = 0
  rw [hsingle, map_zsmul, map_zsmul]
  change _ • f (X.primeCurveCartier hregular C) = 0
  rw [hf C, smul_zero]

/-- An existing numerically trivial rational class pairs to zero with every
rationalized Picard class. -/
theorem rationalPicardIntersectionBilinForm_eq_zero_of_mem
    (v : X.RationalPicard) (hv : v ∈ X.numericallyTrivialSubmodule)
    (w : X.RationalPicard) : X.rationalPicardIntersectionBilinForm hregular v w = 0 := by
  induction w using TensorProduct.induction_on with
  | zero => exact map_zero (X.rationalPicardIntersectionBilinForm hregular v)
  | tmul a p =>
      obtain ⟨D, hD⟩ := cartierPicardClass_surjective X.toScheme p.toMul
      have hp : cartierPicardHom X.toScheme D = p := by
        change Additive.ofMul (cartierPicardClass X.toScheme D) = p
        exact congrArg Additive.ofMul hD
      let f : CartierDivisor X.toScheme →+ ℚ :=
        (X.rationalPicardIntersectionBilinForm hregular v).toAddMonoidHom.comp
          (X.picardTensorInclusion.toAddMonoidHom.comp (cartierPicardHom X.toScheme))
      have hf : ∀ C : X.PrimeCurve, f (X.primeCurveCartier hregular C) = 0 := by
        intro C
        change X.rationalPicardIntersectionBilinForm hregular v
          (X.picardTensorInclusion (cartierPicardHom X.toScheme
            (X.primeCurveCartier hregular C))) = 0
        change X.rationalPicardIntersectionBilinForm hregular v
          (X.primeCurveRationalPicardClass hregular C) = 0
        rw [rationalPicardIntersectionBilinForm_primeCurve]
        exact (X.mem_numericallyTrivialSubmodule_iff v).mp hv C
      have hzero := cartierHom_eq_zero_of_prime X hregular f hf D
      change X.rationalPicardIntersectionBilinForm hregular v
        (X.picardTensorInclusion (cartierPicardHom X.toScheme D)) = 0 at hzero
      rw [hp] at hzero
      have ha : (a ⊗ₜ[ℤ] p) = a • X.picardTensorInclusion p := by
        change (a ⊗ₜ[ℤ] p) = a • ((1 : ℚ) ⊗ₜ[ℤ] p)
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ha, map_smul, hzero, smul_zero]
  | add w₁ w₂ h₁ h₂ =>
      rw [map_add, h₁, h₂, add_zero]

/-- The radical is characterized by exactly the existing all-prime-curve tests. -/
theorem mem_numericallyTrivialSubmodule_iff_rationalPicardIntersection_eq_zero
    (v : X.RationalPicard) :
    v ∈ X.numericallyTrivialSubmodule ↔
      ∀ w : X.RationalPicard, X.rationalPicardIntersectionBilinForm hregular v w = 0 := by
  constructor
  · intro hv w
    exact X.rationalPicardIntersectionBilinForm_eq_zero_of_mem hregular v hv w
  · intro h
    apply (X.mem_numericallyTrivialSubmodule_iff v).mpr
    intro C
    rw [← X.rationalPicardIntersectionBilinForm_primeCurve hregular v C]
    exact h (X.primeCurveRationalPicardClass hregular C)

/-- The kernel of the actual rational bilinear form is the existing numerical radical. -/
theorem rationalPicardIntersectionBilinForm_ker :
    LinearMap.ker (X.rationalPicardIntersectionBilinForm hregular) =
      X.numericallyTrivialSubmodule := by
  ext v
  change X.rationalPicardIntersectionBilinForm hregular v = 0 ↔
    v ∈ X.numericallyTrivialSubmodule
  rw [LinearMap.ext_iff]
  change (∀ w : X.RationalPicard,
    X.rationalPicardIntersectionBilinForm hregular v w = 0) ↔ _
  exact (X.mem_numericallyTrivialSubmodule_iff_rationalPicardIntersection_eq_zero hregular v).symm

/-- Numerical equivalence preserves the actual pairing in its first variable. -/
theorem rationalPicardIntersectionBilinForm_congr_left {v v' : X.RationalPicard}
    (h : X.RationalNumericallyEquivalent v v') (w : X.RationalPicard) :
    X.rationalPicardIntersectionBilinForm hregular v w =
      X.rationalPicardIntersectionBilinForm hregular v' w := by
  have hzero := X.rationalPicardIntersectionBilinForm_eq_zero_of_mem hregular (v - v')
    ((X.rationalNumericallyEquivalent_iff_sub_mem v v').mp h) w
  rw [LinearMap.BilinForm.sub_left] at hzero
  exact sub_eq_zero.mp hzero

/-- Numerical equivalence preserves the actual pairing in its second variable. -/
theorem rationalPicardIntersectionBilinForm_congr_right (v : X.RationalPicard)
    {w w' : X.RationalPicard} (h : X.RationalNumericallyEquivalent w w') :
    X.rationalPicardIntersectionBilinForm hregular v w =
      X.rationalPicardIntersectionBilinForm hregular v w' := by
  rw [LinearMap.BilinForm.IsSymm.eq (X.rationalPicardIntersectionBilinForm_isSymm hregular) v w,
    LinearMap.BilinForm.IsSymm.eq (X.rationalPicardIntersectionBilinForm_isSymm hregular) v w']
  exact X.rationalPicardIntersectionBilinForm_congr_left hregular h v

/-- The intermediate form descends only its second variable along the existing quotient. -/
private def rationalNumericalIntersection :
    X.RationalPicard →ₗ[ℚ] X.NumericalClassGroup →ₗ[ℚ] ℚ where
  toFun v := X.numericallyTrivialSubmodule.liftQ
    (X.rationalPicardIntersectionBilinForm hregular v) (by
      intro w hw
      change X.rationalPicardIntersectionBilinForm hregular v w = 0
      rw [LinearMap.BilinForm.IsSymm.eq
        (X.rationalPicardIntersectionBilinForm_isSymm hregular) v w]
      exact X.rationalPicardIntersectionBilinForm_eq_zero_of_mem hregular w hw v)
  map_add' v v' := by
    apply LinearMap.ext
    intro c
    obtain ⟨w, rfl⟩ := X.rationalPicardNumericalMap_surjective c
    change X.rationalPicardIntersectionBilinForm hregular (v + v') w =
      X.rationalPicardIntersectionBilinForm hregular v w +
        X.rationalPicardIntersectionBilinForm hregular v' w
    exact LinearMap.BilinForm.add_left v v' w
  map_smul' a v := by
    apply LinearMap.ext
    intro c
    obtain ⟨w, rfl⟩ := X.rationalPicardNumericalMap_surjective c
    change X.rationalPicardIntersectionBilinForm hregular (a • v) w =
      a * X.rationalPicardIntersectionBilinForm hregular v w
    exact LinearMap.BilinForm.smul_left a v w

/-- The actual Q-bilinear intersection form on the existing numerical quotient. -/
def numericalIntersectionBilinForm : LinearMap.BilinForm ℚ X.NumericalClassGroup :=
  X.numericallyTrivialSubmodule.liftQ (rationalNumericalIntersection X hregular) (by
    intro v hv
    change rationalNumericalIntersection X hregular v = 0
    apply LinearMap.ext
    intro c
    obtain ⟨w, rfl⟩ := X.rationalPicardNumericalMap_surjective c
    change X.rationalPicardIntersectionBilinForm hregular v w = 0
    exact X.rationalPicardIntersectionBilinForm_eq_zero_of_mem hregular v hv w)

/-- Both quotient maps recover the same rational Picard intersection value. -/
@[simp]
theorem numericalIntersectionBilinForm_mk_mk (v w : X.RationalPicard) :
    X.numericalIntersectionBilinForm hregular
        (X.rationalPicardNumericalMap v) (X.rationalPicardNumericalMap w) =
      X.rationalPicardIntersectionBilinForm hregular v w := rfl

/-- The descended form remains symmetric. -/
theorem numericalIntersectionBilinForm_isSymm :
    (X.numericalIntersectionBilinForm hregular).IsSymm := by
  intro c d
  obtain ⟨v, rfl⟩ := X.rationalPicardNumericalMap_surjective c
  obtain ⟨w, rfl⟩ := X.rationalPicardNumericalMap_surjective d
  rw [numericalIntersectionBilinForm_mk_mk, numericalIntersectionBilinForm_mk_mk]
  exact X.rationalPicardIntersectionBilinForm_isSymm hregular v w

/-- The existing numerical map from integral Picard classes retains their pairing. -/
theorem numericalIntersectionBilinForm_picard (p q : Additive X.toScheme.Pic) :
    X.numericalIntersectionBilinForm hregular (X.picardNumericalMap p) (X.picardNumericalMap q) =
      (picardPairing X hregular p.toMul q.toMul : ℚ) := by
  change X.numericalIntersectionBilinForm hregular
    (X.rationalPicardNumericalMap (X.picardTensorInclusion p))
    (X.rationalPicardNumericalMap (X.picardTensorInclusion q)) = _
  rw [numericalIntersectionBilinForm_mk_mk, rationalPicardIntersectionBilinForm_inclusion]

/-- Pairing against the original prime curve's numerical class is its existing numerical degree. -/
theorem numericalIntersectionBilinForm_primeCurve (c : X.NumericalClassGroup)
    (C : X.PrimeCurve) :
    X.numericalIntersectionBilinForm hregular c
        (X.picardNumericalClass (cartierPicardClass X.toScheme (X.primeCurveCartier hregular C))) =
      X.numericalRestrictionDegree C c := by
  obtain ⟨v, rfl⟩ := X.rationalPicardNumericalMap_surjective c
  change X.numericalIntersectionBilinForm hregular (X.rationalPicardNumericalMap v)
    (X.rationalPicardNumericalMap (X.primeCurveRationalPicardClass hregular C)) = _
  rw [numericalIntersectionBilinForm_mk_mk, numericalRestrictionDegree_mk,
    rationalPicardIntersectionBilinForm_primeCurve]

/-- Nondegeneracy follows from the actual prime-curve tests that define this quotient. -/
theorem numericalIntersectionBilinForm_nondegenerate :
    (X.numericalIntersectionBilinForm hregular).Nondegenerate := by
  intro c hc
  apply (X.numericalClass_eq_zero_iff c).mpr
  intro C
  rw [← X.numericalIntersectionBilinForm_primeCurve hregular c C]
  exact hc (X.picardNumericalClass
    (cartierPicardClass X.toScheme (X.primeCurveCartier hregular C)))

end KltDP.Geometry.NormalProjectiveSurface

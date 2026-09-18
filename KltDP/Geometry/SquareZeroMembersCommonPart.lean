import KltDP.Geometry.NefSquareZeroCommonPart
import KltDP.Geometry.SquareZeroOrthogonalIntegral
import KltDP.Geometry.EffectiveWeilAmpleDegree

/-! Two distinct effective original members of a nef class F with
F²=0 and K.F=-2 have zero common divisor. The residual is constructed
coefficientwise, and all positivity and integral proportionality inputs
are derived from the original members and canonical RR parity. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.NormalProjectiveSurface
open NefNullCurveNegativeSquare

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
  (K : CartierDivisor X.toScheme)
  (eK : cartierDivisorModule X.toScheme K ≅
    relativeDifferentialExterior X.structureMorphism 2)

local instance membersCommonSourceIntegral : IsIntegral X.toScheme := X.integral

private theorem common_degree_zero (z m f n : ℤ)
    (hz : 0 ≤ z) (hm : 0 < m) (hs : z + m = f) (hp : m = n * f) : z = 0 := by
  have hmf : m ≤ f := by omega
  have hf : 0 < f := lt_of_lt_of_le hm hmf
  have hnpos : 0 < n := (mul_pos_iff_of_pos_right hf).mp (by rwa [← hp])
  have hnle : n ≤ 1 := by
    apply (mul_le_mul_right hf).mp
    simpa only [one_mul, ← hp] using hmf
  have hn1 : n = 1 := by omega
  rw [hn1, one_mul] at hp
  omega

include eK in
/-- The actual common divisor of any two distinct original effective
members vanishes; there is no supplied fixed-part or moving-nef input. -/
theorem commonWeilPart_eq_zero_of_nef_squareZero (F : CartierDivisor X.toScheme)
    (hF : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme F))
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2)
    (D E : X.WeilDivisor) (hD : EffectiveDivisor D) (hE : EffectiveDivisor E)
    (hDF : X.LinearlyEquivalent D (X.cartierToWeilHom F))
    (hEF : X.LinearlyEquivalent E (X.cartierToWeilHom F)) (hne : D ≠ E) :
    D ⊓ E = 0 := by
  let e := X.regularCartierWeilEquiv hX
  let Z : X.WeilDivisor := D ⊓ E
  let M : X.WeilDivisor := D - Z
  have hDE := X.linearlyEquivalent_trans hDF (X.linearlyEquivalent_symm hEF)
  have hMeff : EffectiveDivisor M := X.commonWeilPart_left_effective D E
  have hZeff : EffectiveDivisor Z := X.commonWeilPart_effective D E hD hE
  have hMne : M ≠ 0 := X.commonWeilPart_left_ne_zero hX D E hDE hne
  have hMM : 0 ≤ X.intersectionPairing hX (e.symm M) (e.symm M) :=
    X.commonWeilPart_residual_square_nonneg hX D E hDE
  have hMF : X.intersectionPairing hX (e.symm M) F = 0 :=
    (X.commonWeilPart_and_residual_null hX F hF hFF D E hD hE hDF).2
  have hFM : X.intersectionPairing hX F (e.symm M) = 0 :=
    (X.intersectionPairing_symm hX F (e.symm M)).trans hMF
  obtain ⟨n, hn, _⟩ := X.squareZero_orthogonal_integral_multiple hX K eK F (e.symm M)
    hFF hKF hMM hFM
  obtain ⟨A, hA, hAnef⟩ := X.exists_isAmple_isNef_cartier
  have hMpos : 0 < X.intersectionPairing hX (e.symm M) A :=
    X.effectiveWeil_ample_pairing_pos hX M hMeff hMne A hA
  have hZnonneg : 0 ≤ X.intersectionPairing hX (e.symm Z) A :=
    NefIntersectionSectionVanishing.intersection_nonneg X hX A hAnef Z hZeff
  have hprodQ : (X.intersectionPairing hX (e.symm M) A : ℚ) =
      (n : ℚ) * (X.intersectionPairing hX F A : ℚ) := by
    calc
      _ = X.numericalIntersectionBilinForm hX
          (cartierClass X (e.symm M)) (cartierClass X A) :=
        (cartierClass_pairing X hX (e.symm M) A).symm
      _ = (n : ℚ) * X.numericalIntersectionBilinForm hX
          (cartierClass X F) (cartierClass X A) := by
        rw [hn]
        exact (X.numericalIntersectionBilinForm hX).smul_left _ _ _
      _ = _ := by rw [cartierClass_pairing]
  have hprod : X.intersectionPairing hX (e.symm M) A =
      n * X.intersectionPairing hX F A := by exact_mod_cast hprodQ
  have hsum : e.symm Z + e.symm M = e.symm D := by
    rw [← map_add]
    congr 1
    dsimp only [M]
    abel
  have hrep : e.symm (X.cartierToWeilHom F) = F := e.symm_apply_apply F
  have hDA : X.intersectionPairing hX (e.symm D) A = X.intersectionPairing hX F A := by
    rw [NefIntersectionSectionVanishing.intersection_eq_of_linearlyEquivalent X hX A hDF, hrep]
  have hsumA : X.intersectionPairing hX (e.symm Z) A +
      X.intersectionPairing hX (e.symm M) A = X.intersectionPairing hX F A := by
    rw [← X.intersectionPairing_add_left hX, hsum, hDA]
  have hZA : X.intersectionPairing hX (e.symm Z) A = 0 :=
    common_degree_zero _ _ _ n hZnonneg hMpos hsumA hprod
  exact X.effectiveWeil_eq_zero_of_ample_pairing_zero hX Z hZeff A hA hZA

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.commonWeilPart_eq_zero_of_nef_squareZero
#print axioms KltDP.Geometry.NormalProjectiveSurface.commonWeilPart_eq_zero_of_nef_squareZero

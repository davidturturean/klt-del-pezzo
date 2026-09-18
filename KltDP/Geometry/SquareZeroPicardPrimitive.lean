import KltDP.Geometry.CanonicalPicardCharacteristic
import Mathlib.Algebra.Ring.Int.Units

/-! The original square-zero Picard class of canonical degree minus two
cannot be a nonunit integral multiple. The finite algebra proof uses the
actual characteristic parity producer, with no freeness, nefness or
rationality assumption needed for this first clause of the pencil lemma. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u

namespace KltDP.Geometry.SquareZeroPrimitive

/-- A zero-square vector pairing to minus two with a characteristic vector
is divisible only by units in the original integer module. -/
theorem multiplicity_isUnit {M : Type*} [AddCommGroup M] [Module ℤ M]
    (B : LinearMap.BilinForm ℤ M) (K F : M)
    (hchar : KltDP.Codes.IsCharacteristic B K)
    (hFF : B F F = 0) (hKF : B K F = -2)
    (d : ℤ) (G : M) (hdiv : d • G = F) : IsUnit d := by
  have hright (x y : M) : B x (d • y) = d * B x y := by
    have h := (B x).toAddMonoidHom.map_zsmul y d
    change B x (d • y) = d • (B x y) at h
    simpa only [zsmul_eq_mul] using h
  have hleft (x y : M) : B (d • x) y = d * B x y := by
    have h := (B.flip y).toAddMonoidHom.map_zsmul x d
    change B (d • x) y = d • (B x y) at h
    simpa only [zsmul_eq_mul] using h
  have hKG : d * B K G = -2 := calc
    d * B K G = B K (d • G) :=
      (hright K G).symm
    _ = B K F := congrArg (fun v : M => B K v) hdiv
    _ = -2 := hKF
  have hd : d ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hKG
    norm_num at hKG
  have hGGmul : d * (d * B G G) = 0 := calc
    d * (d * B G G) = d * B G (d • G) :=
      congrArg (fun z : ℤ => d * z)
        (hright G G).symm
    _ = B (d • G) (d • G) :=
      (hleft G (d • G)).symm
    _ = B F F := congrArg (fun v : M => B v v) hdiv
    _ = 0 := hFF
  have hGG : B G G = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hGGmul).resolve_left hd)).resolve_left hd
  have heven := hchar G
  rw [hGG, zero_sub] at heven
  obtain ⟨a, ha⟩ := heven
  have hm : d * (-B K G) = d * (a + a) :=
    congrArg (fun z : ℤ => d * z) ha
  have hda : d * a = 1 := by nlinarith only [hm, hKG]
  exact isUnit_of_mul_eq_one d a hda

end KltDP.Geometry.SquareZeroPrimitive

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
  (K : CartierDivisor X.toScheme)
  (eK : cartierDivisorModule X.toScheme K ≅
    relativeDifferentialExterior X.structureMorphism 2)

local instance primitiveSourceIntegral : IsIntegral X.toScheme := X.integral

include eK in
/-- Primitivity in the original Picard group, not merely its numerical image. -/
theorem squareZero_picard_multiplicity_isUnit (F : CartierDivisor X.toScheme)
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2)
    (d : ℤ) (G : Additive X.toScheme.Pic)
    (hdiv : d • G = cartierPicardHom X.toScheme F) : IsUnit d := by
  apply SquareZeroPrimitive.multiplicity_isUnit
    (X.integralPicardIntersectionBilinForm hX) (cartierPicardHom X.toScheme K)
    (cartierPicardHom X.toScheme F)
    (X.canonicalPicard_isCharacteristic hX K eK) _ _ d G hdiv
  · rw [X.integralPicardIntersectionBilinForm_apply]
    exact (X.picardPairing_class hX F F).trans hFF
  · rw [X.integralPicardIntersectionBilinForm_apply]
    exact (X.picardPairing_class hX K F).trans hKF

include eK in
/-- The manuscript's literal no-multiple definition of primitivity. -/
theorem squareZero_picard_not_divisible (F : CartierDivisor X.toScheme)
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2) :
    ∀ d : ℤ, 1 < d → ∀ G : Additive X.toScheme.Pic,
      d • G ≠ cartierPicardHom X.toScheme F := by
  intro d hd G hdiv
  have hu := X.squareZero_picard_multiplicity_isUnit hX K eK F hFF hKF d G hdiv
  rcases Int.isUnit_eq_one_or hu with he | he <;> omega

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.squareZero_picard_not_divisible
#print axioms KltDP.Geometry.NormalProjectiveSurface.squareZero_picard_not_divisible

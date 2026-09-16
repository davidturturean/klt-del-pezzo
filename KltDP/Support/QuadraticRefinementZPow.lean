import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic

/-!
# Quadratic refinements along all integer powers

For an integer-valued function on a commutative group with bilinear second difference `B`,
the correction `2 f(p) - 2 f(1) - B(p,p)` is additive on `Additive G`. The existing
`AddMonoidHom.map_zsmul` theorem gives its value on every integer power. Bilinearity supplies
the quadratic diagonal term and the mixed term for two powers.

This is generic algebra. Its explicit multiplication/second-difference hypotheses are proved
for the actual geometric Euler function by the separate regular-surface adapter.
-/

namespace KltDP.Support.QuadraticRefinement

variable {G : Type*} [CommGroup G]

/-- A pairing additive in its first multiplicative argument scales on every integer power. -/
theorem bilinear_zpow_left (B : G → G → ℤ)
    (hleft : ∀ p p' q, B (p * p') q = B p q + B p' q)
    (p q : G) (n : ℤ) : B (p ^ n) q = n * B p q := by
  let b : Additive G →+ ℤ := AddMonoidHom.mk' (fun a => B a.toMul q)
    (fun a a' => hleft a.toMul a'.toMul q)
  have h := b.map_zsmul (Additive.ofMul p) n
  change B (p ^ n) q = n • B p q at h
  simpa only [zsmul_eq_mul] using h

/-- The corresponding scaling in the second argument. -/
theorem bilinear_zpow_right (B : G → G → ℤ)
    (hright : ∀ p q q', B p (q * q') = B p q + B p q')
    (p q : G) (n : ℤ) : B p (q ^ n) = n * B p q := by
  let b : Additive G →+ ℤ := AddMonoidHom.mk' (fun a => B p a.toMul)
    (fun a a' => hright p a.toMul a'.toMul)
  have h := b.map_zsmul (Additive.ofMul q) n
  change B p (q ^ n) = n • B p q at h
  simpa only [zsmul_eq_mul] using h

/-- Bilinear scaling on a pair of arbitrary integer powers. -/
theorem bilinear_zpow_zpow (B : G → G → ℤ)
    (hleft : ∀ p p' q, B (p * p') q = B p q + B p' q)
    (hright : ∀ p q q', B p (q * q') = B p q + B p q')
    (p q : G) (m n : ℤ) : B (p ^ m) (q ^ n) = m * (n * B p q) := by
  rw [bilinear_zpow_left B hleft, bilinear_zpow_right B hright]

/-- Inverting both arguments preserves a bilinear pairing. -/
theorem bilinear_inv_inv (B : G → G → ℤ)
    (hleft : ∀ p p' q, B (p * p') q = B p q + B p' q)
    (hright : ∀ p q q', B p (q * q') = B p q + B p q')
    (p q : G) : B p⁻¹ q⁻¹ = B p q := by
  simpa only [zpow_neg_one, neg_one_mul, neg_neg] using
    bilinear_zpow_zpow B hleft hright p q (-1) (-1)

/-- The doubled integer-valued quadratic formula, valid at positive and negative exponents. -/
theorem two_mul_apply_zpow (f : G → ℤ) (B : G → G → ℤ)
    (hleft : ∀ p p' q, B (p * p') q = B p q + B p' q)
    (hright : ∀ p q q', B p (q * q') = B p q + B p q')
    (hmul : ∀ p q, f (p * q) = f p + f q - f 1 + B p q)
    (p : G) (n : ℤ) :
    2 * f (p ^ n) = 2 * f 1 + n * (2 * f p - 2 * f 1 - B p p) + n ^ 2 * B p p := by
  have hsymm (a b : G) : B a b = B b a := by
    have hab := hmul a b
    have hba := hmul b a
    rw [mul_comm b a] at hba
    linarith only [hab, hba]
  let l : Additive G →+ ℤ :=
    AddMonoidHom.mk' (fun a => 2 * f a.toMul - 2 * f 1 - B a.toMul a.toMul) (by
      intro a b
      change 2 * f (a.toMul * b.toMul) - 2 * f 1 -
          B (a.toMul * b.toMul) (a.toMul * b.toMul) =
        (2 * f a.toMul - 2 * f 1 - B a.toMul a.toMul) +
          (2 * f b.toMul - 2 * f 1 - B b.toMul b.toMul)
      rw [hmul, hleft, hright, hright, hsymm b.toMul a.toMul]
      ring)
  have hl := l.map_zsmul (Additive.ofMul p) n
  change 2 * f (p ^ n) - 2 * f 1 - B (p ^ n) (p ^ n) =
    n • (2 * f p - 2 * f 1 - B p p) at hl
  rw [zsmul_eq_mul, bilinear_zpow_zpow B hleft hright p p n n] at hl
  linear_combination hl

/-- The rational-coefficient polynomial for a single integer power. -/
theorem apply_zpow_rat (f : G → ℤ) (B : G → G → ℤ)
    (hleft : ∀ p p' q, B (p * p') q = B p q + B p' q)
    (hright : ∀ p q q', B p (q * q') = B p q + B p q')
    (hmul : ∀ p q, f (p * q) = f p + f q - f 1 + B p q)
    (p : G) (n : ℤ) :
    (f (p ^ n) : ℚ) = (f 1 : ℚ) +
      ((f p : ℚ) - (f 1 : ℚ) - (B p p : ℚ) / 2) * (n : ℚ) +
      (B p p : ℚ) / 2 * (n : ℚ) ^ 2 := by
  have h := congrArg (fun z : ℤ => (z : ℚ))
    (two_mul_apply_zpow f B hleft hright hmul p n)
  push_cast at h
  linear_combination (1 / 2 : ℚ) * h

/-- The doubled mixed formula with its integer mixed coefficient. -/
theorem two_mul_apply_zpow_mul_zpow (f : G → ℤ) (B : G → G → ℤ)
    (hleft : ∀ p p' q, B (p * p') q = B p q + B p' q)
    (hright : ∀ p q q', B p (q * q') = B p q + B p q')
    (hmul : ∀ p q, f (p * q) = f p + f q - f 1 + B p q)
    (p q : G) (m n : ℤ) :
    2 * f (p ^ m * q ^ n) = 2 * f 1 +
      m * (2 * f p - 2 * f 1 - B p p) + n * (2 * f q - 2 * f 1 - B q q) +
      m ^ 2 * B p p + 2 * (m * n) * B p q + n ^ 2 * B q q := by
  have hp := two_mul_apply_zpow f B hleft hright hmul p m
  have hq := two_mul_apply_zpow f B hleft hright hmul q n
  rw [hmul (p ^ m) (q ^ n), bilinear_zpow_zpow B hleft hright p q m n]
  linear_combination hp + hq

/-- A rational polynomial of total degree at most two on every integer pair. -/
theorem apply_zpow_mul_zpow_rat (f : G → ℤ) (B : G → G → ℤ)
    (hleft : ∀ p p' q, B (p * p') q = B p q + B p' q)
    (hright : ∀ p q q', B p (q * q') = B p q + B p q')
    (hmul : ∀ p q, f (p * q) = f p + f q - f 1 + B p q)
    (p q : G) (m n : ℤ) :
    (f (p ^ m * q ^ n) : ℚ) = (f 1 : ℚ) +
      ((f p : ℚ) - (f 1 : ℚ) - (B p p : ℚ) / 2) * (m : ℚ) +
      ((f q : ℚ) - (f 1 : ℚ) - (B q q : ℚ) / 2) * (n : ℚ) +
      (B p p : ℚ) / 2 * (m : ℚ) ^ 2 +
      (B p q : ℚ) * ((m : ℚ) * (n : ℚ)) + (B q q : ℚ) / 2 * (n : ℚ) ^ 2 := by
  have h := congrArg (fun z : ℤ => (z : ℚ))
    (two_mul_apply_zpow_mul_zpow f B hleft hright hmul p q m n)
  push_cast at h
  linear_combination (1 / 2 : ℚ) * h

end KltDP.Support.QuadraticRefinement

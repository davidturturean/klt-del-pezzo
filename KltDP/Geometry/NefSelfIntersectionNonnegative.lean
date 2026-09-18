import KltDP.Geometry.NefPositiveSelfIntersectionBig
import KltDP.Geometry.RiemannRochEffectiveMultiple
import KltDP.Geometry.ProjectiveAmpleCartierWitness

/-!
# Nonnegative self-intersection of actual nef line bundles

An actual ample Cartier divisor H has nonnegative intersection with a nef
divisor A, by its original effective positive power. If A²=-c<0 and H.A=b,
the actual Cartier divisor D=2cH+(2b+1)A satisfies D.A=-c, D.H>0 and D²>0.
The compiled RR argument gives an actual effective positive multiple of D.
Its negative intersection with the original nef A is impossible.

The final smooth consumer constructs H and the canonical divisor. No ample
plus nef criterion, Hodge premise, or supplied effective divisor is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.SurfaceRiemannRochSource
open KltDP.Geometry.SmoothCanonicalCartierRepresentative

universe u

namespace KltDP.Geometry.NefSelfIntersectionNonnegative

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

private theorem intersection_zsmul_left (m : ℤ) (D H : CartierDivisor X.toScheme) :
    intersectionPairing X hregular (m • D) H =
      m * intersectionPairing X hregular D H := by
  let f : CartierDivisor X.toScheme →+ ℤ :=
    AddMonoidHom.mk' (fun E => intersectionPairing X hregular E H)
      (fun E F => X.intersectionPairing_add_left hregular E F H)
  have h := f.map_zsmul D m
  change intersectionPairing X hregular (m • D) H =
    m • intersectionPairing X hregular D H at h
  simpa only [zsmul_eq_mul] using h

private theorem intersection_zsmul_right (m : ℤ) (D H : CartierDivisor X.toScheme) :
    intersectionPairing X hregular D (m • H) =
      m * intersectionPairing X hregular D H := by
  rw [X.intersectionPairing_symm hregular D (m • H), intersection_zsmul_left,
    X.intersectionPairing_symm hregular H D]

/-- An actual ample Cartier divisor has nonnegative intersection with any
actual nef Cartier divisor, using a proved effective positive ample power. -/
theorem intersection_nonneg_of_isAmple_isNef (H A : CartierDivisor X.toScheme)
    (hH : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme H))
    (hA : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme A)) :
    0 ≤ intersectionPairing X hregular H A := by
  obtain ⟨n, hn, M, hM, E, _, ⟨e⟩, _, hEff⟩ :=
    AmpleSelfIntersectionPositive.exists_nonzero_effectiveCartier_power_of_isAmple X
      (cartierDivisorInvertibleSheaf X.toScheme H) hH
  have hp := NefIntersectionSectionVanishing.intersection_nonneg X hregular A hA
    (X.cartierToWeilHom E) hEff
  rw [RiemannRochEffectiveMultiple.inverse_toWeil,
    ← X.picardPairing_class hregular E A] at hp
  have hclass : cartierPicardClass X.toScheme E = (cartierPicardClass X.toScheme H) ^ n :=
    (SchemeKernelIdealIsoTransport.toPic_eq_of_iso
      (cartierDivisorInvertibleSheaf X.toScheme E) M e).trans hM
  rw [hclass, AmpleSelfIntersectionPositive.picardPairing_pow_left,
    X.picardPairing_class hregular H A] at hp
  exact (mul_nonneg_iff_of_pos_left (Nat.cast_pos.mpr hn : (0 : ℤ) < n)).mp hp

private theorem contradiction_pairings (H A : CartierDivisor X.toScheme) (a b c : ℤ)
    (ha : intersectionPairing X hregular H H = a)
    (hb : intersectionPairing X hregular H A = b)
    (hc : intersectionPairing X hregular A A = -c) :
    let D := (2 * c) • H + (2 * b + 1) • A
    intersectionPairing X hregular D A = -c ∧
      intersectionPairing X hregular D H = 2 * c * a + (2 * b + 1) * b ∧
        intersectionPairing X hregular D D = c * (4 * c * a + 4 * b ^ 2 - 1) := by
  have hAH : intersectionPairing X hregular A H = b :=
    (X.intersectionPairing_symm hregular A H).trans hb
  dsimp only
  constructor
  · rw [X.intersectionPairing_add_left, intersection_zsmul_left,
      intersection_zsmul_left, hb, hc]
    ring
  constructor
  · rw [X.intersectionPairing_add_left, intersection_zsmul_left,
      intersection_zsmul_left, ha, hAH]
  · simp only [X.intersectionPairing_add_left, X.intersectionPairing_add_right,
      intersection_zsmul_left, intersection_zsmul_right, ha, hb, hc, hAH]
    ring

private theorem contradiction_positive (a b c : ℤ) (ha : 0 < a) (hb : 0 ≤ b)
    (hc : 0 < c) :
    0 < 2 * c * a + (2 * b + 1) * b ∧
      0 < c * (4 * c * a + 4 * b ^ 2 - 1) := by
  have hca : 0 < c * a := mul_pos hc ha
  have hcaOne : 1 ≤ c * a := by omega
  have hbterm : 0 ≤ (2 * b + 1) * b := mul_nonneg (by omega) hb
  constructor
  · nlinarith
  · apply mul_pos hc
    nlinarith [sq_nonneg b]

/-- RR rules out negative self-intersection for an actual nef Cartier
divisor. The auxiliary ample divisor is constructed from projectivity. -/
theorem intersection_nonneg_of_isCanonical (K : X.WeilDivisor)
    (hK : IsCanonical X hregular K) (A : CartierDivisor X.toScheme)
    (hA : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme A)) :
    0 ≤ intersectionPairing X hregular A A := by
  by_contra hnonnegative
  have hnegative : intersectionPairing X hregular A A < 0 := lt_of_not_ge hnonnegative
  obtain ⟨H, hH⟩ := X.exists_isAmple_cartier
  have hHH : 0 < intersectionPairing X hregular H H := by
    have h := AmpleSelfIntersectionPositive.selfIntersection_pos_of_isAmple X hregular
      (cartierDivisorInvertibleSheaf X.toScheme H) hH
    change 0 < X.picardPairing hregular
      (cartierPicardClass X.toScheme H) (cartierPicardClass X.toScheme H) at h
    rwa [X.picardPairing_class hregular] at h
  let c : ℤ := -intersectionPairing X hregular A A
  let b : ℤ := intersectionPairing X hregular H A
  have hc : 0 < c := neg_pos.mpr hnegative
  have hb : 0 ≤ b := intersection_nonneg_of_isAmple_isNef X hregular H A hH hA
  let D : CartierDivisor X.toScheme := (2 * c) • H + (2 * b + 1) • A
  obtain ⟨hDA, hDH, hDD⟩ := contradiction_pairings X hregular H A
    (intersectionPairing X hregular H H) b c rfl rfl (by simp only [c, neg_neg])
  obtain ⟨hDHpos, hDDpos⟩ :=
    contradiction_positive (intersectionPairing X hregular H H) b c hHH hb hc
  have hD_H : 0 < intersectionPairing X hregular D H := hDH.symm ▸ hDHpos
  have hD_D : 0 < intersectionPairing X hregular D D := hDD.symm ▸ hDDpos
  obtain ⟨n, hn, Z, hZ, hZD⟩ :=
    RiemannRochEffectiveMultiple.exists_positive_effective_multiple X hregular K hK D H
      (AmpleNefUnconditional.isNef_of_isAmple X _ hH) hD_D hD_H
  have hmultiple : intersectionPairing X hregular (n • D) A < 0 := by
    rw [RiemannRochEffectiveMultiple.intersection_nsmul_left, hDA]
    exact mul_neg_of_pos_of_neg (Nat.cast_pos.mpr hn) (neg_lt_zero.mpr hc)
  have heffective := NefIntersectionSectionVanishing.intersection_nonneg X hregular A hA Z hZ
  rw [NefIntersectionSectionVanishing.intersection_eq_of_linearlyEquivalent X hregular A hZD,
    RiemannRochEffectiveMultiple.inverse_toWeil] at heffective
  exact (not_le_of_gt hmultiple) heffective

/-- Nonnegative square transfers to the original arbitrary nef line
bundle through its actual Cartier representative. -/
theorem selfIntersection_nonneg_of_isCanonical (K : X.WeilDivisor)
    (hK : IsCanonical X hregular K) (L : InvertibleSheaf X.toScheme)
    (hL : Positivity.IsNef X.structureMorphism L) :
    0 ≤ X.selfIntersection hregular L := by
  let A := X.picardRepresentative L.toPic
  have hclass : cartierPicardClass X.toScheme A = L.toPic :=
    X.cartierPicardClass_picardRepresentative L.toPic
  have h := intersection_nonneg_of_isCanonical X hregular K hK A
    (NefPositiveSelfIntersectionBig.isNef_of_toPic_eq X hclass.symm hL)
  rw [← X.picardPairing_class hregular A A, hclass] at h
  exact h

section Smooth

variable [IsSmoothOfRelativeDimension 2 X.structureMorphism]

local instance source_isSmooth : IsSmooth X.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 X.structureMorphism

/-- Every actual nef line bundle on the original smooth projective
surface has nonnegative self-intersection. -/
theorem selfIntersection_nonneg (L : InvertibleSheaf X.toScheme)
    (hL : Positivity.IsNef X.structureMorphism L) :
    0 ≤ X.selfIntersection X.regularPoints_of_isSmooth L :=
  selfIntersection_nonneg_of_isCanonical X X.regularPoints_of_isSmooth (weilRepresentative X)
    (SurfaceRiemannRochSource.constructedCanonical_isCanonical X) L hL

/-- The same original nef line bundle has nonnegative four-term Euler
pairing, through the compiled comparison on the original regular surface. -/
theorem picardEulerPairing_self_nonneg (L : InvertibleSheaf X.toScheme)
    (hL : Positivity.IsNef X.structureMorphism L) :
    0 ≤ X.picardEulerPairing L.toPic L.toPic := by
  rw [← X.selfIntersection_eq_picardEulerPairing_of_regular X.regularPoints_of_isSmooth L]
  exact selfIntersection_nonneg X L hL

end Smooth

end KltDP.Geometry.NefSelfIntersectionNonnegative

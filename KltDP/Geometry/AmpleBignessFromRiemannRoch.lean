import KltDP.Geometry.SurfaceRiemannRochNef
import KltDP.Geometry.AmpleSelfIntersectionPositive
import KltDP.Geometry.ProjectiveAmpleWitness
import KltDP.Geometry.RiemannRochGrowthBound

/-!
# Actual section growth and bigness on smooth projective surfaces

The full surface RR formula bounds the original h⁰ of O(nA), after actual
nef intersection forces every section of O(K-nA) to vanish. Positive
integral self-intersection then gives the bound n²/4 for arbitrarily large
n. The Cartier-to-Picard comparison transports those original cohomology
dimensions to the powers in the existing definition `Positivity.IsBig`.

The smooth ample consumer constructs the canonical divisor and a Cartier
representative of the given line bundle. It assumes no vanishing, duality,
Euler-characteristic value, effective representative, or extra ample class.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.ModuleCohomology KltDP.Geometry.SurfaceRiemannRochSource
open KltDP.Geometry.SmoothCanonicalCartierRepresentative

universe u

namespace KltDP.Geometry.AmpleBignessFromRiemannRoch

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

private theorem inverse_toWeil (A : CartierDivisor X.toScheme) :
    (X.regularCartierWeilEquiv hregular).symm (X.cartierToWeilHom A) = A :=
  (X.regularCartierWeilEquiv hregular).symm_apply_apply A

private theorem intersection_nsmul_left (n : ℕ) (A B : CartierDivisor X.toScheme) :
    intersectionPairing X hregular (n • A) B =
      (n : ℤ) * intersectionPairing X hregular A B := by
  induction n with
  | zero =>
    simp only [zero_nsmul, X.intersectionPairing_zero_left hregular,
      Nat.cast_zero, zero_mul]
  | succ n ih =>
    rw [succ_nsmul, X.intersectionPairing_add_left, ih, Nat.cast_add, Nat.cast_one]
    ring

private theorem intersection_nsmul_right (n : ℕ) (A B : CartierDivisor X.toScheme) :
    intersectionPairing X hregular A (n • B) =
      (n : ℤ) * intersectionPairing X hregular A B := by
  rw [X.intersectionPairing_symm hregular A (n • B), intersection_nsmul_left,
    X.intersectionPairing_symm hregular B A]

private theorem class_nsmul (A : CartierDivisor X.toScheme) (n : ℕ) :
    cartierPicardClass X.toScheme (n • A) = (cartierPicardClass X.toScheme A) ^ n :=
  congrArg Additive.toMul ((cartierPicardHom X.toScheme).map_nsmul A n)

/-- The cohomology dimension in the full RR statement is exactly h⁰ of
the original power of the Cartier line bundle in the existing Picard group. -/
theorem hDimension_nsmul (A : CartierDivisor X.toScheme) (n : ℕ) :
    hDimension X hregular (X.cartierToWeilHom (n • A)) 0 =
      Positivity.picardHZero X.structureMorphism ((cartierPicardClass X.toScheme A) ^ n) := by
  unfold hDimension divisorModule
  rw [inverse_toWeil, ← class_nsmul]
  exact (Positivity.picardHZero_toPic X.structureMorphism
    (cartierDivisorInvertibleSheaf X.toScheme (n • A))).symm

/-- The existing RR expression on an actual Cartier multiple, with its
actual structure-sheaf Euler characteristic left arbitrary. -/
theorem rrNumber_nsmul (A : CartierDivisor X.toScheme) (K : X.WeilDivisor) (n : ℕ) :
    rrNumber X hregular (X.cartierToWeilHom (n • A)) K =
      ((intersectionPairing X hregular A A : ℚ) * (n : ℚ) ^ 2 -
        (intersectionPairing X hregular A
          ((X.regularCartierWeilEquiv hregular).symm K) : ℚ) * (n : ℚ)) / 2 +
        (eulerCharacteristic X.structureMorphism
          (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) : ℚ) := by
  unfold rrNumber arithmeticGenus
  simp only [map_sub, inverse_toWeil]
  rw [sub_eq_add_neg (n • A), X.intersectionPairing_add_right,
    X.intersectionPairing_neg_right, intersection_nsmul_left,
    intersection_nsmul_right, intersection_nsmul_left]
  push_cast
  ring

/-- Removing the actual complementary section space from full RR gives
a lower bound for the original h⁰; h¹ contributes a nonnegative dimension. -/
theorem rrNumber_le_hDimension (D K : X.WeilDivisor)
    (hK : IsCanonical X hregular K)
    (hvanish : Subsingleton (sections (divisorModule X hregular (K - D)))) :
    rrNumber X hregular D K ≤ (hDimension X hregular D 0 : ℚ) := by
  have heq := SurfaceRiemannRochProved.riemannRoch X hregular D K hK
  have hzero : hDimension X hregular (K - D) 0 = 0 := by
    letI := baseSectionsModule X.structureMorphism (divisorModule X hregular (K - D))
    letI : Subsingleton (sections (divisorModule X hregular (K - D))) := hvanish
    change cohomologyDimension X.structureMorphism (divisorModule X hregular (K - D)) 0 = 0
    rw [cohomologyDimension_zero_eq_finrank_sections]
    exact Module.finrank_zero_of_subsingleton
  rw [hzero, Nat.cast_zero, add_zero] at heq
  rw [← heq]
  exact sub_le_self _ (Nat.cast_nonneg _)

/-- An actual nef Cartier line bundle with positive self-intersection is
big in the original section-growth sense. Canonicality is supplied by the
constructed smooth canonical divisor in the final consumer below. -/
theorem isBig_of_nef_of_intersection_pos (K : X.WeilDivisor)
    (hK : IsCanonical X hregular K) (A : CartierDivisor X.toScheme)
    (hA : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme A))
    (hpositive : 0 < intersectionPairing X hregular A A) :
    Positivity.IsBig X.structureMorphism (cartierDivisorInvertibleSheaf X.toScheme A) := by
  let a : ℤ := intersectionPairing X hregular A A
  let b : ℤ := intersectionPairing X hregular A
    ((X.regularCartierWeilEquiv hregular).symm K)
  let z : ℤ := eulerCharacteristic X.structureMorphism
    (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf)
  have ha : (1 : ℚ) ≤ (a : ℚ) := by
    have h : (1 : ℤ) ≤ a := by omega
    exact_mod_cast h
  have hdim : Positivity.natDim X.toScheme = 2 := by
    unfold Positivity.natDim
    rw [X.dimension_two]
    rfl
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro N
  obtain ⟨n, hn, hdegree, hgrowth⟩ :=
    RiemannRochGrowthBound.exists_large_with_quadratic_bound (a : ℚ) (b : ℚ) (z : ℚ) ha N
  have hdegreeZ : b < (n : ℤ) * a := by exact_mod_cast hdegree
  have hnegative : intersectionPairing X hregular
      ((X.regularCartierWeilEquiv hregular).symm
        (K - X.cartierToWeilHom (n • A))) A < 0 := by
    apply SurfaceRiemannRochNef.complementary_intersection_neg X hregular
      (X.cartierToWeilHom (n • A)) K A
    rw [inverse_toWeil, intersection_nsmul_left,
      X.intersectionPairing_symm hregular
        ((X.regularCartierWeilEquiv hregular).symm K) A]
    exact hdegreeZ
  have hvanish := NefIntersectionSectionVanishing.sections_subsingleton X hregular
    (K - X.cartierToWeilHom (n • A)) A hA hnegative
  have hrr := rrNumber_le_hDimension X hregular
    (X.cartierToWeilHom (n • A)) K hK hvanish
  rw [rrNumber_nsmul, hDimension_nsmul] at hrr
  refine ⟨n, hn, ?_⟩
  rw [hdim]
  exact hgrowth.trans hrr

/-- Serre ampleness supplies nefness and positive self-intersection for
the actual Cartier representative of the given original line bundle. -/
theorem isBig_of_isAmple_of_isCanonical (K : X.WeilDivisor)
    (hK : IsCanonical X hregular K) (L : InvertibleSheaf X.toScheme)
    (hL : AmpleSerre.IsAmple L) : Positivity.IsBig X.structureMorphism L := by
  let A := X.picardRepresentative L.toPic
  have hclass : cartierPicardClass X.toScheme A = L.toPic :=
    X.cartierPicardClass_picardRepresentative L.toPic
  have hample : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme A) :=
    AmplePositivity.isAmple_of_toPic_eq hclass.symm hL
  have hpositive : 0 < intersectionPairing X hregular A A := by
    have h := AmpleSelfIntersectionPositive.selfIntersection_pos_of_isAmple X hregular
      (cartierDivisorInvertibleSheaf X.toScheme A) hample
    change 0 < X.picardPairing hregular
      (cartierPicardClass X.toScheme A) (cartierPicardClass X.toScheme A) at h
    rwa [X.picardPairing_class hregular] at h
  have hbig := isBig_of_nef_of_intersection_pos X hregular K hK A
    (AmpleNefUnconditional.isNef_of_isAmple X _ hample) hpositive
  change ∃ c : ℚ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
    c * (n : ℚ) ^ Positivity.natDim X.toScheme ≤
      (Positivity.picardHZero X.structureMorphism
        ((cartierPicardClass X.toScheme A) ^ n) : ℚ) at hbig
  rw [hclass] at hbig
  exact hbig

section Smooth

variable [IsSmoothOfRelativeDimension 2 X.structureMorphism]

local instance source_isSmooth : IsSmooth X.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 X.structureMorphism

/-- Every actual ample line bundle on the original smooth projective
surface is big, with canonicality and complementary vanishing proved here. -/
theorem isBig_of_isAmple (L : InvertibleSheaf X.toScheme)
    (hL : AmpleSerre.IsAmple L) : Positivity.IsBig X.structureMorphism L :=
  isBig_of_isAmple_of_isCanonical X X.regularPoints_of_isSmooth (weilRepresentative X)
    (SurfaceRiemannRochSource.constructedCanonical_isCanonical X) L hL

/-- The actual projective ample witness is simultaneously big on the
original smooth surface; no line-bundle or divisor witness is assumed. -/
theorem exists_isAmple_isBig :
    ∃ L : InvertibleSheaf X.toScheme,
      AmpleSerre.IsAmple L ∧ Positivity.IsBig X.structureMorphism L := by
  obtain ⟨L, hL⟩ := X.exists_isAmple
  exact ⟨L, hL, isBig_of_isAmple X L hL⟩

end Smooth

end KltDP.Geometry.AmpleBignessFromRiemannRoch

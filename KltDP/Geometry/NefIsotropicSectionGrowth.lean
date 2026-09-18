import KltDP.Geometry.RiemannRochEffectiveMultiple

/-!
# Unbounded actual section dimensions for a nef isotropic divisor

If the original nef Cartier divisor A has A²=0 and K.A<0, every
complementary section space O(K-nA) vanishes by its negative intersection
with A. Full RR gives the linear lower bound -n(A.K)/2+χ(O). Its positive
integral slope makes the actual h⁰ dimensions unbounded, beyond any
requested lower bound on n. The original H0-to-sections comparison then
produces actual independent global sections over the original base field.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.ModuleCohomology KltDP.Geometry.SurfaceRiemannRochSource
open KltDP.Geometry.SmoothCanonicalCartierRepresentative

universe u

namespace KltDP.Geometry.NefIsotropicSectionGrowth

private theorem exists_linear_bound (b z : ℤ) (hb : b < 0) (r N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      (r : ℚ) ≤ -((b : ℚ) * (n : ℚ)) / 2 + (z : ℚ) := by
  obtain ⟨M, hM⟩ := exists_nat_ge (2 * ((r : ℤ) - z))
  have hlargeZ : 2 * ((r : ℤ) - z) ≤ (max N M : ℕ) :=
    hM.trans (by exact_mod_cast (Nat.le_max_right N M))
  have hlarge : (2 : ℚ) * ((r : ℚ) - (z : ℚ)) ≤ (max N M : ℕ) := by
    exact_mod_cast hlargeZ
  have hbOne : b ≤ -1 := by omega
  have hbQ : (b : ℚ) ≤ -1 := by exact_mod_cast hbOne
  have hmul := mul_le_mul_of_nonneg_right hbQ
    (Nat.cast_nonneg (max N M) : (0 : ℚ) ≤ (max N M : ℕ))
  refine ⟨max N M, Nat.le_max_left N M, ?_⟩
  nlinarith

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- For every requested section dimension and lower bound on the power,
an actual power of the original nef isotropic Cartier divisor attains it. -/
theorem exists_hDimension_ge (K : X.WeilDivisor) (hK : IsCanonical X hregular K)
    (A : CartierDivisor X.toScheme)
    (hA : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme A))
    (hAA : intersectionPairing X hregular A A = 0)
    (hKA : intersectionPairing X hregular
      ((X.regularCartierWeilEquiv hregular).symm K) A < 0) (r N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ r ≤ hDimension X hregular (X.cartierToWeilHom (n • A)) 0 := by
  have hAK : intersectionPairing X hregular A
      ((X.regularCartierWeilEquiv hregular).symm K) < 0 := by
    rw [X.intersectionPairing_symm hregular]
    exact hKA
  obtain ⟨n, hn, hbound⟩ := exists_linear_bound
    (intersectionPairing X hregular A ((X.regularCartierWeilEquiv hregular).symm K))
    (eulerCharacteristic X.structureMorphism
      (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf)) hAK r N
  have hnegative : intersectionPairing X hregular
      ((X.regularCartierWeilEquiv hregular).symm
        (K - X.cartierToWeilHom (n • A))) A < 0 := by
    apply SurfaceRiemannRochNef.complementary_intersection_neg X hregular
      (X.cartierToWeilHom (n • A)) K A
    rw [RiemannRochEffectiveMultiple.inverse_toWeil,
      RiemannRochEffectiveMultiple.intersection_nsmul_left, hAA, mul_zero]
    exact hKA
  have hvanish := NefIntersectionSectionVanishing.sections_subsingleton X hregular
    (K - X.cartierToWeilHom (n • A)) A hA hnegative
  have hrr := AmpleBignessFromRiemannRoch.rrNumber_le_hDimension X hregular
    (X.cartierToWeilHom (n • A)) K hK hvanish
  rw [AmpleBignessFromRiemannRoch.rrNumber_nsmul, hAA, Int.cast_zero,
    zero_mul, zero_sub] at hrr
  refine ⟨n, hn, ?_⟩
  have h : (r : ℚ) ≤ (hDimension X hregular (X.cartierToWeilHom (n • A)) 0 : ℚ) :=
    hbound.trans hrr
  exact_mod_cast h

/-- The same bound yields an actual independent family of any prescribed
finite size in the original Cartier-module section space. -/
theorem exists_linearIndependent_sections (K : X.WeilDivisor) (hK : IsCanonical X hregular K)
    (A : CartierDivisor X.toScheme)
    (hA : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme A))
    (hAA : intersectionPairing X hregular A A = 0)
    (hKA : intersectionPairing X hregular
      ((X.regularCartierWeilEquiv hregular).symm K) A < 0) (r N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      letI := baseSectionsModule X.structureMorphism (cartierDivisorModule X.toScheme (n • A))
      ∃ s : Fin r → sections (cartierDivisorModule X.toScheme (n • A)),
        LinearIndependent k s := by
  obtain ⟨n, hn, hdim⟩ := exists_hDimension_ge X hregular K hK A hA hAA hKA r N
  refine ⟨n, hn, ?_⟩
  letI := baseSectionsModule X.structureMorphism (cartierDivisorModule X.toScheme (n • A))
  unfold hDimension divisorModule at hdim
  rw [RiemannRochEffectiveMultiple.inverse_toWeil,
    cohomologyDimension_zero_eq_finrank_sections] at hdim
  exact exists_linearIndependent_of_le_finrank hdim

section Smooth

variable [IsSmoothOfRelativeDimension 2 X.structureMorphism]

local instance source_isSmooth : IsSmooth X.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 X.structureMorphism

/-- The constructed canonical divisor supplies canonicality on the
original smooth projective surface, retaining only the actual nef and
intersection hypotheses of the isotropic section-growth statement. -/
theorem exists_hDimension_ge_of_constructedCanonical (A : CartierDivisor X.toScheme)
    (hA : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme A))
    (hAA : intersectionPairing X X.regularPoints_of_isSmooth A A = 0)
    (hKA : intersectionPairing X X.regularPoints_of_isSmooth
      ((X.regularCartierWeilEquiv X.regularPoints_of_isSmooth).symm (weilRepresentative X)) A < 0)
    (r N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      r ≤ hDimension X X.regularPoints_of_isSmooth (X.cartierToWeilHom (n • A)) 0 :=
  exists_hDimension_ge X X.regularPoints_of_isSmooth (weilRepresentative X)
    (SurfaceRiemannRochSource.constructedCanonical_isCanonical X) A hA hAA hKA r N

/-- Two actual independent sections occur beyond any requested bound on
the power, with no section, vanishing, or effective-divisor premise. -/
theorem exists_two_independent_sections_of_constructedCanonical (A : CartierDivisor X.toScheme)
    (hA : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme A))
    (hAA : intersectionPairing X X.regularPoints_of_isSmooth A A = 0)
    (hKA : intersectionPairing X X.regularPoints_of_isSmooth
      ((X.regularCartierWeilEquiv X.regularPoints_of_isSmooth).symm (weilRepresentative X)) A < 0)
    (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      letI := baseSectionsModule X.structureMorphism (cartierDivisorModule X.toScheme (n • A))
      ∃ s : Fin 2 → sections (cartierDivisorModule X.toScheme (n • A)),
        LinearIndependent k s :=
  exists_linearIndependent_sections X X.regularPoints_of_isSmooth (weilRepresentative X)
    (SurfaceRiemannRochSource.constructedCanonical_isCanonical X) A hA hAA hKA 2 N

end Smooth

end KltDP.Geometry.NefIsotropicSectionGrowth

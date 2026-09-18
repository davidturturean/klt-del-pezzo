import KltDP.Geometry.NefIntersectionSectionVanishing

/-!
# Vanishing of every positive Cartier multiple against an original nef class

The existing original section-to-effective-divisor argument applies to each
positive multiple. The actual H0 comparison transfers this to cohomology
dimension zero. In particular this supplies the canonical-power vanishing
needed after an actual negative canonical intersection has been constructed.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.NormalProjectiveSurface KltDP.Geometry.ModuleCohomology
universe u
namespace KltDP.Geometry.NegativeNefCartierPowers

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

theorem sections_subsingleton (D A : CartierDivisor X.toScheme)
    (hA : Positivity.IsNef X.structureMorphism (cartierDivisorInvertibleSheaf X.toScheme A))
    (hnegative : intersectionPairing X hregular D A < 0) :
    Subsingleton (sections (cartierDivisorModule X.toScheme D)) := by
  have h := NefIntersectionSectionVanishing.sections_subsingleton X hregular
    ((X.regularCartierWeilEquiv hregular) D) A hA (by simpa using hnegative)
  simpa only [AddEquiv.symm_apply_apply] using h

theorem pairing_nsmul (D A : CartierDivisor X.toScheme) (n : ℕ) :
    intersectionPairing X hregular (n • D) A =
      (n : ℤ) * intersectionPairing X hregular D A := by
  induction n with
  | zero => simp only [zero_smul, X.intersectionPairing_zero_left, Nat.cast_zero, zero_mul]
  | succ n ih =>
    rw [succ_nsmul, X.intersectionPairing_add_left, ih]
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]

/-- Every positive multiple has zero actual H0 over the original base field. -/
theorem hZero_positive_multiple_eq_zero (D A : CartierDivisor X.toScheme)
    (hA : Positivity.IsNef X.structureMorphism (cartierDivisorInvertibleSheaf X.toScheme A))
    (hnegative : intersectionPairing X hregular D A < 0) (n : ℕ) (hn : 0 < n) :
    cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme (n • D)) 0 = 0 := by
  have hneg : intersectionPairing X hregular (n • D) A < 0 := by
    rw [pairing_nsmul X hregular D A n]
    exact mul_neg_of_pos_of_neg (Nat.cast_pos.mpr hn) hnegative
  letI : Subsingleton (sections (cartierDivisorModule X.toScheme (n • D))) :=
    sections_subsingleton X hregular (n • D) A hA hneg
  letI := baseSectionsModule X.structureMorphism (cartierDivisorModule X.toScheme (n • D))
  rw [cohomologyDimension_zero_eq_finrank_sections]
  exact Module.finrank_zero_of_subsingleton

end KltDP.Geometry.NegativeNefCartierPowers
#check @KltDP.Geometry.NegativeNefCartierPowers.hZero_positive_multiple_eq_zero
#print axioms KltDP.Geometry.NegativeNefCartierPowers.hZero_positive_multiple_eq_zero

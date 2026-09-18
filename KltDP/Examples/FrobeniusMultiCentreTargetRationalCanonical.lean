import KltDP.Geometry.WeilClassRationalRelation
import KltDP.Examples.FrobeniusMultiCentreTargetCanonicalRelation

/-!
# The actual rational canonical class on the original Frobenius target

The compiled original integral target relation supplies the class identity.
The original positive exponent and n > 2 make its canonical coefficient
nonzero. The existing actual Weil-class rationalization then permits division.
The coefficient is exactly -d/(m*p*(n-2)); the original exponent is retained.
The target canonical divisor is still the independent differential-based one.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreTargetRationalCanonical

open KltDP.Geometry FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved FrobeniusMultiCentreCanonicalWeilRepresentatives
open KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
open InvertibleSheafSectionPowers

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a) (hn : 2 < n)
    (Y : NormalProjectiveSurface k)
    (π : multiSurface (q + 1) n a ⟶ Y.toScheme)
    [IsProper π] [Surjective π] [IsIso π.c]

/-- The original actual canonical divisor has the stated rational Weil class.
The relation is derived from the compiled integral theorem, not assumed. -/
theorem canonical_class_formula :
    letI : IsIntegral (multiSurface (q + 1) n a) :=
      multiSurface_isIntegral (q + 1) n a ha
    ∀ (hπ : π ≫ Y.structureMorphism = multiStructure (q + 1) n a)
      (hbir : IsBirationalScheme π)
      (hconnected : ∀ y : Y.toScheme, IsConnected (π.base ⁻¹' {y}))
      (hcriterion : ∀ C : (sourceSurface q n a ha
          (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
        (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
          C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
          C.restrictionDegree (originalLine q n a ha) = 0)
      (A : InvertibleSheaf Y.toScheme) (m : ℕ) (hm : 0 < m)
      (e : (pullbackInvertibleSheaf π A).obj ≅ (power (originalLine q n a ha) m).obj),
      let p : ℤ := (q + 1 : ℕ)
      let r : ℤ := (n : ℤ) - 2
      let d : ℤ := 2 - (p - 2) * r
      Y.weilClassRationalization
          (Y.weilClassMap (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion)) =
        (-(d : ℚ) / ((m : ℚ) * (p : ℚ) * (r : ℚ))) •
          Y.weilClassRationalization (Y.picardToWeilClassHom (Additive.ofMul A.toPic)) := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  intro hπ hbir hconnected hcriterion A m hm e
  let p : ℤ := (q + 1 : ℕ)
  let r : ℤ := (n : ℤ) - 2
  let d : ℤ := 2 - (p - 2) * r
  let c : ℤ := (m : ℤ) * p * r
  have hmZ : 0 < (m : ℤ) := by exact_mod_cast hm
  have hpZ : 0 < ((q + 1 : ℕ) : ℤ) := by exact_mod_cast (Nat.zero_lt_succ q)
  have hrZ : 0 < (n : ℤ) - 2 := by omega
  have hc : c ≠ 0 := ne_of_gt (mul_pos (mul_pos hmZ hpZ) hrZ)
  have hintegral : c •
      Y.weilClassMap (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion) +
      d • Y.picardToWeilClassHom (Additive.ofMul A.toPic) = 0 :=
    FrobeniusMultiCentreTargetCanonicalRelation.canonical_relation
      q n a ha hn Y π hπ hbir hconnected hcriterion A m e
  have h := Y.rationalization_formula_of_integral_relation c d
    (Y.weilClassMap (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion))
    (Y.picardToWeilClassHom (Additive.ofMul A.toPic)) hc hintegral
  have hcast : (c : ℚ) = (m : ℚ) * (p : ℚ) * (r : ℚ) := by
    simp only [c, Int.cast_mul, Int.cast_natCast]
  have hcoeff : -(d : ℚ) / (c : ℚ) =
      -(d : ℚ) / ((m : ℚ) * (p : ℚ) * (r : ℚ)) :=
    congrArg (fun z : ℚ => -(d : ℚ) / z) hcast
  exact h.trans (congrArg (fun z : ℚ => z •
    Y.weilClassRationalization (Y.picardToWeilClassHom (Additive.ofMul A.toPic))) hcoeff)

end KltDP.Examples.FrobeniusMultiCentreTargetRationalCanonical

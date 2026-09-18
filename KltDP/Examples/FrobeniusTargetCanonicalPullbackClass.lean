import KltDP.Geometry.QCartierPullbackLinePowerClass
import KltDP.Examples.FrobeniusMultiCentreTargetRationalCanonical
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Pull back the proved original target canonical class formula. The actual
isomorphism pi*A = M^m identifies its pulled class. The positive original
exponent m is retained until the final rational scalar cancellation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusTargetCanonicalPullbackClass

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved FrobeniusMultiCentreCanonicalWeilRepresentatives
open FrobeniusMultiCentreContractingNef FrobeniusMultiCentreSemiampleConstruction
open InvertibleSheafSectionPowers

/-- The original target canonical pullback has the prescribed source rational
class, derived from its actual positive-power line witness. -/
theorem target_canonical_pullback_class
    {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a) (hn : 2 < n)
    (Y : NormalProjectiveSurface k)
    (π : (sourceSurface q n a ha
      (originalMultiStructureProjective k (q + 1) n a)).toScheme ⟶ Y.toScheme)
    [IsProper π] [Surjective π] [IsIso π.c]
    (hπ : π ≫ Y.structureMorphism = multiStructure (q + 1) n a)
    (hbir : IsBirationalScheme π)
    (hconnected : ∀ y : Y.toScheme, IsConnected (π.base ⁻¹' {y}))
    (hcriterion : ∀ C : (sourceSurface q n a ha
        (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
        C.restrictionDegree (originalLine q n a ha) = 0)
    (A : InvertibleSheaf Y.toScheme) (m : ℕ) (hm : 0 < m)
    (e : (pullbackInvertibleSheaf π A).obj ≅ (power (originalLine q n a ha) m).obj)
    (hK : Y.QCartier (rationalizeWeilDivisor Y
      (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion))) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    let p : ℤ := (q + 1 : ℕ)
    let r : ℤ := (n : ℤ) - 2
    let d : ℤ := 2 - (p - 2) * r
    (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).rationalWeilClassMap
      (QCartierPullback.pullback
        (X := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
        (Y := Y) (π := π) (rationalizeWeilDivisor Y
          (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion)) hK) =
      (-(d : ℚ) / ((p : ℚ) * (r : ℚ))) •
        (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).rationalWeilClassMap
          (rationalizeWeilDivisor
            (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
            (contractingWeil q n a ha (originalMultiStructureProjective k (q + 1) n a))) := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  let hproj := originalMultiStructureProjective k (q + 1) n a
  let source := sourceSurface q n a ha hproj
  let p : ℤ := (q + 1 : ℕ)
  let r : ℤ := (n : ℤ) - 2
  let d : ℤ := 2 - (p - 2) * r
  let c : ℚ := -(d : ℚ) / ((m : ℚ) * (p : ℚ) * (r : ℚ))
  obtain ⟨B, ⟨eB⟩⟩ := exists_cartierDivisor_module_iso Y.toScheme A.obj
  have hBclass := Y.picardToWeilClassHom_of_module_iso A B eB
  have htarget : Y.rationalWeilClassMap (rationalizeWeilDivisor Y
        (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion)) =
      c • Y.rationalWeilClassMap (Y.rationalCartierToWeilHom B) :=
    (FrobeniusMultiCentreTargetRationalCanonical.canonical_class_formula
      q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e).trans
        (congrArg (fun v : Y.RationalWeilClassGroup => c • v)
          (congrArg Y.weilClassRationalization hBclass))
  have hpulled := QCartierPullback.rationalWeilClassMap_pullback_eq_smul_cartier
    (X := source) (Y := Y) π _ hK B c htarget
  have hpower := QCartierPullback.rational_class_signed_pullback_of_power_iso
    (X := source) (Y := Y) π (originalLine q n a ha)
    (contractingDivisor q n a ha hproj) (Iso.refl _) A B eB m e
  have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hp0 : (p : ℚ) ≠ 0 := by
    dsimp only [p]
    exact_mod_cast (Nat.succ_ne_zero q)
  have hrZ : 0 < r := by dsimp only [r]; omega
  have hr0 : (r : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hrZ)
  have hcancel : c * (m : ℚ) = -(d : ℚ) / ((p : ℚ) * (r : ℚ)) := by
    dsimp only [c]
    field_simp [hm0, hp0, hr0] <;> ring
  exact hpulled.trans ((congrArg (fun v : source.RationalWeilClassGroup => c • v) hpower).trans
    ((smul_smul c (m : ℚ) _).trans
      (congrArg (fun z : ℚ => z • source.rationalWeilClassMap
        (rationalizeWeilDivisor source (contractingWeil q n a ha hproj))) hcancel)))

end KltDP.Examples.FrobeniusTargetCanonicalPullbackClass

#check @KltDP.Examples.FrobeniusTargetCanonicalPullbackClass.target_canonical_pullback_class

import KltDP.Geometry.BirationalPicardPullbackIso
import KltDP.Geometry.FrobeniusTargetCanonicalWeil
import KltDP.Examples.FrobeniusMultiCentreCanonicalWeilRepresentatives

/-!
# The original ample-pullback witness computes m times the pushed M class

Use the actual isomorphism open already derived for the original contraction.
The established Picard pullback/pushforward theorem applies to the original
module isomorphism pi*A = M^m. Existing power and Cartier-class comparisons
identify the source term with m times the actual contracting Weil class.
The line A and natural exponent m are arbitrary; positivity is not needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreContractingWeilPullback

open KltDP.Geometry FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved FrobeniusMultiCentreContractingNef
open FrobeniusMultiCentreContractingClass FrobeniusMultiCentreCanonicalWeilRepresentatives
open KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
open InvertibleSheafSectionPowers

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a) (hn : 2 < n)
    (Y : NormalProjectiveSurface k)
    (π : multiSurface (q + 1) n a ⟶ Y.toScheme)
    [IsProper π] [Surjective π] [IsIso π.c]

include hn in
/-- The original power-line isomorphism gives the target Picard-to-Weil class
as m times the pushforward of the actual original M representative. -/
theorem contractingWeil_pullback_power :
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
      (A : InvertibleSheaf Y.toScheme) (m : ℕ)
      (e : (pullbackInvertibleSheaf π A).obj ≅ (power (originalLine q n a ha) m).obj),
      (m : ℤ) • BirationalWeilClassPushforward.pushforward
          (S := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
          (X := Y) π hbir
          ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).weilClassMap
            (contractingWeil q n a ha (originalMultiStructureProjective k (q + 1) n a))) =
        Y.picardToWeilClassHom (Additive.ofMul A.toPic) := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  intro hπ hbir hconnected hcriterion A m e
  letI : Nonempty (nullImageComplement q n a ha π).toScheme :=
    nullImageComplement_nonempty q n a ha hn Y π hcriterion
  letI : IsIso (π ∣_ nullImageComplement q n a ha π) :=
    isIso_restrict_nullImageComplement q n a ha hn Y π hπ hbir hconnected hcriterion
  have hpower : Additive.ofMul (power (originalLine q n a ha) m).toPic =
      (m : ℤ) • contractingClass q n a ha := by
    rw [power_toPic, _root_.ofMul_pow]
    simpa only [originalLine, natCast_zsmul] using
      congrArg (fun c : Additive (multiSurface (q + 1) n a).Pic => m • c)
        (contractingLine_class q n a ha (originalMultiStructureProjective k (q + 1) n a))
  have h := BirationalPicardPullbackPushforward.pushforward_of_pullback_iso
    (S := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
    (X := Y) π hbir (nullImageComplement q n a ha π)
    (fun C => genericPoint_mem_nullImageComplement q n a ha hn Y π hcriterion C)
    A (power (originalLine q n a ha) m) e
  let F : Additive (multiSurface (q + 1) n a).Pic →+ Y.WeilClassGroup :=
    (BirationalWeilClassPushforward.pushforward
      (S := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
      (X := Y) π hbir).comp
      (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).picardToWeilClassHom
  have hpowerMapped : F (Additive.ofMul (power (originalLine q n a ha) m).toPic) =
      (m : ℤ) • F (contractingClass q n a ha) :=
    (congrArg F hpower).trans (map_zsmul F _ _)
  have hrepresentative : F (contractingClass q n a ha) =
      BirationalWeilClassPushforward.pushforward
        (S := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
        (X := Y) π hbir
        ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).weilClassMap
          (contractingWeil q n a ha (originalMultiStructureProjective k (q + 1) n a))) :=
    congrArg (BirationalWeilClassPushforward.pushforward
      (S := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
      (X := Y) π hbir)
      (contracting_picardToWeil q n a ha (originalMultiStructureProjective k (q + 1) n a))
  exact (hpowerMapped.trans
    (congrArg (fun c : Y.WeilClassGroup => (m : ℤ) • c) hrepresentative)).symm.trans h

end KltDP.Examples.FrobeniusMultiCentreContractingWeilPullback

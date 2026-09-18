import KltDP.Examples.FrobeniusMultiCentreContractingWeilPullback
import KltDP.Examples.FrobeniusMultiCentreCanonicalPushforwardRelation
import KltDP.Examples.FrobeniusMultiCentreCanonicalWeilPushforward

/-!
# The actual target canonical Weil-class relation

Multiply the original pushed canonical relation by the original natural
power exponent. The original differential comparison identifies the pushed
source canonical class with the independently constructed target canonical
Weil class. The actual pullback-line isomorphism identifies m times the
pushed M class with the target line's actual Picard-to-Weil class. Neither
identification is a premise. All coefficients use integer subtraction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreTargetCanonicalRelation

open KltDP.Geometry FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved FrobeniusMultiCentreCanonicalWeilRepresentatives
open FrobeniusMultiCentreCanonicalPushforwardRelation
open FrobeniusMultiCentreCanonicalWeilPushforward FrobeniusMultiCentreContractingWeilPullback
open KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
open InvertibleSheafSectionPowers

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a) (hn : 2 < n)
    (Y : NormalProjectiveSurface k)
    (π : multiSurface (q + 1) n a ⟶ Y.toScheme)
    [IsProper π] [Surjective π] [IsIso π.c]

/-- The original contraction and original oriented pullback-power isomorphism
give the actual target canonical class relation. The natural exponent is arbitrary. -/
theorem canonical_relation :
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
      let p : ℤ := (q + 1 : ℕ)
      let r : ℤ := (n : ℤ) - 2
      let d : ℤ := 2 - (p - 2) * r
      ((m : ℤ) * p * r) •
          Y.weilClassMap (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion) +
        d • Y.picardToWeilClassHom (Additive.ofMul A.toPic) = 0 := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  intro hπ hbir hconnected hcriterion A m e
  let p : ℤ := (q + 1 : ℕ)
  let r : ℤ := (n : ℤ) - 2
  let d : ℤ := 2 - (p - 2) * r
  let cM : Y.WeilClassGroup := BirationalWeilClassPushforward.pushforward
    (S := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
    (X := Y) π hbir
    ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).weilClassMap
      (contractingWeil q n a ha (originalMultiStructureProjective k (q + 1) n a)))
  have hM : (m : ℤ) • cM = Y.picardToWeilClassHom (Additive.ofMul A.toPic) :=
    contractingWeil_pullback_power q n a ha hn Y π hπ hbir hconnected hcriterion A m e
  let cS : Y.WeilClassGroup := BirationalWeilClassPushforward.pushforward
    (S := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
    (X := Y) π hbir
    ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).weilClassMap
      (canonicalWeil q n a ha (originalMultiStructureProjective k (q + 1) n a)))
  let cK : Y.WeilClassGroup :=
    Y.weilClassMap (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion)
  let cA : Y.WeilClassGroup := Y.picardToWeilClassHom (Additive.ofMul A.toPic)
  have hK : cS = cK :=
    canonicalWeil_pushforward q n a ha hn Y π hπ hbir hconnected hcriterion
  have hsource : (p * r) • cS + d • cM = 0 :=
    original_pushforward_canonical_relation q n a ha π hπ hbir hcriterion
  have hbase : (p * r) • cK + d • cM = 0 :=
    (congrArg (fun c : Y.WeilClassGroup => (p * r) • c + d • cM) hK).symm.trans hsource
  have hfirst : ((m : ℤ) * p * r) • cK = (m : ℤ) • ((p * r) • cK) :=
    (congrArg (fun z : ℤ => z • cK) (mul_assoc (m : ℤ) p r)).trans
      (mul_zsmul cK (m : ℤ) (p * r))
  have hsecond : d • cA = (m : ℤ) • (d • cM) :=
    ((congrArg (fun c : Y.WeilClassGroup => d • c) hM.symm).trans
      (mul_zsmul' cM (m : ℤ) d).symm).trans (mul_zsmul cM (m : ℤ) d)
  have hsum : ((m : ℤ) * p * r) • cK + d • cA =
      (m : ℤ) • ((p * r) • cK + d • cM) :=
    (congrArg₂ (fun x y : Y.WeilClassGroup => x + y) hfirst hsecond).trans
      (zsmul_add ((p * r) • cK) (d • cM) (m : ℤ)).symm
  exact hsum.trans ((congrArg (fun c : Y.WeilClassGroup => (m : ℤ) • c) hbase).trans
    (zsmul_zero (m : ℤ)))

end KltDP.Examples.FrobeniusMultiCentreTargetCanonicalRelation

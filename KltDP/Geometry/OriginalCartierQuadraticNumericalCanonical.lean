import KltDP.Geometry.OriginalCartierQuadraticHurwitz
import KltDP.Geometry.OriginalCartierRamificationHalfLinePicard
import KltDP.Geometry.HodgeIndexReduction

/-!
# Numerical Hurwitz for the same original quadratic cover

The original Hurwitz identity and actual doubled ramification class imply
equality of twice the canonical and pulled half-branch canonical classes.
The existing integer intersection pairing then cancels two in ℤ. This
produces numerical equality without cancelling torsion in the Picard group.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.OriginalCartierRamificationSmooth

open SmoothCanonicalCartierRepresentative

private theorem double_pullback_class
    {G H : Type u} [AddCommMonoid G] [AddCommMonoid H]
    (P : G →+ H) (K L : G) (C R : H)
    (hC : C = P K + R) (hR : (2 : ℕ) • R = (2 : ℕ) • P L) :
    (2 : ℕ) • C = (2 : ℕ) • P (K + L) := by
  rw [hC]
  simp only [map_add, nsmul_add, hR]

private theorem integer_hom_eq_of_double_eq
    {G : Type u} [AddCommMonoid G] (F : G →+ ℤ) (a b : G)
    (h : (2 : ℕ) • a = (2 : ℕ) • b) : F a = F b := by
  have h' : F a + F a = F b + F b := by
    simpa only [two_nsmul, map_add] using congrArg F h
  omega

variable {k : Type u} [Field k] [IsAlgClosed k]
  (S : NormalProjectiveSurface k) [IsSmoothOfRelativeDimension 2 S.structureMorphism]

local instance numericalCanonicalSeparated : S.toScheme.IsSeparated :=
  NormalProjectiveSurface.surfaceSeparated S
local instance numericalCanonicalModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
  (L : InvertibleSheaf S.toScheme)
  (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
  (hred : IsReduced (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
  (hne : Nonempty (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
  [IsSmoothOfRelativeDimension 1
    ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism)]

local notation "A" => effectiveCartierQuadraticAtlas S.toScheme E hE L e
local notation "T" => OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne

/-- The actual canonical and pulled half-branch canonical classes agree after doubling. -/
theorem originalCartierHurwitzPicard_twice :
    letI : IsIntegral (T).toScheme := (T).integral
    letI : IsSmoothOfRelativeDimension 2 (T).structureMorphism :=
      originalCover_smoothTwo S E hE L e h2 hred hne
    (2 : ℕ) • cartierPicardHom (T).toScheme (cartierRepresentative (T).structureMorphism) =
      (2 : ℕ) • (schemePicardPullbackHom (A).morphism).toAdditive
        (cartierPicardHom S.toScheme (cartierRepresentative S.structureMorphism) +
          Additive.ofMul L.toPic) := by
  letI : IsIntegral (T).toScheme := (T).integral
  letI : IsSmoothOfRelativeDimension 2 (T).structureMorphism :=
    originalCover_smoothTwo S E hE L e h2 hred hne
  let P : Additive S.toScheme.Pic →+ Additive (T).toScheme.Pic :=
    (schemePicardPullbackHom (A).morphism).toAdditive
  let KS : Additive S.toScheme.Pic :=
    cartierPicardHom S.toScheme (cartierRepresentative S.structureMorphism)
  let KT : Additive (T).toScheme.Pic :=
    cartierPicardHom (T).toScheme (cartierRepresentative (T).structureMorphism)
  let M : Additive S.toScheme.Pic := Additive.ofMul L.toPic
  let R : Additive (T).toScheme.Pic :=
    cartierPicardHom (T).toScheme (originalRamificationDivisor S E hE L e h2 hred hne)
  have hK : KT = P KS + R := originalCartierHurwitzPicard S E hE L e h2 hred hne
  have hR : (2 : ℕ) • R = (2 : ℕ) • P M :=
    original_ramificationPicard_twice S E hE L e h2 hred hne
  exact double_pullback_class P KS M KT R hK hR

/-- Pairing with any actual Picard class cancels the doubled equality in ℤ. -/
theorem originalCartierHurwitz_picardPairing
    (hregular : ∀ y : (T).Point, RegularPoint (T).toScheme y) (q : (T).toScheme.Pic) :
    letI : IsIntegral (T).toScheme := (T).integral
    letI : IsSmoothOfRelativeDimension 2 (T).structureMorphism :=
      originalCover_smoothTwo S E hE L e h2 hred hne
    (T).picardPairing hregular
        (cartierPicardClass (T).toScheme (cartierRepresentative (T).structureMorphism)) q =
      (T).picardPairing hregular
        (schemePicardPullbackHom (A).morphism
          (cartierPicardClass S.toScheme (cartierRepresentative S.structureMorphism) * L.toPic)) q := by
  letI : IsIntegral (T).toScheme := (T).integral
  letI : IsSmoothOfRelativeDimension 2 (T).structureMorphism :=
    originalCover_smoothTwo S E hE L e h2 hred hne
  let F : Additive (T).toScheme.Pic →+ ℤ := (T).picardPairingHom hregular q
  have h := integer_hom_eq_of_double_eq F
    (cartierPicardHom (T).toScheme (cartierRepresentative (T).structureMorphism))
    ((schemePicardPullbackHom (A).morphism).toAdditive
      (cartierPicardHom S.toScheme (cartierRepresentative S.structureMorphism) +
        Additive.ofMul L.toPic))
    (originalCartierHurwitzPicard_twice S E hE L e h2 hred hne)
  exact h

/-- The original canonical self-intersection equals the self-pairing of
the original pulled canonical plus half-branch line class. -/
theorem originalCartierHurwitz_selfIntersection
    (hregular : ∀ y : (T).Point, RegularPoint (T).toScheme y) :
    letI : IsIntegral (T).toScheme := (T).integral
    letI : IsSmoothOfRelativeDimension 2 (T).structureMorphism :=
      originalCover_smoothTwo S E hE L e h2 hred hne
    let P := schemePicardPullbackHom (A).morphism
      (cartierPicardClass S.toScheme (cartierRepresentative S.structureMorphism) * L.toPic)
    (T).intersectionPairing hregular (cartierRepresentative (T).structureMorphism)
        (cartierRepresentative (T).structureMorphism) = (T).picardPairing hregular P P := by
  letI : IsIntegral (T).toScheme := (T).integral
  letI : IsSmoothOfRelativeDimension 2 (T).structureMorphism :=
    originalCover_smoothTwo S E hE L e h2 hred hne
  dsimp only
  rw [← (T).picardPairing_class hregular]
  rw [originalCartierHurwitz_picardPairing S E hE L e h2 hred hne hregular,
    (T).picardPairing_symm hregular,
    originalCartierHurwitz_picardPairing S E hE L e h2 hred hne hregular]

end KltDP.Geometry.OriginalCartierRamificationSmooth

#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.originalCartierHurwitz_picardPairing
#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.originalCartierHurwitz_selfIntersection

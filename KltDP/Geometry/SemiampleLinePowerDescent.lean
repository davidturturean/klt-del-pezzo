import KltDP.Geometry.ProperBirationalLinePowerDescent
import KltDP.Geometry.GeneratedCompleteSystemNormalSurface
import KltDP.Geometry.SemiampleProjectiveNormalPrimeCriterion
import KltDP.Geometry.PrimeCurvePointFiberFactorization

/-!
# A semiample line with the original exceptional null primes descends in power

One generated birational power supplies its actual normal projective factor.
The original degree criterion identifies exactly the original contracted primes;
the separately proved target identification and actual Picard pullback finish.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.SemiampleLinePowerDescent

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem exceptional_iff_fieldPoint_factor
    {S X : NormalProjectiveSurface k} (π : S.toScheme ⟶ X.toScheme)
    (hπ : π ≫ X.structureMorphism = S.structureMorphism) (C : S.PrimeCurve) :
    IsExceptionalCurve π C ↔ ∃ p : Spec (CommRingCat.of k) ⟶ X.toScheme,
      C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ X.structureMorphism = 𝟙 _ := by
  constructor
  · rintro ⟨x, hx⟩
    have hconstant : ∀ y ∈ (C : Set S.toScheme), π.base y = x := by
      intro y hy
      have hy' : π.base y ∈ ({x} : Set X.toScheme) :=
        hx ▸ Set.mem_image_of_mem π.base hy
      exact hy'
    obtain ⟨p, hp, hpσ, _⟩ := PrimeCurvePointFiberFactorization.exists_factor_of_constant
      S C X.structureMorphism π hπ x hconstant
    exact ⟨p, hp, hpσ⟩
  · rintro ⟨p, hp, _⟩
    have hconstant := PrimeCurvePointFiberFactorization.base_eq_on_prime_of_factor S C π p hp
    refine ⟨fieldMorphismPoint p, Set.Subset.antisymm ?_ ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hconstant x hx
    · rintro y (rfl : y = fieldMorphismPoint p)
      obtain ⟨x, hx⟩ := C.nonempty
      exact ⟨x, hx, hconstant x hx⟩

open GeneratedCompleteSystemNormalFactor InvertibleSheafSectionPowers

/-- The descended line and positive exponent are constructed from the original
semiample line, its birational complete systems, and its exact exceptional primes. -/
theorem exists_line_power
    {S X : NormalProjectiveSurface k} (π : S.toScheme ⟶ X.toScheme)
    [IsProper π] (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (hbirπ : IsBirationalScheme π) (L : InvertibleSheaf S.toScheme)
    (hsemi : Positivity.IsSemiample L)
    (hevent : KeelCompleteSystem.EventuallyBirational S.structureMorphism L)
    (hnull : ∀ C : S.PrimeCurve, C.restrictionDegree L = 0 ↔ IsExceptionalCurve π C) :
    ∃ m : ℕ, 0 < m ∧ ∃ A : InvertibleSheaf X.toScheme,
      (pullbackInvertibleSheaf π A).toPic = L.toPic ^ m := by
  obtain ⟨N, _, hN⟩ := hevent
  obtain ⟨m, hm, hmN, hG⟩ := SemiampleActualPowers.exists_globallyGenerated_power_ge L hsemi N
  obtain ⟨hpos, hbir⟩ := hN m hmN
  let Y : NormalProjectiveSurface k := normalProjectiveSurface S (power L m) hpos hG hbir
  let f : S.toScheme ⟶ Y.toScheme := fromSource S.structureMorphism (power L m) hpos hG
  letI : IsProper f := fromSource_isProper S.structureMorphism (power L m) hpos hG
  have hf : f ≫ Y.structureMorphism = S.structureMorphism :=
    fromSource_structure S.structureMorphism (power L m) hpos hG
  have hbirf : IsBirationalScheme f :=
    fromSource_isBirationalScheme S.structureMorphism (power L m) hpos hG hbir
  have hsame : ∀ C : S.PrimeCurve, IsExceptionalCurve π C ↔ IsExceptionalCurve f C := by
    intro C
    exact (hnull C).symm.trans
      ((PrimeCurveImageContraction.generatedNormal_factors_iff S C L m hm hpos hG).symm.trans
        (exceptional_iff_fieldPoint_factor f hf C).symm)
  obtain ⟨A, hA⟩ := ProperBirationalLinePowerDescent.exists_line_of_same_exceptional_curves
    π f hπ hf hbirπ hbirf hsame L
    (line S.structureMorphism (power L m) hpos hG) m
    ⟨fromSource_pullbackLineIso S.structureMorphism (power L m) hpos hG⟩
  exact ⟨m, hm, A, hA⟩

end KltDP.Geometry.SemiampleLinePowerDescent
#check @KltDP.Geometry.SemiampleLinePowerDescent.exists_line_power
#print axioms KltDP.Geometry.SemiampleLinePowerDescent.exists_line_power

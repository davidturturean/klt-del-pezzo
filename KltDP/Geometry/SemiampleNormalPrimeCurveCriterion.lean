import KltDP.Geometry.NormalFactorPrimeCurveCriterion
import KltDP.Geometry.GeneratedCompleteSystemNormalAmple
import KltDP.Geometry.SemiampleLargePower
import KltDP.Geometry.ProperSteinConnected

/-!
The actual normal factor of one generated complete system retains its
original prime-curve criterion. The exponent and explicit relative-spectrum
target are selected once; all geometric properties and the criterion are
proved for its original source map before packaging the existential result.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Geometry.PrimeCurveImageContraction

open GeneratedCompleteSystemNormalFactor InvertibleSheafSectionPowers

/-- An actual normal proper ample factor contracting exactly the original
degree-zero primes, with its original geometric and point fiber connectedness. -/
theorem exists_normal_factor_with_prime_criterion
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) (L : InvertibleSheaf X.toScheme)
    (hsemi : Positivity.IsSemiample L)
    (hevent : KeelCompleteSystem.EventuallyBirational X.structureMorphism L) :
    ∃ m : ℕ, 0 < m ∧ ∃ (Y : Scheme.{u}) (σ : Y ⟶ Spec (CommRingCat.of k)),
      IsProper σ ∧ IsNormalScheme Y ∧ ∃ hY : IsIntegral Y,
        letI : IsIntegral Y := hY
        ∃ π : X.toScheme ⟶ Y, π ≫ σ = X.structureMorphism ∧
          IsProper π ∧ Surjective π ∧ IsBirationalScheme π ∧ IsIso π.c ∧
            (∀ (K : Type u) [Field K] (q : Spec (CommRingCat.of K) ⟶ Y),
              ConnectedSpace (pullback π q : Scheme.{u})) ∧
            (∀ y : Y, IsConnected (π.base ⁻¹' {y})) ∧
            ∃ A : InvertibleSheaf Y, AmpleSerre.IsAmple A ∧
              Nonempty ((pullbackInvertibleSheaf π A).obj ≅ (power L m).obj) ∧
              ∀ C : X.PrimeCurve,
                (∃ p : Spec (CommRingCat.of k) ⟶ Y,
                  C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ σ = 𝟙 _) ↔
                C.restrictionDegree L = 0 := by
  obtain ⟨N, _, hN⟩ := hevent
  obtain ⟨m, hm, hmN, hG⟩ :=
    SemiampleActualPowers.exists_globallyGenerated_power_ge L hsemi N
  obtain ⟨hpos, hbir⟩ := hN m hmN
  letI : IsProper (structureMorphism X.structureMorphism (power L m) hpos hG) :=
    structureMorphism_isProper X.structureMorphism (power L m) hpos hG
  letI : IsLocallyNoetherian (target X.structureMorphism (power L m) hpos hG) :=
    isLocallyNoetherian_of_locallyOfFiniteType_spec
      (structureMorphism X.structureMorphism (power L m) hpos hG)
  letI : IsProper (fromSource X.structureMorphism (power L m) hpos hG) :=
    fromSource_isProper X.structureMorphism (power L m) hpos hG
  letI : IsIso (fromSource X.structureMorphism (power L m) hpos hG).c :=
    fromSource_c_isIso X.structureMorphism (power L m) hpos hG
  refine ⟨m, hm, target X.structureMorphism (power L m) hpos hG,
    structureMorphism X.structureMorphism (power L m) hpos hG,
    structureMorphism_isProper X.structureMorphism (power L m) hpos hG,
    target_isNormal X.structureMorphism (power L m) hpos hG X.normal,
    target_isIntegral X.structureMorphism (power L m) hpos hG,
    fromSource X.structureMorphism (power L m) hpos hG,
    fromSource_structure X.structureMorphism (power L m) hpos hG,
    fromSource_isProper X.structureMorphism (power L m) hpos hG,
    fromSource_surjective X.structureMorphism (power L m) hpos hG,
    fromSource_isBirationalScheme X.structureMorphism (power L m) hpos hG hbir,
    fromSource_c_isIso X.structureMorphism (power L m) hpos hG,
    ProperSteinConnected.geometrically_connected
      (fromSource X.structureMorphism (power L m) hpos hG),
    ProperSteinConnected.pointFibers_connected
      (fromSource X.structureMorphism (power L m) hpos hG),
    line X.structureMorphism (power L m) hpos hG,
    line_isAmple X.structureMorphism (power L m) hpos hG,
    ⟨fromSource_pullbackLineIso X.structureMorphism (power L m) hpos hG⟩, ?_⟩
  intro C
  exact generatedNormal_factors_iff X C L m hm hpos hG

end KltDP.Geometry.PrimeCurveImageContraction

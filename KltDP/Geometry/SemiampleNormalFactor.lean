import KltDP.Geometry.GeneratedCompleteSystemNormalAmple
import KltDP.Geometry.SemiampleLargePower

/-!
A semiample line with eventually birational original complete systems has
an actual normal proper factor. The selected target is the constructed
relative spectrum of a sufficiently large generated complete-system map.
Its original pulled image line is ample and pulls back to that same
positive power. No factorization or target-property witness is an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SemiampleNormalFactor

open GeneratedCompleteSystemNormalFactor InvertibleSheafSectionPowers

/-- Select an actual generated complete system and its normal proper
factor, retaining the original field map and positive-power line iso. -/
theorem normal_proper_ample_factor
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (L : InvertibleSheaf X)
    (hnormal : IsNormalScheme X) (hsemi : Positivity.IsSemiample L)
    (hevent : KeelCompleteSystem.EventuallyBirational f L) :
    ∃ m : ℕ, 0 < m ∧ ∃ (Y : Scheme.{u}) (σ : Y ⟶ Spec (CommRingCat.of k)),
      IsProper σ ∧ IsNormalScheme Y ∧ ∃ hY : IsIntegral Y,
        letI : IsIntegral Y := hY
        ∃ π : X ⟶ Y, π ≫ σ = f ∧ IsProper π ∧ Surjective π ∧
          IsBirationalScheme π ∧ IsIso π.c ∧
            ∃ A : InvertibleSheaf Y, AmpleSerre.IsAmple A ∧
              Nonempty ((pullbackInvertibleSheaf π A).obj ≅ (power L m).obj) := by
  obtain ⟨N, _, hN⟩ := hevent
  obtain ⟨m, hm, hmN, hG⟩ :=
    SemiampleActualPowers.exists_globallyGenerated_power_ge L hsemi N
  obtain ⟨hpos, hbir⟩ := hN m hmN
  exact ⟨m, hm, target f (power L m) hpos hG,
    structureMorphism f (power L m) hpos hG,
    structureMorphism_isProper f (power L m) hpos hG,
    target_isNormal f (power L m) hpos hG hnormal,
    target_isIntegral f (power L m) hpos hG,
    fromSource f (power L m) hpos hG,
    fromSource_structure f (power L m) hpos hG,
    fromSource_isProper f (power L m) hpos hG,
    fromSource_surjective f (power L m) hpos hG,
    fromSource_isBirationalScheme f (power L m) hpos hG hbir,
    fromSource_c_isIso f (power L m) hpos hG,
    line f (power L m) hpos hG, line_isAmple f (power L m) hpos hG,
    ⟨fromSource_pullbackLineIso f (power L m) hpos hG⟩⟩

end KltDP.Geometry.SemiampleNormalFactor

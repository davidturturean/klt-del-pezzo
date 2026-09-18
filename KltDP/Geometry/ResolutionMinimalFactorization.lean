import KltDP.Geometry.GeneralMinimalResolutionExistence
import KltDP.Geometry.ActualResolutionExceptionalCount

/-!
# Minimalization retains the original point-blowup sequence

This is the existing finite-exceptional-set induction with its original
contraction maps retained. It constructs a minimal factor of the given
resolution, rather than choosing an unrelated minimal resolution.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

/-- Every original resolution factors through a minimal one by an actual
sequence of point blowups, with the original composite preserved. -/
theorem IsResolution.exists_minimalFactorization
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}
    (hres : IsResolution S X π) :
    ∃ (T : NormalProjectiveSurface k) (b : S.toScheme ⟶ T.toScheme)
      (g : T.toScheme ⟶ X.toScheme),
      IsPointBlowupSequence S T b ∧ IsMinimalResolution T X g ∧ b ≫ g = π := by
  suffices h : ∀ (n : ℕ) (S : NormalProjectiveSurface k)
      (π : S.toScheme ⟶ X.toScheme),
      IsResolution S X π → {C : S.PrimeCurve | IsExceptionalCurve π C}.ncard = n →
      ∃ (T : NormalProjectiveSurface k) (b : S.toScheme ⟶ T.toScheme)
        (g : T.toScheme ⟶ X.toScheme),
        IsPointBlowupSequence S T b ∧ IsMinimalResolution T X g ∧ b ≫ g = π from
    h _ S π hres rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S π hres hn
    by_cases hmin : ∀ C : S.PrimeCurve,
        IsExceptionalCurve π C → ¬ IsMinusOneCurve hres.regular C
    · exact ⟨S, 𝟙 S.toScheme, π,
        IsPointBlowupSequence.of_isIso _ (by infer_instance) (Category.id_comp _),
        { toIsResolution := hres, no_minusOne_curve := hmin }, Category.id_comp _⟩
    · push_neg at hmin
      obtain ⟨E, hE, hminus⟩ := hmin
      obtain ⟨S', b, hb⟩ :=
        (GeneralResolution.contraction k).exists_contraction S hres.regular E hminus
      obtain ⟨π', hfac, hres'⟩ := hres.of_contraction (contractionUniversal k) hb hE
      have hlt : {C : S'.PrimeCurve | IsExceptionalCurve π' C}.ncard < n := by
        rw [← hn]
        exact hb.ncard_exceptionalCurves_lt_of_actualMaps hres hres' hfac hE
      obtain ⟨T, c, g, hc, hminimal, hcg⟩ := ih _ hlt S' π' hres' rfl
      obtain ⟨z, -, -, -, hpoint⟩ := hb.center
      refine ⟨T, b ≫ c, g, IsPointBlowupSequence.step b c z hpoint hc, hminimal, ?_⟩
      rw [Category.assoc, hcg, hfac]

end KltDP.Geometry

#check @KltDP.Geometry.IsResolution.exists_minimalFactorization
#print axioms KltDP.Geometry.IsResolution.exists_minimalFactorization

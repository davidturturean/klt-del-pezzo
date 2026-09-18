import KltDP.Geometry.ResolutionMinimalFactorization
import KltDP.Geometry.MinimalResolutionRegularTarget

/-!
# Minimalization induction with the actual minus-one curve retained

The finite-exceptional-set induction keeps the original contraction,
minus-one curve and factorization equation available to its step. This
allows intersection and Picard transport before forgetting these witnesses
in the abstract point-blowup sequence.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Induct along actual contractions of exceptional minus-one curves of
the given original resolution. -/
theorem IsResolution.contraction_induction
    {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}
    (hres : IsResolution S X π)
    (P : (T : NormalProjectiveSurface k) → (T.toScheme ⟶ X.toScheme) → Prop)
    (hminimal : ∀ T g, IsMinimalResolution T X g → P T g)
    (hstep : ∀ (T T' : NormalProjectiveSurface k)
      (g : T.toScheme ⟶ X.toScheme) (g' : T'.toScheme ⟶ X.toScheme)
      (hres : IsResolution T X g) (hres' : IsResolution T' X g')
      (E : T.PrimeCurve) (b : T.toScheme ⟶ T'.toScheme),
      IsExceptionalCurve g E → IsMinusOneCurve hres.regular E →
      IsContraction T T' b E → b ≫ g' = g → P T' g' → P T g) : P S π := by
  suffices h : ∀ (n : ℕ) (T : NormalProjectiveSurface k)
      (g : T.toScheme ⟶ X.toScheme),
      IsResolution T X g → {C : T.PrimeCurve | IsExceptionalCurve g C}.ncard = n →
      P T g from h _ S π hres rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro T g hres hn
      by_cases hmin : ∀ C : T.PrimeCurve,
          IsExceptionalCurve g C → ¬ IsMinusOneCurve hres.regular C
      · exact hminimal T g { toIsResolution := hres, no_minusOne_curve := hmin }
      · push_neg at hmin
        obtain ⟨E, hE, hminus⟩ := hmin
        obtain ⟨T', b, hb⟩ :=
          (GeneralResolution.contraction k).exists_contraction T hres.regular E hminus
        obtain ⟨g', hfac, hres'⟩ := hres.of_contraction (contractionUniversal k) hb hE
        have hlt : {C : T'.PrimeCurve | IsExceptionalCurve g' C}.ncard < n := by
          rw [← hn]
          exact hb.ncard_exceptionalCurves_lt_of_actualMaps hres hres' hfac hE
        exact hstep T T' g g' hres hres' E b hE hminus hb hfac
          (ih _ hlt T' g' hres' rfl)

/-- Over a regular original target the base case is an actual isomorphism;
every step still carries its original minus-one curve and contraction. -/
theorem IsResolution.regular_target_induction
    {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}
    (hres : IsResolution S X π)
    (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
    (P : NormalProjectiveSurface k → Prop)
    (hiso : ∀ (T : NormalProjectiveSurface k) (g : T.toScheme ⟶ X.toScheme),
      IsIso g → g ≫ X.structureMorphism = T.structureMorphism → P T)
    (hstep : ∀ (T T' : NormalProjectiveSurface k)
      (hT : ∀ t : T.Point, RegularPoint T.toScheme t)
      (E : T.PrimeCurve) (b : T.toScheme ⟶ T'.toScheme),
      IsMinusOneCurve hT E → IsContraction T T' b E → P T' → P T) : P S := by
  apply hres.contraction_induction (fun T _ => P T)
  · intro T g hmin
    exact hiso T g (hmin.isIso_of_target_regular hX) hmin.over_base
  · intro T T' g g' hres hres' E b hE hminus hb hfac ih
    exact hstep T T' hres.regular E b hminus hb ih

end KltDP.Geometry

#check @KltDP.Geometry.IsResolution.regular_target_induction
#print axioms KltDP.Geometry.IsResolution.regular_target_induction

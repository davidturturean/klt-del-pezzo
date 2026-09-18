import KltDP.Geometry.NoEvenIsolatedSelectionOnKltResolution
import KltDP.Geometry.GeneralMinimalResolutionExistence

/-!
# Vanishing of even isolated-node selections on actual minimal resolutions

The positive characteristic restriction supplies invertibility of two.
The original surface hypotheses construct a minimal resolution, and every
isolated minus-two selection divisible by two in its actual Picard group
is empty. Rationality and numerical identities are not input hypotheses.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

open NormalProjectiveSurface UnbranchedExceptionalBlocks

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The original Picard half-class of isolated nodes can only have empty
support in positive characteristic greater than two. -/
theorem isolated_even_selection_eq_empty
    {S X : NormalProjectiveSurface k} (π : S.toScheme ⟶ X.toScheme)
    (hmin : IsMinimalResolution S X π)
    (hDP : IsKltDelPezzo X) (hrank : X.picardRank = 1)
    (p : ℕ) [CharP k p] (hp : 2 < p)
    (N : Finset S.PrimeCurve) (hiso : IsolatedSelection π N)
    (hN : ∀ C ∈ N, IsExceptionalCurve π C)
    (hself : ∀ C ∈ N, C.selfIntersectionNumber hmin.regular = -2)
    (heven : ∃ m : Additive S.toScheme.Pic,
      letI : IsSmooth S.structureMorphism :=
        MinimalResolutionQuadraticRegular.source_isSmooth π hmin;
      S.smoothWeilClassPicardEquiv (S.weilClassMap (S.selectedPrimeWeil N)) =
        (2 : ℕ) • m) : N = ∅ := by
  classical
  have h2 : IsUnit (2 : k) := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff k p 2).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by norm_num) hp) hd
  by_contra hne
  obtain ⟨m, hm⟩ := heven
  exact no_nonempty_even_isolatedSelection_of_klt_resolution
    π hmin hDP hrank p (by omega) N hiso hN
    (Finset.nonempty_iff_ne_empty.mpr hne) hself m hm h2

/-- Every original rank-one klt del Pezzo surface in characteristic greater
than two has a constructed minimal resolution with vanishing isolated-node
code, expressed as the equivalent actual integral half-class criterion. -/
theorem exists_minimalResolution_with_no_even_isolatedNodes
    (X : NormalProjectiveSurface k) (hDP : IsKltDelPezzo X)
    (hrank : X.picardRank = 1) (p : ℕ) [CharP k p] (hp : 2 < p) :
    ∃ (S : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme)
      (hmin : IsMinimalResolution S X π),
      ∀ (N : Finset S.PrimeCurve), IsolatedSelection π N →
        (∀ C ∈ N, IsExceptionalCurve π C) →
        (∀ C ∈ N, C.selfIntersectionNumber hmin.regular = -2) →
        (∃ m : Additive S.toScheme.Pic,
          letI : IsSmooth S.structureMorphism :=
            MinimalResolutionQuadraticRegular.source_isSmooth π hmin;
          S.smoothWeilClassPicardEquiv (S.weilClassMap (S.selectedPrimeWeil N)) =
            (2 : ℕ) • m) → N = ∅ := by
  obtain ⟨S, π, hmin⟩ := GeneralResolution.exists_minimalResolution X
  exact ⟨S, π, hmin, fun N hiso hN hself heven =>
    isolated_even_selection_eq_empty π hmin hDP hrank p hp N hiso hN hself heven⟩

end KltDP.Geometry

#check @KltDP.Geometry.isolated_even_selection_eq_empty
#check @KltDP.Geometry.exists_minimalResolution_with_no_even_isolatedNodes
#print axioms KltDP.Geometry.isolated_even_selection_eq_empty
#print axioms KltDP.Geometry.exists_minimalResolution_with_no_even_isolatedNodes

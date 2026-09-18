import KltDP.Geometry.KltExceptionalSemiampleProjection
import KltDP.Geometry.PicardRankFromActualLineDescent
import KltDP.Geometry.SemiampleLinePowerDescent
import KltDP.Geometry.GeneralMinimalResolutionExistence

/-!
# The Picard rank of the original minimal klt resolution

The original exceptional projection is constructed for every ample source
line. Its original forest restriction makes it semiample; its actual power
descends to the original target. The already proved numerical rank theorem
therefore applies without a supplied descent or rank hypothesis.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}

theorem IsMinimalResolution.picardRank_eq_of_klt
    (hmin : IsMinimalResolution S X π) (hklt : IsKlt X)
    (p : ℕ) [CharP k p] (hp : 0 < p) :
    S.picardRank = X.picardRank + Nat.card (ActualExceptionalIncidence.Vertices π) := by
  letI : IsProper π := hmin.toIsResolution.isProper
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hmin.regular
  let hbir : IsBirationalScheme π :=
    (isBirational_iff_isBirationalScheme π).mp hmin.birational
  apply ActualExceptionalNumerical.picardRank_eq_of_actual_line_descent π hmin.over_base hbir
  intro H hH
  obtain ⟨n, hn, L, hclass, _, _, _, _, hdegree, hsemi, hevent⟩ :=
    hmin.exists_semiample_original_projection hklt p hp H hH
  obtain ⟨m, hm, A, hpower⟩ := SemiampleLinePowerDescent.exists_line_power
    π hmin.over_base hbir L hsemi hevent hdegree
  exact ⟨n, m, hn, hm, L, A, hclass, hpower⟩

theorem IsMinimalResolution.exceptional_card_eq_picardRank_sub_one
    (hmin : IsMinimalResolution S X π) (hklt : IsKlt X)
    (p : ℕ) [CharP k p] (hp : 0 < p) (hrank : X.picardRank = 1) :
    Nat.card (ActualExceptionalIncidence.Vertices π) = S.picardRank - 1 := by
  have h := hmin.picardRank_eq_of_klt hklt p hp
  rw [hrank] at h
  omega

/-- Existence and rank use the same original minimal resolution, with all
resolution and numerical-descent data constructed by the preceding proofs. -/
theorem exists_minimalResolution_with_picardRank
    (X : NormalProjectiveSurface k) (hklt : IsKlt X)
    (p : ℕ) [CharP k p] (hp : 0 < p) :
    ∃ (S : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme),
      IsMinimalResolution S X π ∧
        S.picardRank = X.picardRank + Nat.card (ActualExceptionalIncidence.Vertices π) := by
  obtain ⟨S, π, hmin⟩ := GeneralResolution.exists_minimalResolution X
  exact ⟨S, π, hmin, hmin.picardRank_eq_of_klt hklt p hp⟩

end KltDP.Geometry
#check @KltDP.Geometry.IsMinimalResolution.picardRank_eq_of_klt
#print axioms KltDP.Geometry.IsMinimalResolution.picardRank_eq_of_klt
#print axioms KltDP.Geometry.exists_minimalResolution_with_picardRank

import KltDP.Geometry.ContractionNumericalRank
import KltDP.Geometry.GeneralMinimalResolutionExistence
import KltDP.Geometry.RegularSurfaceSmoothLiteralUse

/-!
# Absolute minimal models by the original numerical Picard rank

Contract an actual minus-one curve whenever one exists. The proved rank
formula decreases the original finite numerical Picard rank by one, so
natural-number induction terminates. Every step retains the original curve,
its contraction and the original map. The resulting sequence ends at a
regular projective surface with no minus-one prime curve anywhere.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Absolute contraction induction, with every original exceptional curve
and contraction available to the induction step. Termination follows from
the actual numerical Picard-rank formula. -/
theorem absolute_contraction_induction (S : NormalProjectiveSurface k)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (P : (T : NormalProjectiveSurface k) →
      (∀ t : T.Point, RegularPoint T.toScheme t) → Prop)
    (hminimal : ∀ (T : NormalProjectiveSurface k)
      (hT : ∀ t : T.Point, RegularPoint T.toScheme t),
      (∀ E : T.PrimeCurve, ¬ IsMinusOneCurve hT E) → P T hT)
    (hstep : ∀ (T T' : NormalProjectiveSurface k)
      (hT : ∀ t : T.Point, RegularPoint T.toScheme t)
      (E : T.PrimeCurve) (b : T.toScheme ⟶ T'.toScheme)
      (hminus : IsMinusOneCurve hT E) (hb : IsContraction T T' b E),
      P T' hb.regular → P T hT) : P S hS := by
  classical
  suffices h : ∀ (n : ℕ) (T : NormalProjectiveSurface k)
      (hT : ∀ t : T.Point, RegularPoint T.toScheme t),
      T.picardRank = n → P T hT from h _ S hS rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro T hT hn
      by_cases hmin : ∀ E : T.PrimeCurve, ¬ IsMinusOneCurve hT E
      · exact hminimal T hT hmin
      · push_neg at hmin
        obtain ⟨E, hminus⟩ := hmin
        obtain ⟨T', b, hb⟩ :=
          (GeneralResolution.contraction k).exists_contraction T hT E hminus
        have hlt : T'.picardRank < n := by
          have hrank := hb.picardRank_eq_add_one hT hminus
          omega
        exact hstep T T' hT E b hminus hb (ih _ hlt T' hb.regular rfl)

/-- The original regular projective surface admits an actual finite
point-blowup sequence to a regular projective surface with no minus-one
curves. The original field triangle and the rank bound are retained. -/
theorem exists_absoluteMinimalModel (S : NormalProjectiveSurface k)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s) :
    ∃ (V : NormalProjectiveSurface k)
      (hV : ∀ v : V.Point, RegularPoint V.toScheme v)
      (b : S.toScheme ⟶ V.toScheme),
      IsPointBlowupSequence S V b ∧
      (∀ C : V.PrimeCurve, ¬ IsMinusOneCurve hV C) ∧
      b ≫ V.structureMorphism = S.structureMorphism ∧ V.picardRank ≤ S.picardRank := by
  apply S.absolute_contraction_induction hS
    (fun T _ => ∃ (V : NormalProjectiveSurface k)
      (hV : ∀ v : V.Point, RegularPoint V.toScheme v)
      (b : T.toScheme ⟶ V.toScheme),
      IsPointBlowupSequence T V b ∧
      (∀ C : V.PrimeCurve, ¬ IsMinusOneCurve hV C) ∧
      b ≫ V.structureMorphism = T.structureMorphism ∧ V.picardRank ≤ T.picardRank)
  · intro T hT hmin
    exact ⟨T, hT, 𝟙 T.toScheme,
      IsPointBlowupSequence.of_isIso _ (by infer_instance) (by simp),
      hmin, by simp, le_rfl⟩
  · intro T T' hT E b hminus hb ih
    obtain ⟨V, hV, g, hseq, hmin, hg, hrank⟩ := ih
    obtain ⟨z, _, _, _, hbl⟩ := hb.center
    refine ⟨V, hV, b ≫ g, IsPointBlowupSequence.step b g z hbl hseq, hmin, ?_, ?_⟩
    · rw [Category.assoc, hg, hb.over_base]
    · exact hrank.trans (by have h := hb.picardRank_eq_add_one hT hminus; omega)

/-- The same original minimal target is smooth of relative dimension two
over the original algebraically closed field. -/
theorem exists_smooth_absoluteMinimalModel (S : NormalProjectiveSurface k)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s) :
    ∃ (V : NormalProjectiveSurface k)
      (hV : ∀ v : V.Point, RegularPoint V.toScheme v)
      (b : S.toScheme ⟶ V.toScheme),
      IsPointBlowupSequence S V b ∧
      (∀ C : V.PrimeCurve, ¬ IsMinusOneCurve hV C) ∧
      b ≫ V.structureMorphism = S.structureMorphism ∧
      IsSmoothOfRelativeDimension 2 V.structureMorphism ∧ V.picardRank ≤ S.picardRank := by
  obtain ⟨V, hV, b, hseq, hmin, hover, hrank⟩ := S.exists_absoluteMinimalModel hS
  exact ⟨V, hV, b, hseq, hmin, hover,
    V.isSmoothOfRelativeDimension_two_of_regularPoints hV, hrank⟩

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.absolute_contraction_induction
#print axioms KltDP.Geometry.NormalProjectiveSurface.absolute_contraction_induction
#print axioms KltDP.Geometry.NormalProjectiveSurface.exists_absoluteMinimalModel
#print axioms KltDP.Geometry.NormalProjectiveSurface.exists_smooth_absoluteMinimalModel

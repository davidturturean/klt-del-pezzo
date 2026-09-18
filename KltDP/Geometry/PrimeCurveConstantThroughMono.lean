import KltDP.Geometry.PrimeCurveLineDegree
import KltDP.Geometry.RationalPoints
import Mathlib.Topology.Separation.Basic

/-!
# Constant original prime-curve maps descend through a monomorphism

An original closed point supplies an actual section of the curve's
structure morphism over the algebraically closed field. Evaluating at
this section and cancelling the target monomorphism gives the factor.
No target normality, properness, or Stein property is needed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.PrimeCurveImageContraction

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k) (C : X.PrimeCurve)

/-- The original integral projective prime curve has an actual point over k. -/
theorem exists_curve_section :
    ∃ s : Spec (CommRingCat.of k) ⟶ C.toScheme, s ≫ C.toSpec = 𝟙 _ := by
  obtain ⟨x, _, hx⟩ :=
    (isClosed_univ : IsClosed (Set.univ : Set C.toScheme)).exists_closed_singleton
      Set.univ_nonempty
  exact ⟨closedPointSection C.toSpec x hx, closedPointSection_over_base C.toSpec x hx⟩

/-- Factoring through the original field is detected after a target monomorphism. -/
theorem factors_iff_comp_mono {Y T : Scheme.{u}}
    (g : C.toScheme ⟶ Y) (σ : Y ⟶ Spec (CommRingCat.of k))
    (hg : g ≫ σ = C.toSpec) (i : Y ⟶ T) [Mono i]
    (τ : T ⟶ Spec (CommRingCat.of k)) (hi : i ≫ τ = σ) :
    (∃ p : Spec (CommRingCat.of k) ⟶ Y,
      g = C.toSpec ≫ p ∧ p ≫ σ = 𝟙 _) ↔
    ∃ p : Spec (CommRingCat.of k) ⟶ T,
      g ≫ i = C.toSpec ≫ p ∧ p ≫ τ = 𝟙 _ := by
  constructor
  · rintro ⟨p, hp, hpσ⟩
    refine ⟨p ≫ i, ?_, ?_⟩
    · rw [hp, Category.assoc]
    · rw [Category.assoc, hi, hpσ]
  · rintro ⟨p, hp, _⟩
    obtain ⟨s, hs⟩ := exists_curve_section X C
    have hqi : (s ≫ g) ≫ i = p := by
      rw [Category.assoc, hp, ← Category.assoc, hs, Category.id_comp]
    refine ⟨s ≫ g, ?_, ?_⟩
    · apply (cancel_mono i).mp
      rw [Category.assoc, hqi]
      exact hp
    · rw [Category.assoc, hg, hs]

end KltDP.Geometry.PrimeCurveImageContraction

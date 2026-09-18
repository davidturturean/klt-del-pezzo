import KltDP.Geometry.SplitPrimeCurveCartierPullback
import KltDP.Geometry.SelectedPairCurveIntersection

/-!
# Intersections of coherent original split curve copies

The original pullback divisor is the actual two-copy Cartier sum.
Projection computes its intersection with an actual lifted curve. When
that curve avoids the opposite copy, the selected-pair support formula
leaves exactly the intersection with the chosen copy. Thus compatible
whole-tree sheets preserve the original full intersection matrix.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.SplitPrimeCurveIntersection

open NormalProjectiveSurface SplitPrimeCurveImages SplitPrimeCurveCartierPullback

variable {k : Type u} [Field k] [IsAlgClosed k] {S T : NormalProjectiveSurface k}
    (π : T.toScheme ⟶ S.toScheme) [GenericPointPreserving π] [QuasiCompact π]
    (C D : S.PrimeCurve)
    (qC : pullback π C.inclusion ≅ C.toScheme ⨿ C.toScheme)
    (qD : pullback π D.inclusion ≅ D.toScheme ⨿ D.toScheme)
    (hS : ∀ x : S.Point, RegularPoint S.toScheme x)
    (hT : ∀ x : T.Point, RegularPoint T.toScheme x)
    (hqC : qC.hom ≫ coprod.desc (𝟙 C.toScheme) (𝟙 C.toScheme) = pullback.snd π C.inclusion)
    (hπ : π ≫ S.structureMorphism = T.structureMorphism)

include hqC hπ in
/-- Chosen copies retain the original intersection if the opposite target copy is disjoint. -/
theorem copyCurve_intersectionNumber (ε δ : Bool)
    (hdisj : Disjoint (copyCurve (T := T) π C qC ε : Set T.toScheme)
      (copyCurve (T := T) π D qD (!δ) : Set T.toScheme)) :
    (copyCurve (T := T) π C qC ε).intersectionNumber
      (T.primeCurveCartier hT (copyCurve (T := T) π D qD δ)) =
        C.intersectionNumber (S.primeCurveCartier hS D) := by
  classical
  letI := T.stalks_uniqueFactorizationMonoid_of_regular hT
  have hp := PrimeCurveCartierProjectionCases.intersectionNumber_pullbackDivisor_eq_of_isoFactor
    (copyCurve (T := T) π C qC ε) C π (copyCurveSourceIso (T := T) π C qC ε).hom
    (copyCurveSourceIso_hom_toBase π C qC hqC ε).symm
    (copyCurveSourceIso_hom_toSpec π C qC hqC hπ ε)
    (S.primeCurveCartier hS D) (S.primeCurveCartier_hasRegularEquations hS D)
  rw [pullback_primeCurveCartier_eq_selected π D qD hS hT] at hp
  have hne : copyCurve (T := T) π D qD δ ≠ copyCurve (T := T) π D qD (!δ) := by
    cases δ
    · exact copyCurve_false_ne_true π D qD
    · exact (copyCurve_false_ne_true π D qD).symm
  have hpair : copyCurves (T := T) π D qD =
      {copyCurve (T := T) π D qD δ, copyCurve (T := T) π D qD (!δ)} := by
    cases δ <;> simp only [copyCurves, Bool.not_false, Bool.not_true, Finset.pair_comm]
  have hselected := T.selectedPrimeCartier_weil (copyCurves (T := T) π D qD)
  rw [hpair] at hselected
  have hintersection := T.intersectionNumber_selected_pair_of_disjoint hT
    (copyCurve (T := T) π C qC ε) (copyCurve (T := T) π D qD δ)
    (copyCurve (T := T) π D qD (!δ)) hne hdisj
    (T.selectedPrimeCartier (copyCurves (T := T) π D qD)) (by simpa only [hpair] using hselected)
  exact hintersection.symm.trans hp

end KltDP.Geometry.SplitPrimeCurveIntersection

#print axioms KltDP.Geometry.SplitPrimeCurveIntersection.copyCurve_intersectionNumber

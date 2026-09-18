import KltDP.Geometry.KltMinimalResolutionGeometry
import KltDP.Geometry.ActualExceptionalNoTriple
import KltDP.Geometry.PrimeCurveIntersectionOneSNC

/-!
# Original exceptional double points from the actual klt surface

Actual minimality, the original all-model klt property, and the remaining
exceptional rationality input now imply the no-triple condition and the
existing local strict-normal-crossings equation at every double point.
Canonical choices, original discrepancy coefficients, all matrix bounds,
and local transversality are produced by the preceding proof chain.
The full reduced exceptional union still needs the local union equation
identified with these original prime-curve factors.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k}
  [IsSmoothOfRelativeDimension 2 S.structureMorphism]
  {π : S.toScheme ⟶ X.toScheme} (hmin : IsMinimalResolution S X π)
  (hklt : IsKlt X)
  (hrational : ∀ C : S.PrimeCurve, IsExceptionalCurve π C →
    ∃ e : C.toScheme ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec)

include hmin hklt hrational

/-- Three distinct original exceptional primes cannot pass through one
original surface point, without any supplied graph or coefficient data. -/
theorem IsMinimalResolution.no_three_exceptional_of_klt
    (C D E : S.PrimeCurve) (hC : IsExceptionalCurve π C)
    (hD : IsExceptionalCurve π D) (hE : IsExceptionalCurve π E)
    (x : S.toScheme) (hxC : x ∈ (C : Set S.toScheme))
    (hxD : x ∈ (D : Set S.toScheme)) (hxE : x ∈ (E : Set S.toScheme)) :
    C = D ∨ C = E ∨ D = E := by
  have hG := (hmin.exceptional_forest_and_singular_count_of_klt hklt hrational).2.2.1
  have h := KltDP.Topology.no_three_of_incidence_isAcyclic
    (fun F : ActualExceptionalIncidence.Vertices π => (F.val : Set S.toScheme))
    hG ⟨C, hC⟩ ⟨D, hD⟩ ⟨E, hE⟩ x hxC hxD hxE
  simpa only [Subtype.mk.injEq] using h

/-- Every product of the original local Cartier equations of two distinct
exceptional curves is an SNC equation at their actual common point. -/
theorem IsMinimalResolution.exceptional_double_equation_snc_of_klt
    (C D : S.PrimeCurve) (hC : IsExceptionalCurve π C) (hD : IsExceptionalCurve π D)
    (hCD : C ≠ D) (x : S.toScheme)
    (hxC : x ∈ (C : Set S.toScheme)) (hxD : x ∈ (D : Set S.toScheme))
    (c : RegularCartierEquationChart S.toScheme (S.primeCurveCartier hmin.regular C))
    (hc : x ∈ c.chart.openSet)
    (d : RegularCartierEquationChart S.toScheme (S.primeCurveCartier hmin.regular D))
    (hd : x ∈ d.chart.openSet) :
    IsStrictNormalCrossingsEquation (S.toScheme.presheaf.stalk x)
      (S.toScheme.presheaf.germ c.chart.openSet x hc c.coefficient *
        S.toScheme.presheaf.germ d.chart.openSet x hd d.coefficient) := by
  obtain ⟨e, he⟩ := hrational C hC
  letI := smoothOne_of_projectiveLineIso C.toSpec e he
  letI : IsSmooth C.toSpec := IsSmoothOfRelativeDimension.isSmooth 1 C.toSpec
  have hpair := (hmin.exceptional_forest_and_singular_count_of_klt hklt hrational).2.2.2
    (⟨C, hC⟩ : ActualExceptionalIncidence.Vertices π) ⟨D, hD⟩
    (fun h => hCD (congrArg Subtype.val h))
  exact PrimeCurveIntersectionOneSNC.product_isStrictNormalCrossingsEquation_of_pairing_le_one
    S hmin.regular C D hCD hpair x hxC hxD c hc d hd

end KltDP.Geometry

#print axioms KltDP.Geometry.IsMinimalResolution.no_three_exceptional_of_klt
#print axioms KltDP.Geometry.IsMinimalResolution.exceptional_double_equation_snc_of_klt

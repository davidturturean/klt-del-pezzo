import KltDP.Geometry.ActualExceptionalForest
import KltDP.Geometry.KltOriginalDiscrepancyBound
import KltDP.Geometry.MinimalResolutionDiscrepancy
import KltDP.Geometry.RationalWeilIntersectionFamily
import KltDP.Geometry.CompatibleRationalAdjunctionDegree

/-!
# The original minimal-resolution incidence forest from actual klt data

The original compatible canonical difference supplies all coefficients.
The all-normal-model klt predicate gives the strict lower bound; minimality,
actual rational exceptional curves, and Stieltjes give nonpositivity. The
literal original matrix rows are derived from original divisor intersection
and rational adjunction. The finite family is all actual contracted primes.

Thus graph acyclicity and distinct-prime intersection at most one have no
supplied coefficient, matrix, row, support, or forest hypotheses. The actual
projective-line isomorphisms remain explicit: this file does not assert the
still-missing general rationality theorem for klt exceptional curves.
The strict-negativity route retains the selected isolated Hodge dependency.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix

universe u

namespace KltDP.Geometry.KltMinimalResolutionForest

open NormalProjectiveSurface NormalModelCanonical

/-- Actual klt and minimality data produce the original exceptional forest
and the original distinct-prime intersection bound. Every numerical input
of the finite forest theorem is derived in this proof. -/
theorem forest_and_intersection_le_one
    {k : Type u} [Field k] [IsAlgClosed k]
    (S X : NormalProjectiveSurface k)
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    (π : S.toScheme ⟶ X.toScheme) (hmin : IsMinimalResolution S X π)
    (KS : CartierDivisor S.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2)
    (KX : X.WeilDivisor) (hklt : IsKltWithCanonicalDivisor X KX)
    (hrational : ∀ C : S.PrimeCurve, IsExceptionalCurve π C →
      ∃ e : C.toScheme ≅ projectiveSpace k 1,
        e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec) :
    letI : IsProper π := hmin.toIsResolution.isProper
    let hbir : IsBirationalScheme π :=
      (isBirational_iff_isBirationalScheme π).mp hmin.birational
    BirationalWeilPushforward.pushforward π hbir (S.cartierToWeilHom KS) = KX →
      (ActualExceptionalIncidence.graph π).IsAcyclic ∧
        ∀ C D : ActualExceptionalIncidence.Vertices π, C ≠ D →
          S.intersectionPairing hmin.regular
            (S.primeCurveCartier hmin.regular C.val)
            (S.primeCurveCartier hmin.regular D.val) ≤ 1 := by
  classical
  letI : IsProper π := hmin.toIsResolution.isProper
  let hbir : IsBirationalScheme π :=
    (isBirational_iff_isBirationalScheme π).mp hmin.birational
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  dsimp only
  intro hpush
  letI : Fintype (ActualExceptionalIncidence.Vertices π) :=
    (exceptionalCurves_finite_of_proper_birational π hbir).fintype
  let Δ : S.RationalWeilDivisor := S.rationalCartierToWeilHom KS -
    QCartierPullback.pullback π (rationalizeWeilDivisor X KX) hklt.2.1
  let C : ActualExceptionalIncidence.Vertices π → S.PrimeCurve := Subtype.val
  let d : ActualExceptionalIncidence.Vertices π → ℚ := fun i => Δ (C i)
  have hlower (i : ActualExceptionalIncidence.Vertices π) : -1 < d i :=
    KltOriginalDiscrepancyBound.coefficient_gt_neg_one S X π hbir hmin.over_base
      KS eKS KX hklt hpush (C i)
  have hupper (i : ActualExceptionalIncidence.Vertices π) : d i ≤ 0 :=
    MinimalResolutionDiscrepancy.coefficient_nonpos S X π hmin KS eKS KX
      hklt.2.1 hrational hpush (C i)
  have hrow : NullCurveIntersectionMatrix.intersectionMatrix S hmin.regular C *ᵥ d =
      fun i => -NullCurveIntersectionMatrix.intersectionMatrix S hmin.regular C i i - 2 := by
    funext i
    have hri := RationalWeilIntersection.intersectionMatrix_mulVec_compatible_difference
      hmin.regular π hbir hmin.over_base KS KX hklt.2.1 hpush
      C Subtype.val_injective (fun E => E.property)
      (fun E hE => ⟨⟨E, hE⟩, rfl⟩) i
    change (NullCurveIntersectionMatrix.intersectionMatrix S hmin.regular C *ᵥ d) i =
      -NullCurveIntersectionMatrix.intersectionMatrix S hmin.regular C i i - 2
    rw [hri]
    obtain ⟨e, he⟩ := hrational (C i) i.property
    have hadj := CompatibleRationalAdjunctionDegree.canonical_intersection_eq
      S hmin.regular KS eKS (C i) e he
    change ((C i).intersectionNumber KS : ℚ) =
      -(S.intersectionPairing hmin.regular
        (S.primeCurveCartier hmin.regular (C i))
        (S.primeCurveCartier hmin.regular (C i)) : ℚ) - 2
    rw [S.intersectionPairing_primeCurve hmin.regular]
    exact_mod_cast hadj
  exact ActualExceptionalForest.forest_and_intersection_le_one
    π hmin.over_base hbir hmin.regular C Subtype.val_injective
    (fun E => E.property) d hlower hupper hrow

end KltDP.Geometry.KltMinimalResolutionForest

#print axioms KltDP.Geometry.KltMinimalResolutionForest.forest_and_intersection_le_one

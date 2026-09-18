import KltDP.Geometry.KltMinimalResolutionGeometry
import KltDP.Geometry.ActualExceptionalGraphMatrix

/-!
# The weighted canonical graph of the actual minimal resolution

The graph uses every original contracted prime and its actual intersections.
Its weights are minus the original diagonal intersections. Actual minimality
and rational exceptional curves give weights at least two. The target's klt
property and the produced compatible canonical divisor supply a coefficient
vector in [0,1) satisfying the actual graph's canonical equation. Its matrix
is positive definite by the original proper birational geometry.

No graph realization, weight, coefficient vector, matrix equation, or positivity
is an input. Resolution existence and exceptional rationality remain separate;
the selected isolated Hodge dependency remains visible.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory Matrix
universe u

namespace KltDP.Geometry

open NormalProjectiveSurface

/-- All numerical data of the actual weighted exceptional graph are produced
from the actual klt surface, minimal map, and rational exceptional curves. -/
theorem IsMinimalResolution.exists_weighted_canonical_graph_coefficients
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k}
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    {π : S.toScheme ⟶ X.toScheme} (hmin : IsMinimalResolution S X π)
    (hklt : IsKlt X)
    (hrational : ∀ C : S.PrimeCurve, IsExceptionalCurve π C →
      ∃ e : C.toScheme ≅ projectiveSpace k 1,
        e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec) :
    letI : Fintype (ActualExceptionalIncidence.Vertices π) :=
      hmin.toIsResolution.exceptionalCurves_finite_of_actualMap.fintype
    letI : DecidableEq (ActualExceptionalIncidence.Vertices π) := Classical.decEq _
    letI : DecidableRel (ActualExceptionalIncidence.graph π).Adj := Classical.decRel _
    let M := NullCurveIntersectionMatrix.intersectionMatrix S hmin.regular
      (fun C : ActualExceptionalIncidence.Vertices π => C.val)
    let w := fun i => -M i i
    let B := KltDP.LinearAlgebra.graphWeightMatrix (ActualExceptionalIncidence.graph π) w
    (∀ i, 2 ≤ w i) ∧ B.PosDef ∧
      ∃ a : ActualExceptionalIncidence.Vertices π → ℚ,
        (∀ i, 0 ≤ a i ∧ a i < 1) ∧ B *ᵥ a = fun i => w i - 2 := by
  classical
  letI : IsProper π := hmin.toIsResolution.isProper
  let hbir : IsBirationalScheme π :=
    (isBirational_iff_isBirationalScheme π).mp hmin.birational
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  letI : Fintype (ActualExceptionalIncidence.Vertices π) :=
    hmin.toIsResolution.exceptionalCurves_finite_of_actualMap.fintype
  letI : DecidableEq (ActualExceptionalIncidence.Vertices π) := Classical.decEq _
  letI : DecidableRel (ActualExceptionalIncidence.graph π).Adj := Classical.decRel _
  dsimp only
  let C : ActualExceptionalIncidence.Vertices π → S.PrimeCurve := Subtype.val
  let M := NullCurveIntersectionMatrix.intersectionMatrix S hmin.regular C
  let w := fun i => -M i i
  let B := KltDP.LinearAlgebra.graphWeightMatrix (ActualExceptionalIncidence.graph π) w
  change (∀ i, 2 ≤ w i) ∧ B.PosDef ∧
    ∃ a : ActualExceptionalIncidence.Vertices π → ℚ,
      (∀ i, 0 ≤ a i ∧ a i < 1) ∧ B *ᵥ a = fun i => w i - 2
  obtain ⟨KX, hKX⟩ := hklt
  obtain ⟨KS, ⟨eKS⟩, hpush⟩ :=
    IsCanonicalWeilDivisor.exists_compatible_canonical_cartier
      S X π hmin.over_base hbir KX hKX.1
  let Δ : S.RationalWeilDivisor := S.rationalCartierToWeilHom KS -
    QCartierPullback.pullback π (rationalizeWeilDivisor X KX) hKX.2.1
  let d : ActualExceptionalIncidence.Vertices π → ℚ := fun i => Δ (C i)
  have hlower (i : ActualExceptionalIncidence.Vertices π) : -1 < d i :=
    KltOriginalDiscrepancyBound.coefficient_gt_neg_one S X π hbir hmin.over_base
      KS eKS KX hKX hpush (C i)
  have hupper (i : ActualExceptionalIncidence.Vertices π) : d i ≤ 0 :=
    MinimalResolutionDiscrepancy.coefficient_nonpos S X π hmin KS eKS KX
      hKX.2.1 hrational hpush (C i)
  have hrow : M *ᵥ d = fun i => w i - 2 := by
    funext i
    have hri := RationalWeilIntersection.intersectionMatrix_mulVec_compatible_difference
      hmin.regular π hbir hmin.over_base KS KX hKX.2.1 hpush
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
  have hB : -M = B :=
    ActualExceptionalGraphMatrix.negativeIntersectionMatrix_eq_graphWeightMatrix
      π hmin.over_base hbir hmin.regular C Subtype.val_injective
      (fun E => E.property) d hlower hupper hrow
  refine ⟨?_, ?_, -d, ?_, ?_⟩
  · intro i
    obtain ⟨e, he⟩ := hrational (C i) i.property
    have hneg := hmin.rational_exceptional_selfIntersection_le_neg_two
      (C i) i.property e he
    change (2 : ℚ) ≤ -(S.intersectionPairing hmin.regular
      (S.primeCurveCartier hmin.regular (C i))
      (S.primeCurveCartier hmin.regular (C i)) : ℚ)
    rw [S.intersectionPairing_primeCurve hmin.regular]
    exact_mod_cast (by omega : (2 : ℤ) ≤ -(C i).selfIntersectionNumber hmin.regular)
  · rw [← hB]
    exact ActualExceptionalStieltjes.negativeIntersectionMatrix_posDef
      π hmin.over_base hbir hmin.regular C Subtype.val_injective (fun E => E.property)
  · intro i
    change 0 ≤ -d i ∧ -d i < 1
    constructor <;> linarith only [hlower i, hupper i]
  · rw [← hB, Matrix.neg_mulVec, Matrix.mulVec_neg, neg_neg]
    exact hrow

end KltDP.Geometry

#check @KltDP.Geometry.IsMinimalResolution.exists_weighted_canonical_graph_coefficients
#print axioms KltDP.Geometry.IsMinimalResolution.exists_weighted_canonical_graph_coefficients

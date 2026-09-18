import KltDP.Geometry.KltMinimalResolutionForest
import KltDP.Geometry.MinimalResolutionSingularCount
import KltDP.Geometry.CanonicalWeilBirationalRepresentative

/-!
# Exceptional forest and exact singular count from the actual klt surface

The target's all-normal-model klt property provides a genuine canonical Weil
divisor. The proved original birational canonical comparison constructs the
source Cartier divisor, its exterior-square isomorphism, and exact pushforward.
The original minimal-resolution forest and count theorems then apply.

No canonical representative, compatibility equation, coefficient bounds, graph
axioms, or singular count is supplied. An actual minimal resolution, smooth
source, and actual exceptional projective-line isomorphisms are still inputs;
general resolution existence and exceptional rationality are separate work.
The selected Hodge and Stein literature dependencies are retained.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

/-- Original-map geometry and exact counting, with all canonical choices and
numerical discrepancy inputs produced from the actual klt surface. -/
theorem IsMinimalResolution.exceptional_forest_and_singular_count_of_klt
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k}
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    {π : S.toScheme ⟶ X.toScheme} (hmin : IsMinimalResolution S X π)
    (hklt : IsKlt X)
    (hrational : ∀ C : S.PrimeCurve, IsExceptionalCurve π C →
      ∃ e : C.toScheme ≅ projectiveSpace k 1,
        e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec) :
    Finite (ActualExceptionalIncidence.graph π).ConnectedComponent ∧
      X.singularPoints.card =
        Nat.card (ActualExceptionalIncidence.graph π).ConnectedComponent ∧
      (ActualExceptionalIncidence.graph π).IsAcyclic ∧
      ∀ C D : ActualExceptionalIncidence.Vertices π, C ≠ D →
        S.intersectionPairing hmin.regular
          (S.primeCurveCartier hmin.regular C.val)
          (S.primeCurveCartier hmin.regular D.val) ≤ 1 := by
  letI : IsProper π := hmin.toIsResolution.isProper
  let hbir : IsBirationalScheme π :=
    (isBirational_iff_isBirationalScheme π).mp hmin.birational
  obtain ⟨KX, hKX⟩ := hklt
  obtain ⟨KS, ⟨eKS⟩, hpush⟩ :=
    IsCanonicalWeilDivisor.exists_compatible_canonical_cartier
      S X π hmin.over_base hbir KX hKX.1
  obtain ⟨hfinite, hcount⟩ :=
    hmin.singularPoints_card_eq_graph_components KS eKS KX hKX.1 hKX.2.1 hrational hpush
  have hforest := KltMinimalResolutionForest.forest_and_intersection_le_one
    S X π hmin KS eKS KX hKX hrational hpush
  exact ⟨hfinite, hcount, hforest⟩

end KltDP.Geometry

#check @KltDP.Geometry.IsMinimalResolution.exceptional_forest_and_singular_count_of_klt
#print axioms KltDP.Geometry.IsMinimalResolution.exceptional_forest_and_singular_count_of_klt

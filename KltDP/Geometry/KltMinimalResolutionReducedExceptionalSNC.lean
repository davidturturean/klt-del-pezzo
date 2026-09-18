import KltDP.Geometry.KltMinimalResolutionGeometry
import KltDP.Geometry.ActualExceptionalNoTriple
import KltDP.Geometry.FiniteSmoothCurveSumSNC

/-!
# The original reduced exceptional Cartier sum is globally SNC

Finiteness is derived for all actual exceptional prime curves. The original
klt surface produces its actual incidence forest and intersection bounds;
the remaining actual projective-line isomorphisms produce smoothness.
The finite sum of their original prime Cartier divisors then satisfies
the existing global strict-normal-crossings predicate on the original
resolution surface, including its generic and closed points.

No finite enumeration, canonical choice, discrepancy row, graph, crossing,
or SNC assumption is supplied. General minimal-resolution existence and
exceptional rationality remain explicit frontiers. The selected Hodge and
Stein dependencies of the preceding geometry producer remain isolated.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

/-- The actual all-exceptional reduced Cartier divisor is SNC, from the
actual klt surface, minimal resolution, and exceptional rationality. -/
theorem IsMinimalResolution.reduced_exceptional_cartier_snc_of_klt
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k}
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    {π : S.toScheme ⟶ X.toScheme} (hmin : IsMinimalResolution S X π)
    (hklt : IsKlt X)
    (hrational : ∀ C : S.PrimeCurve, IsExceptionalCurve π C →
      ∃ e : C.toScheme ≅ projectiveSpace k 1,
        e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec) :
    letI : IsProper π := hmin.toIsResolution.isProper
    let hbir : IsBirationalScheme π :=
      (isBirational_iff_isBirationalScheme π).mp hmin.birational
    letI : Fintype (ActualExceptionalIncidence.Vertices π) :=
      (exceptionalCurves_finite_of_proper_birational π hbir).fintype
    letI : IsLocallyNoetherian S.toScheme := S.isLocallyNoetherian
    IsStrictNormalCrossingsCartier S.toScheme
      (∑ C : ActualExceptionalIncidence.Vertices π, S.primeCurveCartier hmin.regular C.val) := by
  classical
  letI : IsProper π := hmin.toIsResolution.isProper
  let hbir : IsBirationalScheme π :=
    (isBirational_iff_isBirationalScheme π).mp hmin.birational
  letI : Fintype (ActualExceptionalIncidence.Vertices π) :=
    (exceptionalCurves_finite_of_proper_birational π hbir).fintype
  letI : IsLocallyNoetherian S.toScheme := S.isLocallyNoetherian
  letI : ∀ C : ActualExceptionalIncidence.Vertices π, IsSmooth C.val.toSpec := fun C => by
    obtain ⟨e, he⟩ := hrational C.val C.property
    letI := smoothOne_of_projectiveLineIso C.val.toSpec e he
    exact IsSmoothOfRelativeDimension.isSmooth 1 C.val.toSpec
  have hgeom := hmin.exceptional_forest_and_singular_count_of_klt hklt hrational
  apply finite_smooth_primeCurve_sum_isStrictNormalCrossings S hmin.regular
    (fun C : ActualExceptionalIncidence.Vertices π => C.val) Subtype.val_injective hgeom.2.2.2
  intro C D E x hxC hxD hxE
  exact KltDP.Topology.no_three_of_incidence_isAcyclic
    (fun F : ActualExceptionalIncidence.Vertices π => (F.val : Set S.toScheme))
    hgeom.2.2.1 C D E x hxC hxD hxE

end KltDP.Geometry

#print axioms KltDP.Geometry.IsMinimalResolution.reduced_exceptional_cartier_snc_of_klt

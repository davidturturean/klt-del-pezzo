import KltDP.Geometry.GeneralMinimalResolutionExistence
import KltDP.Geometry.KltMinimalResolutionAutomaticGeometry

/-!
# Constructed minimal resolutions with klt exceptional geometry

All existence, exceptional-curve rationality, source smoothness, forest,
singular-count and weighted-matrix inputs are derived from the original
klt normal projective surface. No Picard-rank equality or global
rationality of the surface is asserted here.
-/
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry

/-- A constructed minimal resolution has the original rational exceptional
forest and its actual connected components count the target singular points. -/
theorem exists_minimalResolution_with_exceptional_geometry
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) (hklt : IsKlt X) :
    ∃ (S : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme)
      (hmin : IsMinimalResolution S X π),
      (∀ (C : S.PrimeCurve), IsExceptionalCurve π C →
        ∃ e : C.toScheme ≅ projectiveSpace k 1,
          e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec) ∧
      Finite (ActualExceptionalIncidence.graph π).ConnectedComponent ∧
      X.singularPoints.card =
        Nat.card (ActualExceptionalIncidence.graph π).ConnectedComponent ∧
      (ActualExceptionalIncidence.graph π).IsAcyclic ∧
      ∀ C D : ActualExceptionalIncidence.Vertices π, C ≠ D →
        S.intersectionPairing hmin.regular
          (S.primeCurveCartier hmin.regular C.val)
          (S.primeCurveCartier hmin.regular D.val) ≤ 1 := by
  obtain ⟨S, π, hmin⟩ := GeneralResolution.exists_minimalResolution X
  exact ⟨S, π, hmin,
    hmin.toIsResolution.exceptional_projectiveLine_iso_of_klt hklt,
    hmin.exceptional_forest_and_singular_count_from_klt hklt⟩

/-- The same general construction supplies an actual positive weighted
exceptional graph and canonical discrepancy coefficients in [0,1). -/
theorem exists_minimalResolution_with_weighted_graph
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) (hklt : IsKlt X) :
    ∃ (S : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme)
      (hmin : IsMinimalResolution S X π),
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
          (∀ i, 0 ≤ a i ∧ a i < 1) ∧ Matrix.mulVec B a = fun i => w i - 2 := by
  obtain ⟨S, π, hmin⟩ := GeneralResolution.exists_minimalResolution X
  exact ⟨S, π, hmin, hmin.exists_weighted_canonical_graph_coefficients_of_klt hklt⟩

end KltDP.Geometry
#check @KltDP.Geometry.exists_minimalResolution_with_exceptional_geometry
#print axioms KltDP.Geometry.exists_minimalResolution_with_exceptional_geometry
#print axioms KltDP.Geometry.exists_minimalResolution_with_weighted_graph

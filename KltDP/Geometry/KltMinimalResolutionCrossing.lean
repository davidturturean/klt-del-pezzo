import KltDP.Geometry.KltMinimalResolutionGeometry
import KltDP.Geometry.PrimeCurveIntersectionOneCrossing

/-!
# Actual klt exceptional curves cross in the original local rings

The original-map forest producer derives the intersection bound and all
canonical compatibility data from `IsKlt X`. Actual projective-line
isomorphisms derive smoothness; the local-length producer derives the
original ambient maximal-ideal sum. No canonical, transversality, degree,
matrix, or discrepancy input remains. General exceptional rationality
remains the explicit geometric frontier; Hodge and Stein dependencies of
the selected original-map geometry producer remain isolated as recorded.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace KltDP.Geometry.KltMinimalResolutionCrossing

/-- From the actual klt surface and its original minimal resolution, every
two distinct rational exceptional primes have the original crossing ideals. -/
theorem vanishingIdeal_sup_eq_maximalIdeal
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k}
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    {π : S.toScheme ⟶ X.toScheme} (hmin : IsMinimalResolution S X π)
    (hklt : IsKlt X)
    (hrational : ∀ C : S.PrimeCurve, IsExceptionalCurve π C →
      ∃ e : C.toScheme ≅ projectiveSpace k 1,
        e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec)
    (C D : S.PrimeCurve) (hC : IsExceptionalCurve π C) (hD : IsExceptionalCurve π D)
    (hCD : C ≠ D) (y : C.toScheme) (hyD : C.inclusion.base y ∈ (D : Set S.toScheme))
    (U : S.toScheme.affineOpens) (hyU : C.inclusion.base y ∈ U.1) :
    (C.vanishingIdeal.ideal U).map
        (S.toScheme.presheaf.germ U.1 (C.inclusion.base y) hyU).hom ⊔
      (D.vanishingIdeal.ideal U).map
        (S.toScheme.presheaf.germ U.1 (C.inclusion.base y) hyU).hom =
      maximalIdeal (S.toScheme.presheaf.stalk (C.inclusion.base y)) := by
  obtain ⟨e, he⟩ := hrational C hC
  letI := smoothOne_of_projectiveLineIso C.toSpec e he
  letI : IsSmooth C.toSpec := IsSmoothOfRelativeDimension.isSmooth 1 C.toSpec
  have hpair := (hmin.exceptional_forest_and_singular_count_of_klt hklt hrational).2.2.2
    (⟨C, hC⟩ : ActualExceptionalIncidence.Vertices π) ⟨D, hD⟩
    (fun h => hCD (congrArg Subtype.val h))
  exact PrimeCurveIntersectionOneCrossing.vanishingIdeal_sup_eq_maximalIdeal_of_pairing_le_one
    S hmin.regular C D hCD hpair y hyD U hyU

end KltDP.Geometry.KltMinimalResolutionCrossing

#print axioms KltDP.Geometry.KltMinimalResolutionCrossing.vanishingIdeal_sup_eq_maximalIdeal

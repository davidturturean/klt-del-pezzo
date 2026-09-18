import KltDP.Geometry.SplitPrimeCurveCartierPullback

/-!
# The geometry of the two original split prime-curve images

This reducible predicate packages the already proved exact cardinality,
disjointness, original self-intersection and source comparison. Keeping
the generic conjunction abstract avoids repeatedly elaborating the
unchanged quadratic cover's concrete sheaf construction in consumers.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.SplitPrimeCurveGeometry

open NormalProjectiveSurface SplitPrimeCurveImages SplitPrimeCurveCartierPullback

variable {k : Type u} [Field k] [IsAlgClosed k] {S T : NormalProjectiveSurface k}
    (π : T.toScheme ⟶ S.toScheme) (C : S.PrimeCurve)
    (q : pullback π C.inclusion ≅ C.toScheme ⨿ C.toScheme)
    (hS : ∀ x : S.Point, RegularPoint S.toScheme x)
    (hT : ∀ x : T.Point, RegularPoint T.toScheme x)

/-- Exact geometry of the two actual split images, retaining their original source maps. -/
def copyGeometry : Prop :=
  (copyCurves (T := T) π C q).card = 2 ∧
    ((copyCurves (T := T) π C q : Finset T.PrimeCurve) : Set T.PrimeCurve).Pairwise
      (fun P Q => Disjoint (P : Set T.toScheme) (Q : Set T.toScheme)) ∧
    ∀ ε : Bool, (copyCurve (T := T) π C q ε).selfIntersectionNumber hT =
        C.selfIntersectionNumber hS ∧
      ∃ η : (copyCurve (T := T) π C q ε).toScheme ≅ C.toScheme,
        η.hom ≫ C.toSpec = (copyCurve (T := T) π C q ε).toSpec

/-- The proved Cartier pullback and original splitting projection supply all four clauses. -/
theorem copyGeometry_of_projection
    [GenericPointPreserving π] [QuasiCompact π]
    (hq : q.hom ≫ coprod.desc (𝟙 C.toScheme) (𝟙 C.toScheme) = pullback.snd π C.inclusion)
    (hπ : π ≫ S.structureMorphism = T.structureMorphism) :
    copyGeometry π C q hS hT := by
  refine ⟨copyCurves_card (T := T) π C q, copyCurves_pairwise (T := T) π C q, ?_⟩
  intro ε
  exact ⟨copyCurve_selfIntersection π C q hS hT hq hπ ε,
    copyCurveSourceIso (T := T) π C q ε,
    copyCurveSourceIso_hom_toSpec π C q hq hπ ε⟩

end KltDP.Geometry.SplitPrimeCurveGeometry

#print axioms KltDP.Geometry.SplitPrimeCurveGeometry.copyGeometry_of_projection

import KltDP.Geometry.SplitPrimeCurveImages
import KltDP.Geometry.SelectedPrimeCartierCanonicalIdeal
import KltDP.Geometry.SelectedPrimeCartierIntersection
import KltDP.Geometry.PrimeCurveCartierProjectionCases

/-!
# The actual split inverse image preserves each curve self-intersection

The general Cartier closed-fiber comparison identifies the original
pulled curve divisor with the selected Cartier divisor of the two
actual disjoint copies. Each copy maps isomorphically to the original
curve over the original field. The existing projection theorem and
disjoint selected-sum intersection formula give the self-intersection
of each actual copy.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.SplitPrimeCurveCartierPullback

open NormalProjectiveSurface SplitPrimeCurveImages SplitAmbientPullbackCopies
  SplitCartierPullbackReducedUnion

variable {k : Type u} [Field k] [IsAlgClosed k] {S T : NormalProjectiveSurface k}
    (π : T.toScheme ⟶ S.toScheme) [GenericPointPreserving π] [QuasiCompact π]
    (C : S.PrimeCurve) (q : pullback π C.inclusion ≅ C.toScheme ⨿ C.toScheme)
    (hS : ∀ x : S.Point, RegularPoint S.toScheme x)
    (hT : ∀ x : T.Point, RegularPoint T.toScheme x)

/-- The actual original curve pullback is the Cartier divisor of the actual two-copy selection. -/
theorem pullback_primeCurveCartier_eq_selected :
    letI := T.stalks_uniqueFactorizationMonoid_of_regular hT
    pullbackDivisor π (S.primeCurveCartier hS C) (S.primeCurveCartier_hasRegularEquations hS C) =
      T.selectedPrimeCartier (copyCurves (T := T) π C q) := by
  letI := T.stalks_uniqueFactorizationMonoid_of_regular hT
  have hi : effectiveCartierIdealDataOfRegularEquations S.toScheme (S.primeCurveCartier hS C)
      (S.primeCurveCartier_hasRegularEquations hS C) = C.inclusion.ker := by
    rw [S.primeCurveCartier_idealData_eq_vanishingIdeal hS C]
    exact C.vanishingIdeal.ker_gluedTo.symm
  have hp := pullbackIdealData_eq_copyUnion π C.inclusion q (S.primeCurveCartier hS C)
    (S.primeCurveCartier_hasRegularEquations hS C) hi
  apply cartierDivisor_eq_of_idealData T.toScheme _ _
    (pullbackDivisor_hasRegularEquations π _ (S.primeCurveCartier_hasRegularEquations hS C))
    (T.hasRegularCartierEquations_of_effective_weil _ (T.selectedPrimeCartier_effective _))
  change pullbackIdealData π (S.primeCurveCartier hS C) (S.primeCurveCartier_hasRegularEquations hS C) = _
  rw [T.selectedPrimeCartier_canonicalIdeal, copyCurves_union]
  exact hp

variable (hq : q.hom ≫ coprod.desc (𝟙 C.toScheme) (𝟙 C.toScheme) = pullback.snd π C.inclusion)
    (hπ : π ≫ S.structureMorphism = T.structureMorphism)

include hq in
@[reassoc] theorem copyCurveSourceIso_hom_toBase (ε : Bool) :
    (copyCurveSourceIso (T := T) π C q ε).hom ≫ C.inclusion =
      (copyCurve (T := T) π C q ε).inclusion ≫ π := by
  rw [← ambientCopy_projection π C.inclusion q hq ε, ← Category.assoc,
    copyCurveSourceIso_hom_map]

include hq hπ in
@[reassoc] theorem copyCurveSourceIso_hom_toSpec (ε : Bool) :
    (copyCurveSourceIso (T := T) π C q ε).hom ≫ C.toSpec =
      (copyCurve (T := T) π C q ε).toSpec := by
  change _ ≫ C.inclusion ≫ S.structureMorphism = _ ≫ T.structureMorphism
  rw [← Category.assoc, copyCurveSourceIso_hom_toBase π C q hq ε, Category.assoc, hπ]

include hq hπ in
/-- Each actual copy has exactly the original curve's self-intersection. -/
theorem copyCurve_selfIntersection (ε : Bool) :
    (copyCurve (T := T) π C q ε).selfIntersectionNumber hT = C.selfIntersectionNumber hS := by
  letI := T.stalks_uniqueFactorizationMonoid_of_regular hT
  have hp := PrimeCurveCartierProjectionCases.intersectionNumber_pullbackDivisor_eq_of_isoFactor
    (copyCurve (T := T) π C q ε) C π (copyCurveSourceIso (T := T) π C q ε).hom
    (copyCurveSourceIso_hom_toBase π C q hq ε).symm
    (copyCurveSourceIso_hom_toSpec π C q hq hπ ε)
    (S.primeCurveCartier hS C) (S.primeCurveCartier_hasRegularEquations hS C)
  rw [pullback_primeCurveCartier_eq_selected π C q hS hT,
    T.intersectionNumber_selected_disjoint_sum hT (copyCurves (T := T) π C q) _
      (T.selectedPrimeCartier_weil _) (copyCurves_pairwise (T := T) π C q) _
      (copyCurve_mem (T := T) π C q ε)] at hp
  exact hp

end KltDP.Geometry.SplitPrimeCurveCartierPullback

#print axioms KltDP.Geometry.SplitPrimeCurveCartierPullback.pullback_primeCurveCartier_eq_selected
#print axioms KltDP.Geometry.SplitPrimeCurveCartierPullback.copyCurve_selfIntersection


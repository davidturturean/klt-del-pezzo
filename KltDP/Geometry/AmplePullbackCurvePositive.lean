import KltDP.Geometry.AmpleCurveRestrictionPositive
import KltDP.Geometry.CartierDivisorPullbackSupport
import KltDP.Geometry.DominantCartierRegularPullback
import KltDP.Geometry.DominantCartierPullbackModule
import KltDP.Geometry.ActualExceptionalPullback

/-!
# Positive ample-pullback degree on every actual noncontracted prime

A closed point of the original curve has closed image under the proper
map. If that image equalled the image of the curve's generic point, the
whole curve would be contracted. An original ample section separates these
two target points. Its actual effective Cartier pullback meets the original
curve and avoids its generic point, giving positive original degree.

No finite-degree morphism, intersection projection formula, Hodge theorem,
Riemann--Roch condition, or independent contraction criterion is supplied.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.AmplePullbackCurvePositive

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme)

/-- A noncontracted prime's generic image differs from each closed image
of an actual point of that prime. -/
theorem generic_image_ne_of_not_exceptional (C : S.PrimeCurve)
    (hC : ¬ IsExceptionalCurve π C) (x : S.toScheme) (hx : x ∈ C)
    (hclosed : IsClosed ({π.base x} : Set X.toScheme)) :
    π.base C.genericPoint ≠ π.base x := by
  intro heq
  have hsub : (C : Set S.toScheme) ⊆ π.base ⁻¹' {π.base x} := by
    rw [← C.closure_genericPoint]
    exact closure_minimal (Set.singleton_subset_iff.mpr heq) (hclosed.preimage π.continuous)
  apply hC
  refine ⟨π.base x, Set.Subset.antisymm ?_ ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    exact hsub hz
  · intro y hy
    have hyx : y = π.base x := hy
    exact ⟨x, hx, hyx.symm⟩

/-- The original ample pullback has strictly positive degree along an
actual prime which the original proper dominant map does not contract. -/
theorem restrictionDegree_pos [IsProper π] [GenericPointPreserving π]
    (L : InvertibleSheaf X.toScheme) (hL : AmpleSerre.IsAmple L)
    (C : S.PrimeCurve) (hC : ¬ IsExceptionalCurve π C) :
    0 < C.restrictionDegree (pullbackInvertibleSheaf π L) := by
  letI : IsLocallyNoetherian X.toScheme := X.isLocallyNoetherian
  obtain ⟨x, hxC, hxclosed, _⟩ :=
    AmpleCurveRestrictionPositive.exists_closed_point_ne_generic S C
  have hxclosed' : IsClosed ({π.base x} : Set X.toScheme) := by
    rw [← Set.image_singleton]
    exact π.isClosedMap _ hxclosed
  have hne := generic_image_ne_of_not_exceptional π C hC x hxC hxclosed'
  obtain ⟨n, hn, M, hM, E, hE, e, _, _, hxE, hηE⟩ :=
    AmplePointSeparatingCartier.exists_positive_power_point_separating_effectiveCartier
      L hL (π.base x) (π.base C.genericPoint) hxclosed' hne
  let E' := pullbackDivisor π E hE
  have hE' : HasRegularCartierEquations S.toScheme E' :=
    pullbackDivisor_hasRegularEquations π E hE
  have e' : cartierDivisorModule S.toScheme E' ≅ (pullbackInvertibleSheaf π M).obj :=
    eqToIso (congrArg (cartierDivisorModule S.toScheme)
      (DominantCartierPullback.pullbackHom_eq_pullbackDivisor π E hE).symm) ≪≫
      (DominantCartierPullback.modulePullbackIso π E).symm ≪≫
      (schemeModulePullback π).mapIso e
  have hp : 0 < C.restrictionDegree (pullbackInvertibleSheaf π M) :=
    AmpleCurveRestrictionPositive.restrictionDegree_pos_of_effectiveIso_of_mem
      S C (pullbackInvertibleSheaf π M) E' hE'
      (not_mem_support_pullbackDivisor π E hE C.genericPoint hηE) e' x hxC
      ((mem_support_pullbackDivisor_iff π E hE x).mpr hxE)
  have hclass : (pullbackInvertibleSheaf π M).toPic =
      (pullbackInvertibleSheaf π L).toPic ^ n := by
    rw [← schemePicardPullbackHom_toPic, hM, map_pow, schemePicardPullbackHom_toPic]
  rw [← C.picardRestrictionDegree_toPic (pullbackInvertibleSheaf π M), hclass,
    AmplePositivity.picardRestrictionDegree_pow S C (pullbackInvertibleSheaf π L).toPic n,
    C.picardRestrictionDegree_toPic] at hp
  exact (mul_pos_iff_of_pos_left (Nat.cast_pos.mpr hn : (0 : ℤ) < n)).mp hp

/-- For an ample target sheaf, actual contraction is precisely zero
original pullback degree. Both geometric directions are derived. -/
theorem exceptional_iff_degree_zero [IsAlgClosed k] [IsProper π] [GenericPointPreserving π]
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (L : InvertibleSheaf X.toScheme) (hL : AmpleSerre.IsAmple L) (C : S.PrimeCurve) :
    IsExceptionalCurve π C ↔ C.restrictionDegree (pullbackInvertibleSheaf π L) = 0 := by
  constructor
  · intro hC
    exact hC.restrictionDegree_pullback_eq_zero π hπ C L
  · intro hzero
    by_contra hC
    exact (ne_of_gt (restrictionDegree_pos π L hL C hC)) hzero

end KltDP.Geometry.AmplePullbackCurvePositive

#print axioms KltDP.Geometry.AmplePullbackCurvePositive.restrictionDegree_pos
#print axioms KltDP.Geometry.AmplePullbackCurvePositive.exceptional_iff_degree_zero

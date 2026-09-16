import KltDP.Geometry.AmplePointSeparatingCartier
import KltDP.Geometry.PrimeCurveCodimension
import KltDP.Geometry.PrimeCurveIntersectionZero
import KltDP.Geometry.PrimeCurveIntersectionNumber
import KltDP.Geometry.FiniteTypeNoetherian
import KltDP.Geometry.AmplePositivity
import Mathlib.Topology.Separation.Basic

/-!
# Serre ampleness has positive degree on every actual prime curve

Choose an actual closed point of the original prime curve in the projective
surface. The curve's generic point is not closed, hence is distinct. The proved
point-separating Cartier construction gives a representative of a positive
power containing the closed point and avoiding the curve's generic point.
The original support/range equality supplies an actual intersection point.
The existing zero-degree criterion and original restriction/power equalities
then give strictly positive restriction degree for the original line bundle.

All point choices, support exclusions, and nonempty intersection data in the
ample consumer are derived. The curve may be singular, and the base field
need not be algebraically closed. This does not construct an IsAmple witness.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AmpleCurveRestrictionPositive

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- An actual prime curve contains an ambient closed point distinct from its
actual generic point. Compactness follows from the original projectivity. -/
theorem exists_closed_point_ne_generic (C : X.PrimeCurve) :
    ∃ x : X.toScheme, x ∈ C ∧ IsClosed ({x} : Set X.toScheme) ∧ C.genericPoint ≠ x := by
  obtain ⟨x, hxC, hx⟩ := C.isClosed.exists_closed_singleton C.nonempty
  refine ⟨x, hxC, hx, ?_⟩
  intro h
  apply C.not_isClosed_singleton_genericPoint
  simpa only [h] using hx

/-- A point in the original curve and effective divisor support supplies a
point of their actual scheme-theoretic intersection. -/
theorem nonempty_intersectionScheme_of_mem (C : X.PrimeCurve)
    (E : CartierDivisor X.toScheme) (hE : HasRegularCartierEquations X.toScheme E)
    (hC : C.NotInSupport E hE) (x : X.toScheme) (hxC : x ∈ C)
    (hxE : x ∈ (effectiveCartierIdealDataOfRegularEquations X.toScheme E hE).support) :
    Nonempty (C.intersectionScheme E hE hC) := by
  have hx : x ∈ Set.range (C.intersectionToSurface E hE hC).base := by
    rw [C.range_intersectionToSurface E hE hC]
    exact ⟨hxC, hxE⟩
  obtain ⟨z, _⟩ := hx
  exact ⟨z⟩

/-- An actual effective Cartier representative meeting the curve properly at
an actual point gives strictly positive degree for the original isomorphic
invertible sheaf. -/
theorem restrictionDegree_pos_of_effectiveIso_of_mem (C : X.PrimeCurve)
    (M : InvertibleSheaf X.toScheme) (E : CartierDivisor X.toScheme)
    (hE : HasRegularCartierEquations X.toScheme E) (hC : C.NotInSupport E hE)
    (e : cartierDivisorModule X.toScheme E ≅ M.obj)
    (x : X.toScheme) (hxC : x ∈ C)
    (hxE : x ∈ (effectiveCartierIdealDataOfRegularEquations X.toScheme E hE).support) :
    0 < C.restrictionDegree M := by
  obtain ⟨z⟩ := nonempty_intersectionScheme_of_mem X C E hE hC x hxC hxE
  have hne : C.intersectionDegree E hE hC ≠ 0 := by
    intro hz
    letI : IsEmpty (C.intersectionScheme E hE hC) :=
      (C.intersectionDegree_eq_zero_iff E hE hC).mp hz
    exact isEmptyElim z
  have hpos : 0 < C.intersectionDegree E hE hC := by omega
  calc
    (0 : ℤ) < (C.intersectionDegree E hE hC : ℤ) := Nat.cast_pos.mpr hpos
    _ = C.intersectionNumber E := (C.intersectionNumber_eq_intersectionDegree E hE hC).symm
    _ = C.restrictionDegree (cartierDivisorInvertibleSheaf X.toScheme E) :=
      C.intersectionNumber_eq_restrictionDegree E
    _ = C.restrictionDegree M := C.restrictionDegree_eq_of_iso e

/-- Serre ampleness of the original invertible sheaf implies strictly positive
restriction degree on each actual prime curve of the original normal projective
surface. No section, support, closed point, or intersection witness is assumed. -/
theorem restrictionDegree_pos_of_isAmple (L : InvertibleSheaf X.toScheme)
    (hL : AmpleSerre.IsAmple L) (C : X.PrimeCurve) :
    0 < C.restrictionDegree L := by
  letI : IsLocallyNoetherian X.toScheme := NormalProjectiveSurface.isLocallyNoetherian X
  obtain ⟨x, hxC, hxclosed, hne⟩ := exists_closed_point_ne_generic X C
  obtain ⟨n, hn, M, hM, E, hE, e, _, _, hxE, hηE⟩ :=
    AmplePointSeparatingCartier.exists_positive_power_point_separating_effectiveCartier
      L hL x C.genericPoint hxclosed hne
  have hC : C.NotInSupport E hE := hηE
  have hpos : 0 < C.restrictionDegree M :=
    restrictionDegree_pos_of_effectiveIso_of_mem X C M E hE hC e x hxC hxE
  rw [← C.picardRestrictionDegree_toPic M, hM,
    AmplePositivity.picardRestrictionDegree_pow X C L.toPic n,
    C.picardRestrictionDegree_toPic] at hpos
  have hn' : (0 : ℤ) < (n : ℤ) := Nat.cast_pos.mpr hn
  exact (mul_pos_iff_of_pos_left hn').mp hpos

end KltDP.Geometry.AmpleCurveRestrictionPositive

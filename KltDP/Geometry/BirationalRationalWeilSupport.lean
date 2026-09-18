import KltDP.Geometry.BirationalRationalWeilPushforward
import KltDP.Geometry.NonclosedPointBirationalIso

/-!
# Actual support of a rational Weil divisor killed by birational pushforward

A noncontracted source prime maps to the generic point of its original
closure curve. The existing proper birational correspondence identifies it
with that target prime's unique source prime, so its coefficient survives.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.BirationalWeilPushforward

open BirationalPrimeCorrespondence

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)

include hbir in
/-- A prime generic point cannot map to the surface generic point. -/
theorem prime_genericPoint_image_ne_generic (C : S.PrimeCurve) :
    π.base C.genericPoint ≠ genericPoint X.toScheme := by
  intro h
  obtain ⟨U, hne, hU⟩ := exists_isomorphism_open_of_isBirationalScheme π hbir
  letI : IsIso (π ∣_ U) := hU
  have hgeneric : genericPoint X.toScheme ∈ U :=
    ((genericPoint_spec X.toScheme).mem_open_set_iff U.isOpen).mpr
      (by simpa using hne)
  have hfiber := NonclosedPointBirationalIso.pointFiber_subsingleton_of_isIso_restrict
    π U (genericPoint X.toScheme) hgeneric
  exact C.genericPoint_ne_surface_genericPoint (hfiber h hbir.map_genericPoint)

/-- Every noncontracted original source prime is the unique prime above an
actual target prime; no image-prime or correspondence witness is supplied. -/
theorem exists_abovePrimeCurve_of_not_exceptional (C : S.PrimeCurve)
    (hC : ¬ IsExceptionalCurve π C) :
    ∃ E : X.PrimeCurve, C = abovePrimeCurve π hbir E := by
  have hclosed : ¬ IsClosed ({π.base C.genericPoint} : Set X.toScheme) := by
    intro hc
    apply hC
    refine ⟨π.base C.genericPoint, ?_⟩
    rw [← C.closure_genericPoint,
      ← π.isClosedMap.closure_image_eq_of_continuous π.continuous,
      Set.image_singleton, hc.closure_eq]
  let E := X.primeCurveOfNonclosedPoint (π.base C.genericPoint)
    (prime_genericPoint_image_ne_generic π hbir C) hclosed
  refine ⟨E, abovePrimeCurve_unique π hbir E C ?_⟩
  exact (X.primeCurveOfNonclosedPoint_genericPoint _ _ _).symm

/-- A nonzero original coefficient killed by pushforward is contracted. -/
theorem exceptional_of_rationalPushforward_eq_zero
    (D : S.RationalWeilDivisor) (hD : rationalPushforward π hbir D = 0)
    (C : S.PrimeCurve) (hC : D C ≠ 0) : IsExceptionalCurve π C := by
  by_contra hnot
  obtain ⟨E, hE⟩ := exists_abovePrimeCurve_of_not_exceptional π hbir C hnot
  apply hC
  rw [hE]
  exact congrArg (fun A : X.RationalWeilDivisor => A E) hD

/-- The actual finite prime support is contained in the actual contracted set. -/
theorem support_subset_exceptional_of_rationalPushforward_eq_zero
    (D : S.RationalWeilDivisor) (hD : rationalPushforward π hbir D = 0) :
    (D.support : Set S.PrimeCurve) ⊆ {C | IsExceptionalCurve π C} := by
  intro C hC
  exact exceptional_of_rationalPushforward_eq_zero π hbir D hD C
    (Finsupp.mem_support_iff.mp hC)

end KltDP.Geometry.BirationalWeilPushforward

#check @KltDP.Geometry.BirationalWeilPushforward.support_subset_exceptional_of_rationalPushforward_eq_zero
#print axioms KltDP.Geometry.BirationalWeilPushforward.support_subset_exceptional_of_rationalPushforward_eq_zero

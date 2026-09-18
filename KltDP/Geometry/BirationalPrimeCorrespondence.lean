import KltDP.Geometry.BirationalPrimePoint
import KltDP.Geometry.PointClosureCurve

/-!
# The unique original source prime above a target prime

Properness makes the lifted generic point nonclosed, since its image is
the nonclosed target prime point. The actual birational generic-point
identity makes it nongeneric. Its existing point-closure construction is
therefore an actual source prime over any field. No global equivalence
between all height-one points and prime curves is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.BirationalPrimeCorrespondence

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)

/-- The lifted point differs from the original surface generic point. -/
theorem point_ne_surface_genericPoint (C : X.PrimeCurve) :
    (point π hbir C).val ≠ genericPoint S.toScheme := by
  intro h
  apply C.genericPoint_ne_surface_genericPoint
  calc
    C.genericPoint = π.base (point π hbir C).val := (point_map π hbir C).symm
    _ = π.base (genericPoint S.toScheme) := congrArg π.base h
    _ = genericPoint X.toScheme := hbir.map_genericPoint

/-- The lifted point is nonclosed by the original proper-map closedness. -/
theorem point_not_isClosed (C : X.PrimeCurve) :
    ¬ IsClosed ({(point π hbir C).val} : Set S.toScheme) := by
  intro h
  apply C.not_isClosed_singleton_genericPoint
  simpa only [Set.image_singleton, point_map] using
    π.isClosedMap {(point π hbir C).val} h

/-- The unique source prime is the actual closure of the lifted point. -/
def abovePrimeCurve (C : X.PrimeCurve) : S.PrimeCurve :=
  S.primeCurveOfNonclosedPoint (point π hbir C).val
    (point_ne_surface_genericPoint π hbir C) (point_not_isClosed π hbir C)

/-- The actual generic point of the constructed prime is the lifted point. -/
theorem abovePrimeCurve_genericPoint (C : X.PrimeCurve) :
    (abovePrimeCurve π hbir C).genericPoint = (point π hbir C).val :=
  S.primeCurveOfNonclosedPoint_genericPoint _ _ _

/-- The original morphism sends its actual source prime generic point to
the original target prime generic point. -/
theorem abovePrimeCurve_map_genericPoint (C : X.PrimeCurve) :
    π.base (abovePrimeCurve π hbir C).genericPoint = C.genericPoint := by
  rw [abovePrimeCurve_genericPoint, point_map]

/-- The original stalk map at that prime generic point is an isomorphism. -/
theorem abovePrimeCurve_stalkMap_isIso (C : X.PrimeCurve) :
    IsIso (π.stalkMap (abovePrimeCurve π hbir C).genericPoint) := by
  rw [abovePrimeCurve_genericPoint]
  exact point_stalkMap_isIso π hbir C

/-- Any original source prime above the original target generic point is
the same constructed prime. -/
theorem abovePrimeCurve_unique (C : X.PrimeCurve) (D : S.PrimeCurve)
    (hD : π.base D.genericPoint = C.genericPoint) : D = abovePrimeCurve π hbir C := by
  apply NormalProjectiveSurface.PrimeCurve.genericPoint_injective
  exact (point_unique π hbir C D.genericPoint hD).trans
    (abovePrimeCurve_genericPoint π hbir C).symm

include hbir in
/-- Each actual target prime has exactly one actual source prime above it. -/
theorem existsUnique_prime_above (C : X.PrimeCurve) :
    ∃! D : S.PrimeCurve, π.base D.genericPoint = C.genericPoint := by
  exact ⟨abovePrimeCurve π hbir C, abovePrimeCurve_map_genericPoint π hbir C,
    fun D hD => abovePrimeCurve_unique π hbir C D hD⟩

/-- Distinct target primes have distinct original source primes. -/
theorem abovePrimeCurve_injective : Function.Injective (abovePrimeCurve π hbir) := by
  intro C D h
  apply NormalProjectiveSurface.PrimeCurve.genericPoint_injective
  calc
    C.genericPoint = π.base (abovePrimeCurve π hbir C).genericPoint :=
      (abovePrimeCurve_map_genericPoint π hbir C).symm
    _ = π.base (abovePrimeCurve π hbir D).genericPoint :=
      congrArg (fun E : S.PrimeCurve => π.base E.genericPoint) h
    _ = D.genericPoint := abovePrimeCurve_map_genericPoint π hbir D

/-- Properness identifies the image of the entire actual source prime
with the entire original target prime. -/
theorem abovePrimeCurve_image (C : X.PrimeCurve) :
    π.base '' (abovePrimeCurve π hbir C : Set S.toScheme) = (C : Set X.toScheme) := by
  rw [← (abovePrimeCurve π hbir C).closure_genericPoint,
    ← π.isClosedMap.closure_image_eq_of_continuous π.continuous,
    Set.image_singleton, abovePrimeCurve_map_genericPoint, C.closure_genericPoint]

end KltDP.Geometry.BirationalPrimeCorrespondence

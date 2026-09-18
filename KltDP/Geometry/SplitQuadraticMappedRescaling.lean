import KltDP.Geometry.SplitQuadraticGluing
import KltDP.Geometry.QuadraticCoverMappedRescaling

/-!
# The original quadratic transition preserves the two split components

The map is the existing coefficient restriction followed by the existing
unit change of generator. A compatible pair of actual unit roots makes its
CRT coordinates the two copies of the original coefficient map. This is
an ordinary local compatibility lemma; no global splitting is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry

open QuadraticCover

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Compatibility of roots implies the original quadratic branch equation. -/
theorem splitQuadraticMappedCondition (f : R →+* S) (a : Rˣ) (b v : Sˣ)
    (ha : f (a : R) = (v : S) * (b : S)) :
    f ((a : R) ^ 2) = (v : S) ^ 2 * (b : S) ^ 2 := by
  rw [map_pow, ha, mul_pow]

/-- The original coefficient-and-rescaling map preserves the actual CRT coordinates. -/
theorem splitQuadraticAlgEquiv_mappedRescale (f : R →+* S) (a : Rˣ) (b v : Sˣ)
    (h : f ((a : R) ^ 2) = (v : S) ^ 2 * (b : S) ^ 2)
    (ha : f (a : R) = (v : S) * (b : S))
    (hR : IsUnit (2 : R)) (hS : IsUnit (2 : S)) :
    (splitQuadraticAlgEquiv b hS).toRingHom.comp
        (mappedRescaleHom f ((a : R) ^ 2) ((b : S) ^ 2) v h) =
      (RingHom.prodMap f f).comp (splitQuadraticAlgEquiv a hR).toRingHom := by
  apply coverRingHom_ext
  · intro r
    change splitQuadraticAlgEquiv b hS
        (mappedRescaleHom f ((a : R) ^ 2) ((b : S) ^ 2) v h
          (algebraMap R (CoverAlgebra ((a : R) ^ 2)) r)) = _
    rw [mappedRescaleHom_algebraMap]
    change splitQuadraticAlgEquiv b hS
        (algebraMap S (SplitQuadraticAlgebra b) (f r)) =
      (RingHom.prodMap f f)
        (splitQuadraticAlgEquiv a hR (algebraMap R (SplitQuadraticAlgebra a) r))
    rw [splitQuadraticAlgEquiv_algebraMap b hS (f r),
      splitQuadraticAlgEquiv_algebraMap a hR r]
    rfl
  · change splitQuadraticAlgEquiv b hS
        (mappedRescaleHom f ((a : R) ^ 2) ((b : S) ^ 2) v h
          (root ((a : R) ^ 2))) =
      (RingHom.prodMap f f)
        (splitQuadraticAlgEquiv a hR (AdjoinRoot.root (splitQuadraticPolynomial a)))
    rw [mappedRescaleHom_root, map_mul]
    change splitQuadraticAlgEquiv b hS
        (algebraMap S (SplitQuadraticAlgebra b) (v : S)) *
          splitQuadraticAlgEquiv b hS (AdjoinRoot.root (splitQuadraticPolynomial b)) =
      (RingHom.prodMap f f)
        (splitQuadraticAlgEquiv a hR (AdjoinRoot.root (splitQuadraticPolynomial a)))
    rw [splitQuadraticAlgEquiv_algebraMap b hS (v : S),
      splitQuadraticAlgEquiv_root b hS, splitQuadraticAlgEquiv_root a hR]
    change ((v : S) * (b : S), (v : S) * (-(b : S))) =
      (f (a : R), f (-(a : R)))
    rw [map_neg, ha, mul_neg]

/-- The positive root evaluation commutes with the original atlas transition. -/
theorem splitQuadraticEvalPositive_mappedRescale (f : R →+* S) (a : Rˣ) (b v : Sˣ)
    (h : f ((a : R) ^ 2) = (v : S) ^ 2 * (b : S) ^ 2)
    (ha : f (a : R) = (v : S) * (b : S))
    (hR : IsUnit (2 : R)) (hS : IsUnit (2 : S)) :
    (splitQuadraticEvalPositive b hS).toRingHom.comp
        (mappedRescaleHom f ((a : R) ^ 2) ((b : S) ^ 2) v h) =
      f.comp (splitQuadraticEvalPositive a hR).toRingHom := by
  apply RingHom.ext
  intro x
  exact congrArg Prod.fst
    (RingHom.congr_fun (splitQuadraticAlgEquiv_mappedRescale f a b v h ha hR hS) x)

/-- The negative root evaluation commutes with that same original transition. -/
theorem splitQuadraticEvalNegative_mappedRescale (f : R →+* S) (a : Rˣ) (b v : Sˣ)
    (h : f ((a : R) ^ 2) = (v : S) ^ 2 * (b : S) ^ 2)
    (ha : f (a : R) = (v : S) * (b : S))
    (hR : IsUnit (2 : R)) (hS : IsUnit (2 : S)) :
    (splitQuadraticEvalNegative b hS).toRingHom.comp
        (mappedRescaleHom f ((a : R) ^ 2) ((b : S) ^ 2) v h) =
      f.comp (splitQuadraticEvalNegative a hR).toRingHom := by
  apply RingHom.ext
  intro x
  exact congrArg Prod.snd
    (RingHom.congr_fun (splitQuadraticAlgEquiv_mappedRescale f a b v h ha hR hS) x)

end KltDP.Geometry

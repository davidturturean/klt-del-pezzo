import KltDP.Geometry.FrobeniusNormalFactorComplement
import KltDP.Geometry.PrimeCurvePointFiberFactorization
import KltDP.Geometry.PrimeCurveCodimension

/-!
Every point of the original null-locus image is the actual point of a
section over the original field. Such a point is closed, whereas a prime
curve's generic point is not closed. Thus the original image complement
contains every target divisor generic point. No finiteness argument or
new hypothesis about target generic points is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a) (hn : 2 < n)
  (Y : NormalProjectiveSurface k) (π : multiSurface (q + 1) n a ⟶ Y.toScheme)
  (hcriterion : ∀ C : (multiSurfaceSurface (q + 1) n a ha
      (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
    (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
      C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
      C.restrictionDegree (originalLine q n a ha) = 0)

include hn hcriterion

/-- An original null-image point is an actual rational point over the
original target structure morphism. -/
theorem exists_fieldPoint_of_mem_nullImage (y : Y.toScheme)
    (hy : y ∈ π.base '' Positivity.nullLocus (multiStructure (q + 1) n a)
      (originalLine q n a ha)) :
    ∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
      p ≫ Y.structureMorphism = 𝟙 _ ∧ fieldMorphismPoint p = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [originalNullLocus_eq_curveUnion q n a ha hn] at hx
  obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨p, hp, hpY⟩ := (hcriterion C).mpr hC
  refine ⟨p, hpY, ?_⟩
  exact (PrimeCurvePointFiberFactorization.base_eq_on_prime_of_factor
    (multiSurfaceSurface (q + 1) n a ha
      (originalMultiStructureProjective k (q + 1) n a)) C π p hp x hxC).symm

/-- Every point of the original null-locus image is closed. -/
theorem isClosed_singleton_of_mem_nullImage (y : Y.toScheme)
    (hy : y ∈ π.base '' Positivity.nullLocus (multiStructure (q + 1) n a)
      (originalLine q n a ha)) : IsClosed ({y} : Set Y.toScheme) := by
  obtain ⟨p, hp, hpy⟩ :=
    exists_fieldPoint_of_mem_nullImage q n a ha hn Y π hcriterion y hy
  rw [← hpy]
  exact isClosed_point_of_section Y.structureMorphism p hp

/-- The actual complement contains the generic point of every target
prime curve, so it contains every point used to define Weil coefficients. -/
theorem genericPoint_mem_nullImageComplement [IsProper π] (C : Y.PrimeCurve) :
    C.genericPoint ∈ nullImageComplement q n a ha π := by
  change C.genericPoint ∉ π.base '' Positivity.nullLocus
    (multiStructure (q + 1) n a) (originalLine q n a ha)
  intro hC
  exact C.not_isClosed_singleton_genericPoint
    (isClosed_singleton_of_mem_nullImage q n a ha hn Y π hcriterion C.genericPoint hC)

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

import KltDP.Geometry.FrobeniusTargetDivisorOpen
import KltDP.Geometry.ExceptionalCurveOfFieldPointFactor

/-!
# An original contracted prime above each Frobenius null-image point

The actual null-locus union and the original contraction criterion produce
a prime whose entire carrier, and hence its original generic point, maps
to the given target point. The already proved section argument makes that
same target point closed. No singularity of the target is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved

/-- Every original null-image point has a genuine contracted source prime
with precisely that original generic-point image. -/
theorem exists_contracted_prime_of_mem_nullImage
    {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a) (hn : 2 < n)
    (Y : NormalProjectiveSurface k) (π : multiSurface (q + 1) n a ⟶ Y.toScheme)
    (hcriterion : ∀ C : (multiSurfaceSurface (q + 1) n a ha
        (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
        C.restrictionDegree (originalLine q n a ha) = 0)
    (y : Y.toScheme)
    (hy : y ∈ π.base '' Positivity.nullLocus (multiStructure (q + 1) n a)
      (originalLine q n a ha)) :
    IsClosed ({y} : Set Y.toScheme) ∧
    ∃ C : (multiSurfaceSurface (q + 1) n a ha
        (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
      C.restrictionDegree (originalLine q n a ha) = 0 ∧
      IsExceptionalCurve π C ∧ π.base C.genericPoint = y ∧
      ∀ z ∈ (C : Set (multiSurfaceSurface (q + 1) n a ha
          (originalMultiStructureProjective k (q + 1) n a)).toScheme), π.base z = y := by
  refine ⟨isClosed_singleton_of_mem_nullImage q n a ha hn Y π hcriterion y hy, ?_⟩
  obtain ⟨x, hx, rfl⟩ := hy
  rw [originalNullLocus_eq_curveUnion q n a ha hn] at hx
  obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨p, hp, _⟩ := (hcriterion C).mpr hC
  have hbase := PrimeCurvePointFiberFactorization.base_eq_on_prime_of_factor
    (multiSurfaceSurface (q + 1) n a ha
      (originalMultiStructureProjective k (q + 1) n a)) C π p hp
  refine ⟨C, hC, IsExceptionalCurve.of_fieldPoint_factor π C p hp, ?_, ?_⟩
  · exact (hbase C.genericPoint C.genericPoint_mem).trans (hbase x hxC).symm
  · intro z hz
    exact (hbase z hz).trans (hbase x hxC).symm

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

#print axioms KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction.exists_contracted_prime_of_mem_nullImage

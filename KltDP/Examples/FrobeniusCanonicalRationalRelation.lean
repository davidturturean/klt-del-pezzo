import KltDP.Examples.FrobeniusMultiCentreCanonicalWeilRelation
import KltDP.Geometry.SmoothCanonicalExteriorComparison
import KltDP.Geometry.CartierPicardEndpointRationalClasses

/-!
The original integral source relation applies to every actual Cartier
representative of the intrinsic exterior-square sheaf. Its class agrees
with the existing canonical representative by the original sheaf
isomorphism and Picard-to-Weil map; no canonical formula is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusCanonicalRationalRelation

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusMultiCentreCanonicalOpenComparison FrobeniusMultiCentreSpecialNullCurves
open FrobeniusMultiCentreCanonicalWeilRepresentatives FrobeniusMultiCentreCanonicalWeilRelation
open SmoothCanonicalExteriorComparison FrobeniusMultiCentreContractingNef

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

local notation "S" => sourceSurface q n a ha hproj

/-- An actual exterior-square representative has the original canonical rational class. -/
theorem canonical_module_rational_class (D : CartierDivisor (S).toScheme)
    (eD : cartierDivisorModule (S).toScheme D ≅
      relativeDifferentialExterior (multiStructure (q + 1) n a) 2) :
    (S).rationalWeilClassMap ((S).rationalCartierToWeilHom D) =
      (S).rationalWeilClassMap (rationalizeWeilDivisor S (canonicalWeil q n a ha hproj)) := by
  letI := multiStructure_smoothTwo (q + 1) n a ha
  let eLine : cartierDivisorModule (S).toScheme D ≅
      (multiCanonicalLine (q + 1) n a ha).obj :=
    eD ≪≫ (canonicalSheafOfSmoothSurfaceIsoExterior (multiStructure (q + 1) n a)).symm
  have hclass : (S).weilClassMap ((S).cartierToWeilHom D) =
      (S).weilClassMap (canonicalWeil q n a ha hproj) :=
    ((S).picardToWeilClassHom_of_module_iso (multiCanonicalLine (q + 1) n a ha)
      D eLine.symm).symm.trans (canonical_picardToWeil q n a ha hproj)
  exact congrArg (S).weilClassRationalization hclass

/-- The proved original source relation, rationalized on the actual divisor classes. -/
theorem canonical_module_rational_relation (D : CartierDivisor (S).toScheme)
    (eD : cartierDivisorModule (S).toScheme D ≅
      relativeDifferentialExterior (multiStructure (q + 1) n a) 2) :
    let p : ℤ := (q + 1 : ℕ)
    let r : ℤ := (n : ℤ) - 2
    let s : ℤ := p * r
    let d : ℤ := 2 - (p - 2) * r
    (s : ℚ) • (S).rationalWeilClassMap ((S).rationalCartierToWeilHom D) +
      ((s - 2 : ℤ) : ℚ) • (S).rationalWeilClassMap
        (rationalizeWeilDivisor S (Finsupp.single (graphPrimeCurve q n a ha hproj) 1)) +
      ((r * (p - 2) : ℤ) : ℚ) • (S).rationalWeilClassMap
        (rationalizeWeilDivisor S
          (∑ i : Fin n, Finsupp.single (fiberPrimeCurve q n a ha hproj i) 1)) +
      (d : ℚ) • (S).rationalWeilClassMap
        (rationalizeWeilDivisor S (contractingWeil q n a ha hproj)) = 0 := by
  have h := congrArg (S).weilClassRationalization
    (canonicalRelationDivisor_class_eq_zero q n a ha hproj)
  simp only [canonicalRelationDivisor, map_add, map_zsmul, map_zero,
    weilClassRationalization_class] at h
  rw [← canonical_module_rational_class q n a ha hproj D eD] at h
  simpa only [Int.cast_smul_eq_zsmul] using h

end KltDP.Examples.FrobeniusCanonicalRationalRelation

import KltDP.Geometry.QuadraticBranchIntrinsicCanonicalFactor
import KltDP.Geometry.QuadraticUnitIntrinsicCanonicalFactor
import KltDP.Geometry.SchemeTopDifferentialFactorSquare

/-!
# Named normalization of the original intrinsic quadratic factors

These small affine statements identify the existing intrinsic tensor
inclusion with the original structure-unit tensor inclusion. The original
ring maps and actual differential maps remain explicit, before any global
chart square is substituted.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.QuadraticCover

open AffineNativeTopDifferential

local instance intrinsicStructureModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
  [Algebra.IsStandardSmoothOfRelativeDimension 2 k R] (s : R)

/-- The original branch factor uses the same actual structure tensor inclusion. -/
theorem branchIntrinsicCanonicalIso_structure_factor [Nontrivial R]
    (hs : s ∈ nonZeroDivisors R) (h2 : IsUnit (2 : R))
    (b : Basis (Fin 2) R (KaehlerDifferential k R)) (hb : b 0 = KaehlerDifferential.D k R s) :
    (branchIntrinsicCanonicalIso k R s hs h2 b hb).hom ≫
      schemeStructureTensorInclusion (AffinePrincipalIdealTildeFrame.inclusion (rootIdeal s))
        (intrinsic k (CoverAlgebra s) 2) =
      SchemeKaehlerExteriorPullbackTransport.map
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) (toBase s)
        (Spec.map (CommRingCat.ofHom (algebraMap k (CoverAlgebra s))))
        (spec_comp k (IsScalarTower.toAlgHom k R (CoverAlgebra s))) 2 := by
  simpa only [AffineNativeTopDifferentialIdealTensor.tensorInclusion,
    AffineNativeTopDifferentialIdealTensor.idealInclusionSheaf,
    AffineNativeTopDifferentialIdealTensor.inclusionMorphism,
    AffineNativeTopDifferentialIdealTensor.ringTildeUnitIso,
    AffinePrincipalIdealTildeFrame.inclusion, schemeStructureTensorInclusion,
    Iso.trans_hom, Category.assoc, intrinsicMap] using
      branchIntrinsicCanonicalIso_factor k R s hs h2 b hb

/-- The original unit factor has the same normalized structure tensor inclusion. -/
theorem unitIntrinsicCanonicalIso_structure_factor (h2 : IsUnit (2 : R)) (hs : IsUnit s)
    (b : Basis (Fin 2) R (KaehlerDifferential k R)) :
    (unitIntrinsicCanonicalIso k R s h2 hs b).hom ≫
      schemeStructureTensorInclusion (AffinePrincipalIdealTildeFrame.inclusion (rootIdeal s))
        (intrinsic k (CoverAlgebra s) 2) =
      SchemeKaehlerExteriorPullbackTransport.map
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) (toBase s)
        (Spec.map (CommRingCat.ofHom (algebraMap k (CoverAlgebra s))))
        (spec_comp k (IsScalarTower.toAlgHom k R (CoverAlgebra s))) 2 := by
  simpa only [AffineNativeTopDifferentialIdealTensor.tensorInclusion,
    AffineNativeTopDifferentialIdealTensor.idealInclusionSheaf,
    AffineNativeTopDifferentialIdealTensor.inclusionMorphism,
    AffineNativeTopDifferentialIdealTensor.ringTildeUnitIso,
    AffinePrincipalIdealTildeFrame.inclusion, schemeStructureTensorInclusion,
    Iso.trans_hom, Category.assoc, intrinsicMap] using
      unitIntrinsicCanonicalIso_factor k R s h2 hs b

end KltDP.Geometry.QuadraticCover

#print axioms KltDP.Geometry.QuadraticCover.branchIntrinsicCanonicalIso_structure_factor
#print axioms KltDP.Geometry.QuadraticCover.unitIntrinsicCanonicalIso_structure_factor

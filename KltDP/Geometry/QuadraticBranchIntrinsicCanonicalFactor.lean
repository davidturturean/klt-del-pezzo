import KltDP.Geometry.QuadraticBranchNativeIdealFactor
import KltDP.Geometry.StandardSmoothIdealDifferentialFactor

/-!
# The intrinsic canonical factor on the same original quadratic spectrum

The original ring map, actual differential bases and original regular root
ideal yield an intrinsic top-sheaf tensor isomorphism. Its composite with
the original root-ideal tensor inclusion is exactly the original intrinsic
differential. The branch-adapted base basis is the explicit local helper
input; its geometric producer is kept separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

namespace KltDP.Geometry.QuadraticCover

open AffineNativeTopDifferential AffineNativeTopDifferentialIdealTensor

universe u

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] [Nontrivial R]
variable [Algebra.IsStandardSmoothOfRelativeDimension 2 k R]
variable (s : R) (hs : s ∈ nonZeroDivisors R) (h2 : IsUnit (2 : R))
variable (b : Basis (Fin 2) R (KaehlerDifferential k R))
variable (hb : b 0 = KaehlerDifferential.D k R s)

local instance branchModules : MonoidalCategory (Spec (CommRingCat.of (CoverAlgebra s))).Modules :=
  Scheme.Modules.monoidalCategory _

/-- The original pulled intrinsic top sheaf is the original root ideal
tensored with the intrinsic top sheaf of the same quadratic spectrum. -/
def branchIntrinsicCanonicalIso :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom (algebraMap R (CoverAlgebra s))))).obj
        (intrinsic k R 2) ≅
      (ModuleCat.of (CoverAlgebra s) (rootIdeal s)).tilde ⊗ intrinsic k (CoverAlgebra s) 2 :=
  tensorIso k (CoverAlgebra s) (branchDifferentialBasis k R s b hb) (rootIdeal s)
    (IsScalarTower.toAlgHom k R (CoverAlgebra s)) b (branchNativeIdealEquiv k R s hs h2 b)

/-- This is a normalized factor of the same intrinsic differential,
with the native factor proved internally from the original quadratic equation. -/
theorem branchIntrinsicCanonicalIso_factor :
    (branchIntrinsicCanonicalIso k R s hs h2 b hb).hom ≫
        tensorInclusion k (CoverAlgebra s) (rootIdeal s) =
      intrinsicMap k (IsScalarTower.toAlgHom k R (CoverAlgebra s)) 2 :=
  tensorIso_factor_of_standardSmooth k (CoverAlgebra s)
    (IsScalarTower.toAlgHom k R (CoverAlgebra s)) b
    (branchDifferentialBasis k R s b hb) (rootIdeal s)
    (branchNativeIdealEquiv k R s hs h2 b) (branchNativeIdealEquiv_factor k R s hs h2 b hb)

end KltDP.Geometry.QuadraticCover

#print axioms KltDP.Geometry.QuadraticCover.branchIntrinsicCanonicalIso_factor

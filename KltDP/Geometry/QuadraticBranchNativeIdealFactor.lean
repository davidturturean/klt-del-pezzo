import KltDP.Geometry.QuadraticBranchNativeDifferential
import KltDP.Geometry.QuadraticBranchCanonicalFactor

/-!
# The original native quadratic differential factors through the root ideal

The original extended source frame, multiplication by the actual unit two,
and the original regular root frame produce the ideal equivalence. Its
composite with the original inclusion and cover frame is proved to be the
whole original native map. No native factorization is an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry.QuadraticCover

open AffineKaehlerTildeDerivation AffineTopDifferentialFrame
open AffineNativeTopDifferential

universe u

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] [Nontrivial R]
variable (s : R) (hs : s ∈ nonZeroDivisors R) (h2 : IsUnit (2 : R))
variable (b : Basis (Fin 2) R (KaehlerDifferential k R))

/-- The actual regular root gives the original scalar-extended top
differentials an equivalence with the original root ideal. -/
def branchNativeIdealEquiv :
    (ModuleCat.extendScalars (algebraMap R (CoverAlgebra s))).obj
      ((differentialModule k R).exteriorPower 2) ≃ₗ[CoverAlgebra s] rootIdeal s :=
  (extendedFrame k (IsScalarTower.toAlgHom k R (CoverAlgebra s)) b).trans
    ((LinearEquiv.smulOfUnit (M := CoverAlgebra s) (coverTwoUnit R s h2)).trans
      (AffinePrincipalIdealTildeFrame.equationEquiv (rootIdeal s) (rootIdealGenerator s)
        rfl (root_mem_nonZeroDivisors s hs)))

/-- The constructed equivalence retains the original root coefficient. -/
theorem branchNativeIdealEquiv_val
    (omega : (ModuleCat.extendScalars (algebraMap R (CoverAlgebra s))).obj
      ((differentialModule k R).exteriorPower 2)) :
    (branchNativeIdealEquiv k R s hs h2 b omega : CoverAlgebra s) =
      extendedFrame k (IsScalarTower.toAlgHom k R (CoverAlgebra s)) b omega * (2 * root s) := by
  change ((coverTwoUnit R s h2 : CoverAlgebra s) *
    extendedFrame k (IsScalarTower.toAlgHom k R (CoverAlgebra s)) b omega) * root s = _
  rw [coverTwoUnit_val]
  ring

/-- The produced factor is exactly the original native top-differential
map after the original ideal inclusion and original cover-frame inverse. -/
theorem branchNativeIdealEquiv_factor (hb : b 0 = KaehlerDifferential.D k R s) :
    (determinantEquiv (branchDifferentialBasis k R s b hb)).symm.toLinearMap.comp
        ((rootIdeal s).subtype.comp (branchNativeIdealEquiv k R s hs h2 b).toLinearMap) =
      (AffineNativeTopDifferential.map k (IsScalarTower.toAlgHom k R (CoverAlgebra s)) 2).hom := by
  apply LinearMap.ext
  intro omega
  change (determinantEquiv (branchDifferentialBasis k R s b hb)).symm
      (branchNativeIdealEquiv k R s hs h2 b omega : CoverAlgebra s) = _
  apply (determinantEquiv (branchDifferentialBasis k R s b hb)).injective
  rw [LinearEquiv.apply_symm_apply, branchNativeIdealEquiv_val]
  exact (branchNativeMap_frame k R s b hb omega).symm

end KltDP.Geometry.QuadraticCover

#print axioms KltDP.Geometry.QuadraticCover.branchNativeIdealEquiv_factor

import KltDP.Geometry.AffineNativeDifferentialWedge
import KltDP.Geometry.AffineNativeTopDifferentialFrame
import KltDP.Geometry.QuadraticBranchTopDifferentialMap

/-!
# The actual native top-differential map of the original quadratic ring map

The scalar extension is the literal ModuleCat.extendScalars object used
by the intrinsic sheaf comparison. The original algebra structure is
compared by the preceding wedge lemma before applying the proved branch
calculation. The resulting whole-map coefficient is exactly twice the
original quadratic root.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace KltDP.Geometry.QuadraticCover

open AffineKaehlerTildeDerivation AffineTopDifferentialFrame
open AffineNativeTopDifferential

universe u

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] [Nontrivial R]
variable (s : R) (b : Basis (Fin 2) R (KaehlerDifferential k R))
variable (hb : b 0 = KaehlerDifferential.D k R s)

/-- The original native map has the proved branch value on the original
scalar-extended basis wedge, without an assumed native-map comparison. -/
theorem branchNativeMap_basis_wedge :
    AffineNativeTopDifferential.map k (IsScalarTower.toAlgHom k R (CoverAlgebra s)) 2
        ((1 : CoverAlgebra s) ⊗ₜ[R,(algebraMap R (CoverAlgebra s))]
          exteriorPower.ιMulti R 2 b) =
      (2 * root s) • exteriorPower.ιMulti (CoverAlgebra s) 2
        (branchDifferentialBasis k R s b hb) := by
  rw [map_one_tmul_forms_algebraMap]
  simpa only [exteriorPower.map_apply_ιMulti, Function.comp_def,
    Basis.baseChange_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul] using
    exteriorDifferential_basis_wedge k R s b hb

/-- The original native source frame and the constructed cover frame
identify the entire original map with multiplication by twice the root. -/
theorem branchNativeMap_frame
    (omega : (ModuleCat.extendScalars (algebraMap R (CoverAlgebra s))).obj
      ((differentialModule k R).exteriorPower 2)) :
    determinantEquiv (branchDifferentialBasis k R s b hb)
        (AffineNativeTopDifferential.map k (IsScalarTower.toAlgHom k R (CoverAlgebra s)) 2 omega) =
      extendedFrame k (IsScalarTower.toAlgHom k R (CoverAlgebra s)) b omega * (2 * root s) := by
  let φ := IsScalarTower.toAlgHom k R (CoverAlgebra s)
  have hw : AffineNativeTopDifferential.map k φ 2 omega =
      (extendedFrame k φ b omega * (2 * root s)) •
        exteriorPower.ιMulti (CoverAlgebra s) 2 (branchDifferentialBasis k R s b hb) := by
    calc
      _ = AffineNativeTopDifferential.map k φ 2
          (extendedFrame k φ b omega •
            ((1 : CoverAlgebra s) ⊗ₜ[R,φ.toRingHom] exteriorPower.ιMulti R 2 b)) :=
        congrArg (AffineNativeTopDifferential.map k φ 2)
          (extendedFrame_expansion k φ b omega).symm
      _ = extendedFrame k φ b omega • AffineNativeTopDifferential.map k φ 2
          ((1 : CoverAlgebra s) ⊗ₜ[R,φ.toRingHom] exteriorPower.ιMulti R 2 b) :=
        (AffineNativeTopDifferential.map k φ 2).hom.map_smul _ _
      _ = _ := by rw [branchNativeMap_basis_wedge k R s b hb, smul_smul]
  change determinantEquiv (branchDifferentialBasis k R s b hb)
    (AffineNativeTopDifferential.map k φ 2 omega) = _
  rw [hw, map_smul, determinantEquiv_basis_wedge, smul_eq_mul, mul_one]

end KltDP.Geometry.QuadraticCover

#print axioms KltDP.Geometry.QuadraticCover.branchNativeMap_frame

import KltDP.Geometry.AffineNativeDifferentialWedge
import KltDP.Geometry.AffineNativeTopDifferentialFrame
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The original native differential frame for an actual formally étale algebra

The pinned Kähler equivalence carries the original pulled basis to a basis
of the target. The original native map sends the original wedge to that
same target wedge, so its whole determinant coordinate is unchanged.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct ChangeOfRings
universe u

namespace KltDP.Geometry.AffineEtaleNativeDifferentialFrame

open AffineKaehlerTildeDerivation AffineTopDifferentialFrame AffineNativeTopDifferential

variable (k A B : Type u) [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  [Algebra.FormallyEtale A B]
  (b : Basis (Fin 2) A (KaehlerDifferential k A))

/-- The actual étale Kähler map transports the original base basis. -/
def basis : Basis (Fin 2) B (KaehlerDifferential k B) :=
  (b.baseChange B).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A B)

theorem basis_apply (i : Fin 2) :
    basis k A B b i = KaehlerDifferential.map k k A B (b i) := by
  rw [basis, Basis.map_apply, Basis.baseChange_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul]

/-- The original scalar-extended wedge has exactly the original target wedge as image. -/
theorem map_basis_wedge :
    AffineNativeTopDifferential.map k (IsScalarTower.toAlgHom k A B) 2
      ((1 : B) ⊗ₜ[A,(algebraMap A B)] exteriorPower.ιMulti A 2 b) =
      exteriorPower.ιMulti B 2 (basis k A B b) := by
  rw [map_one_tmul_forms_algebraMap]
  apply congrArg (exteriorPower.ιMulti B 2)
  funext i
  exact (basis_apply k A B b i).symm

/-- The whole original native map preserves the original determinant coordinate. -/
theorem map_frame
    (omega : (ModuleCat.extendScalars (algebraMap A B)).obj
      ((differentialModule k A).exteriorPower 2)) :
    determinantEquiv (basis k A B b)
      (AffineNativeTopDifferential.map k (IsScalarTower.toAlgHom k A B) 2 omega) =
      extendedFrame k (IsScalarTower.toAlgHom k A B) b omega := by
  let φ := IsScalarTower.toAlgHom k A B
  have hw : AffineNativeTopDifferential.map k φ 2 omega =
      extendedFrame k φ b omega • exteriorPower.ιMulti B 2 (basis k A B b) := by
    calc
      _ = AffineNativeTopDifferential.map k φ 2
          (extendedFrame k φ b omega •
            ((1 : B) ⊗ₜ[A,φ.toRingHom] exteriorPower.ιMulti A 2 b)) :=
        congrArg (AffineNativeTopDifferential.map k φ 2)
          (extendedFrame_expansion k φ b omega).symm
      _ = extendedFrame k φ b omega • AffineNativeTopDifferential.map k φ 2
          ((1 : B) ⊗ₜ[A,φ.toRingHom] exteriorPower.ιMulti A 2 b) :=
        (AffineNativeTopDifferential.map k φ 2).hom.map_smul _ _
      _ = _ := by rw [map_basis_wedge k A B b]
  change determinantEquiv (basis k A B b) (AffineNativeTopDifferential.map k φ 2 omega) = _
  rw [hw, map_smul, determinantEquiv_basis_wedge, smul_eq_mul, mul_one]

end KltDP.Geometry.AffineEtaleNativeDifferentialFrame

#print axioms KltDP.Geometry.AffineEtaleNativeDifferentialFrame.map_frame

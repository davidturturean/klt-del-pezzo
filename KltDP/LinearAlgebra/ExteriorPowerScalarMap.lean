import KltDP.Compatibility.ExteriorPowerBaseChange

/-!
# The original exterior-power map after scalar extension

This is the canonical exterior-power scalar-extension comparison followed
by the exterior power of the scalar extension of the given linear map.
Its formula on every original pure wedge follows from the existing
universal-property maps. No basis or invertibility premise is used.
-/

noncomputable section

open scoped TensorProduct

universe u v w z

namespace KltDP.LinearAlgebra.ExteriorPowerScalarMap

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
  {M : Type w} {N : Type z} [AddCommGroup M] [AddCommGroup N]
  [Module A M] [Module A N] [Module B N] [IsScalarTower A B N]

/-- The canonical map on exterior powers for the original change of scalars. -/
def map (n : ℕ) (f : M →ₗ[A] N) : (⋀[A]^n M) →ₗ[A] (⋀[B]^n N) :=
  ((exteriorPower.map n (f.liftBaseChange B)).restrictScalars A).comp
    (((KltDP.Compatibility.ExteriorPowerBaseChange.map A B n M).restrictScalars A).comp
      (TensorProduct.mk A B (⋀[A]^n M) 1))

/-- Each original pure wedge maps to the wedge of the original mapped vectors. -/
theorem map_ιMulti (n : ℕ) (f : M →ₗ[A] N) (v : Fin n → M) :
    map A B n f (exteriorPower.ιMulti A n v) =
      exteriorPower.ιMulti B n (fun i => f (v i)) := by
  change exteriorPower.map n (f.liftBaseChange B)
      (KltDP.Compatibility.ExteriorPowerBaseChange.map A B n M
        (1 ⊗ₜ[A] exteriorPower.ιMulti A n v)) = _
  rw [KltDP.Compatibility.ExteriorPowerBaseChange.map_one_tmul_ιMulti,
    exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  exact (LinearMap.liftBaseChange_tmul B f (1 : B) (v i)).trans (one_smul B _)

end KltDP.LinearAlgebra.ExteriorPowerScalarMap

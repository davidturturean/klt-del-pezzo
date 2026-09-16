import KltDP.LinearAlgebra.ExteriorPowerScalarMap

/-!
# Exterior maps retaining an explicit original ring homomorphism

View the original semilinear map as linear over its original restriction
of scalars, then apply the existing canonical exterior scalar map. The
result keeps the ring homomorphism explicit, including in its type.
-/

noncomputable section

universe u v w z

namespace KltDP.LinearAlgebra.ExteriorPowerSemilinearMap

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
  {M : Type w} {N : Type z} [AddCommGroup M] [AddCommGroup N]
  [Module A M] [Module B N] (φ : A →+* B)

private def asLinear (f : M →ₛₗ[φ] N) :
    letI : Module A N := Module.compHom N φ
    M →ₗ[A] N := by
  letI : Module A N := Module.compHom N φ
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' := f.map_smulₛₗ }

/-- The canonical exterior map is semilinear over exactly the original ring homomorphism. -/
def map (n : ℕ) (f : M →ₛₗ[φ] N) : (⋀[A]^n M) →ₛₗ[φ] (⋀[B]^n N) := by
  letI : Algebra A B := φ.toAlgebra
  letI : Module A N := Module.compHom N φ
  letI : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let g := ExteriorPowerScalarMap.map A B n (asLinear φ f)
  exact
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun a x => (g.map_smul a x).trans (algebraMap_smul B a _).symm }

/-- The original pure wedge maps to the wedge of the original semilinear images. -/
theorem map_ιMulti (n : ℕ) (f : M →ₛₗ[φ] N) (v : Fin n → M) :
    map φ n f (exteriorPower.ιMulti A n v) = exteriorPower.ιMulti B n (fun i => f (v i)) := by
  letI : Algebra A B := φ.toAlgebra
  letI : Module A N := Module.compHom N φ
  letI : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  change ExteriorPowerScalarMap.map A B n (asLinear φ f)
    (exteriorPower.ιMulti A n v) = exteriorPower.ιMulti B n (fun i => (asLinear φ f) (v i))
  exact ExteriorPowerScalarMap.map_ιMulti A B n (asLinear φ f) v

end KltDP.LinearAlgebra.ExteriorPowerSemilinearMap

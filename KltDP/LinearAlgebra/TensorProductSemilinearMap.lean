/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jack McKoen, Joël Riou

The scalar-balancing calculation follows the pinned original restriction
map in Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.lean:40-46.
-/
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Module.RingHom

/-!
# Tensor products of maps over the original ring homomorphism

The pinned tensor universal property produces the map on pure tensors.
The ring homomorphism remains explicit in the resulting semilinear type.
-/

noncomputable section

open scoped TensorProduct

universe u v w z w' z'

namespace KltDP.LinearAlgebra.TensorProductSemilinearMap

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
  {M : Type w} {N : Type z} {M' : Type w'} {N' : Type z'}
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid M'] [AddCommMonoid N']
  [Module A M] [Module A N] [Module B M'] [Module B N']
  (φ : A →+* B) (f : M →ₛₗ[φ] M') (g : N →ₛₗ[φ] N')

/-- The original pure tensor pairing, before introducing any scalar action on a map space. -/
private def additivePair : M →+ N →+ M' ⊗[B] N' :=
  { toFun := fun m =>
      { toFun := fun n => f m ⊗ₜ[B] g n
        map_zero' := by rw [map_zero, TensorProduct.tmul_zero]
        map_add' := fun n n' => by rw [map_add, TensorProduct.tmul_add] }
    map_zero' := by
      apply AddMonoidHom.ext
      intro n
      change f 0 ⊗ₜ[B] g n = 0
      rw [map_zero, TensorProduct.zero_tmul]
    map_add' := fun m m' => by
      apply AddMonoidHom.ext
      intro n
      change f (m + m') ⊗ₜ[B] g n = f m ⊗ₜ[B] g n + f m' ⊗ₜ[B] g n
      rw [map_add, TensorProduct.add_tmul] }

/-- The original pairing is balanced over the source ring. -/
private def additiveMap : M ⊗[A] N →+ M' ⊗[B] N' :=
  TensorProduct.liftAddHom (additivePair φ f g) (fun a m n => by
    change f (a • m) ⊗ₜ[B] g n = f m ⊗ₜ[B] g (a • n)
    rw [f.map_smulₛₗ, g.map_smulₛₗ, TensorProduct.tmul_smul, TensorProduct.smul_tmul'])

private theorem additiveMap_tmul (m : M) (n : N) :
    additiveMap φ f g (m ⊗ₜ[A] n) = f m ⊗ₜ[B] g n := rfl

private theorem additiveMap_smul (a : A) (x : M ⊗[A] N) :
    additiveMap φ f g (a • x) = φ a • additiveMap φ f g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul m n =>
      rw [TensorProduct.smul_tmul', additiveMap_tmul, additiveMap_tmul,
        f.map_smulₛₗ, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- The canonical tensor map over exactly the original scalar homomorphism. -/
def map : M ⊗[A] N →ₛₗ[φ] M' ⊗[B] N' :=
  { toFun := additiveMap φ f g
    map_add' := (additiveMap φ f g).map_add
    map_smul' := additiveMap_smul φ f g }

/-- The actual pure tensor formula identifies both original component maps. -/
theorem map_tmul (m : M) (n : N) :
    map φ f g (m ⊗ₜ[A] n) = f m ⊗ₜ[B] g n := rfl

end KltDP.LinearAlgebra.TensorProductSemilinearMap

/-
The scalar-restriction adapter below uses the pinned Mathlib multilinear
and alternating-map constructions, preserving their notices:

Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

Copyright (c) 2020 Zhangir Azerbayev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Zhangir Azerbayev
-/
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The canonical map from the scalar extension of an exterior power

For the given algebra structure `A → B`, extend the canonical alternating
map on `B ⊗[A] M` by the universal properties of the exterior power and
the tensor product. This gives the original scalar-extension comparison
`B ⊗[A] (⋀[A]^n M) →ₗ[B] ⋀[B]^n (B ⊗[A] M)`.

The pure-wedge formulas identify this map on the original vectors. No
basis, flatness, invertibility of two, or replacement scalar action is
assumed. This module constructs the forward map and makes no assertion
that it is an equivalence.
-/

noncomputable section

open scoped TensorProduct

universe u v w

namespace KltDP.Compatibility.ExteriorPowerBaseChange

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
variable (n : ℕ) (M : Type w) [AddCommGroup M] [Module A M]

/-- The canonical `B`-alternating wedge, viewed over the original scalars
`A` and evaluated on the vectors `1 ⊗ m`. -/
private def alternating : M [⋀^Fin n]→ₗ[A] (⋀[B]^n (B ⊗[A] M)) :=
  let a : (B ⊗[A] M) [⋀^Fin n]→ₗ[A] (⋀[B]^n (B ⊗[A] M)) :=
    { toMultilinearMap :=
        (exteriorPower.ιMulti B n).toMultilinearMap.restrictScalars A
      map_eq_zero_of_eq' := fun v i j h hij =>
        (exteriorPower.ιMulti B n).map_eq_zero_of_eq v h hij }
  a.compLinearMap (TensorProduct.mk A B M 1)

/-- The canonical comparison from the scalar extension of the original
exterior power to the exterior power of the scalar-extended module. -/
def map : B ⊗[A] (⋀[A]^n M) →ₗ[B] (⋀[B]^n (B ⊗[A] M)) :=
  (exteriorPower.alternatingMapLinearEquiv (alternating A B n M)).liftBaseChange B

/-- A pure tensor containing an original wedge maps to the scalar times
the wedge of the extended vectors. -/
theorem map_tmul_ιMulti (r : B) (v : Fin n → M) :
    map A B n M (r ⊗ₜ[A] exteriorPower.ιMulti A n v) =
      r • exteriorPower.ιMulti B n (fun i => 1 ⊗ₜ[A] v i) := by
  exact (LinearMap.liftBaseChange_tmul B
    (exteriorPower.alternatingMapLinearEquiv (alternating A B n M))
    r (exteriorPower.ιMulti A n v)).trans
      (congrArg (fun z : ⋀[B]^n (B ⊗[A] M) => r • z)
        (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
          (alternating A B n M) v))

/-- In particular, the original pure wedge extends to the pure wedge of
the canonically extended vectors. -/
theorem map_one_tmul_ιMulti (v : Fin n → M) :
    map A B n M (1 ⊗ₜ[A] exteriorPower.ιMulti A n v) =
      exteriorPower.ιMulti B n (fun i => 1 ⊗ₜ[A] v i) := by
  simpa only [one_smul] using map_tmul_ιMulti A B n M 1 v

end KltDP.Compatibility.ExteriorPowerBaseChange

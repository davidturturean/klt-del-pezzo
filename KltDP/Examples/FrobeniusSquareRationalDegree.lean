import KltDP.Examples.FrobeniusSquareRationalMap
import KltDP.Geometry.QuadraticCoverIntegral
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Degree and inseparability of the actual square field lift

We reuse the project's original quadratic quotient and its proved basis.
Sending its root to the rational coordinate and its coefficients through
the original square substitution gives a bijection. Thus the field action
defined by that substitution has dimension two. In characteristic two,
the square of every rational function lies in its actual image.
-/

noncomputable section

universe u

namespace KltDP.Examples.FrobeniusSquareRationalMap

open KltDP.Geometry.QuadraticCover

variable (k : Type u) [Field k]

private instance quotientIrreducible :
    Fact (Irreducible (polynomial (RatFunc.X : RatFunc k))) :=
  ⟨polynomial_irreducible_of_nonsquare _ (X_not_square k)⟩

/-- Cache the quotient's original coefficient action before installing the
different square-map action on its target field. -/
private def originalQuotientAlgebra :
    Algebra (RatFunc k) (CoverAlgebra (RatFunc.X : RatFunc k)) := inferInstance

/-- The existing quadratic algebra maps to the original rational function field. -/
def quadraticMap : CoverAlgebra (RatFunc.X : RatFunc k) →+* RatFunc k :=
  AdjoinRoot.lift (squareHom k).toRingHom RatFunc.X (by
    simp only [polynomial, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    change (RatFunc.X : RatFunc k) ^ 2 - squareHom k RatFunc.X = 0
    rw [squareHom_X, sub_self])

@[simp]
theorem quadraticMap_algebraMap (a : RatFunc k) :
    quadraticMap k (algebraMap (RatFunc k) (CoverAlgebra RatFunc.X) a) =
      squareHom k a := AdjoinRoot.lift_of _

@[simp]
theorem quadraticMap_root :
    quadraticMap k (root (RatFunc.X : RatFunc k)) = RatFunc.X :=
  AdjoinRoot.lift_root _

/-- Constants and the original coordinate already generate every fraction. -/
theorem quadraticMap_surjective : Function.Surjective (quadraticMap k) := by
  have hp : ∀ p : Polynomial k,
      ∃ z, quadraticMap k z = algebraMap (Polynomial k) (RatFunc k) p := by
    intro p
    refine Polynomial.induction_on p ?_ ?_ ?_
    · intro c
      refine ⟨algebraMap (RatFunc k) (CoverAlgebra RatFunc.X) (RatFunc.C c), ?_⟩
      simpa only [quadraticMap_algebraMap, RatFunc.algebraMap_C,
        RatFunc.algebraMap_eq_C] using (squareHom k).commutes c
    · intro p q hp hq
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    · intro n c _
      refine ⟨algebraMap (RatFunc k) (CoverAlgebra RatFunc.X) (RatFunc.C c) *
        root RatFunc.X ^ (n + 1), ?_⟩
      simp only [map_mul, map_pow, quadraticMap_algebraMap, quadraticMap_root,
        RatFunc.algebraMap_C, RatFunc.algebraMap_X]
      exact congrArg (fun a : RatFunc k => a * RatFunc.X ^ (n + 1))
        ((squareHom k).commutes c)
  intro z
  obtain ⟨a, ha⟩ := hp z.num
  obtain ⟨b, hb⟩ := hp z.denom
  exact ⟨a / b, by rw [map_div₀, ha, hb, RatFunc.num_div_denom]⟩

/-- This equivalence uses the original square map as its base-field action. -/
def quadraticEquiv :
    letI : Algebra (RatFunc k) (CoverAlgebra (RatFunc.X : RatFunc k)) :=
      originalQuotientAlgebra k
    letI : Algebra (RatFunc k) (RatFunc k) := (squareHom k).toRingHom.toAlgebra
    CoverAlgebra (RatFunc.X : RatFunc k) ≃ₐ[RatFunc k] RatFunc k := by
  letI : Algebra (RatFunc k) (CoverAlgebra (RatFunc.X : RatFunc k)) :=
    originalQuotientAlgebra k
  letI : Algebra (RatFunc k) (RatFunc k) := (squareHom k).toRingHom.toAlgebra
  exact { RingEquiv.ofBijective (quadraticMap k)
      ⟨(quadraticMap k).injective, quadraticMap_surjective k⟩ with
    commutes' := by
      intro r
      change quadraticMap k (algebraMap (RatFunc k) (CoverAlgebra RatFunc.X) r) =
        squareHom k r
      exact quadraticMap_algebraMap k r }

/-- The extension induced by the actual square substitution has degree two. -/
theorem squareHom_finrank :
    letI : Algebra (RatFunc k) (RatFunc k) := (squareHom k).toRingHom.toAlgebra
    letI : Module (RatFunc k) (RatFunc k) := Algebra.toModule
    Module.finrank (RatFunc k) (RatFunc k) = 2 := by
  letI : Algebra (RatFunc k) (RatFunc k) := (squareHom k).toRingHom.toAlgebra
  letI : Module (RatFunc k) (RatFunc k) := Algebra.toModule
  letI : Algebra (RatFunc k) (CoverAlgebra (RatFunc.X : RatFunc k)) :=
    originalQuotientAlgebra k
  exact (quadraticEquiv k).toLinearEquiv.finrank_eq.symm.trans
    (finrank (RatFunc.X : RatFunc k))

variable [CharP k 2]

/-- Every square is in the actual image, without requiring square roots in k. -/
theorem squareHom_square_mem_range (z : RatFunc k) :
    ∃ a : RatFunc k, squareHom k a = z ^ 2 := by
  letI : CharP (RatFunc k) 2 := charP_of_injective_algebraMap' k (RatFunc k) 2
  obtain ⟨w, rfl⟩ := quadraticMap_surjective k z
  let a := constantCoeff RatFunc.X w
  let b := rootCoeff RatFunc.X w
  have hw : quadraticMap k w = squareHom k a + squareHom k b * RatFunc.X := by
    have h := congrArg (quadraticMap k) (ofCoeffs_coefficients RatFunc.X w)
    simpa only [ofCoeffs, map_add, map_mul, quadraticMap_algebraMap,
      quadraticMap_root] using h.symm
  refine ⟨a ^ 2 + b ^ 2 * RatFunc.X, ?_⟩
  rw [hw]
  simp only [map_add, map_mul, map_pow, squareHom_X, add_pow_char, mul_pow]

/-- Pure inseparability is proved for the original coefficient-fixed square map. -/
theorem squareHom_isPurelyInseparable :
    letI : Algebra (RatFunc k) (RatFunc k) := (squareHom k).toRingHom.toAlgebra
    IsPurelyInseparable (RatFunc k) (RatFunc k) := by
  letI : Algebra (RatFunc k) (RatFunc k) := (squareHom k).toRingHom.toAlgebra
  letI : CharP (RatFunc k) 2 := charP_of_injective_algebraMap' k (RatFunc k) 2
  apply (isPurelyInseparable_iff_pow_mem (RatFunc k) 2).2
  intro z
  obtain ⟨a, ha⟩ := squareHom_square_mem_range k z
  exact ⟨1, a, by simpa only [pow_one] using ha⟩

end KltDP.Examples.FrobeniusSquareRationalMap

import KltDP.Compatibility.ClosedAlgebraResidue
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.RingTheory.FiniteType

/-!
# The equation of an actual closed point of the affine line

The existing canonical closed-residue character identifies the given
maximal ideal with the kernel of polynomial evaluation. No chosen
residue-field identification or point equation is assumed.
-/

noncomputable section

namespace KltDP.Geometry.PolynomialClosedPointEquation

open Polynomial

universe u

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- An actual maximal ideal of the original polynomial ring is generated
by the variable minus a scalar from the original field. -/
theorem exists_eq_span (P : Ideal (Polynomial k)) [P.IsMaximal] :
    ∃ c : k, P = Ideal.span {X - C c} := by
  letI : Algebra.FiniteType k (Polynomial k) := Algebra.FiniteType.polynomial k
  let χ : Polynomial k →ₐ[k] k := KltDP.Compatibility.closedPointCharacter k P
  have hχ : χ = aeval (χ X) :=
    Polynomial.algHom_ext (by rw [Polynomial.aeval_X])
  refine ⟨χ X, ?_⟩
  calc
    P = RingHom.ker χ.toRingHom :=
      (KltDP.Compatibility.closedPointCharacter_ker k P).symm
    _ = RingHom.ker (evalRingHom (χ X)) :=
      congrArg (fun h : Polynomial k →ₐ[k] k => RingHom.ker h.toRingHom) hχ
    _ = Ideal.span {X - C (χ X)} := Polynomial.ker_evalRingHom _

end KltDP.Geometry.PolynomialClosedPointEquation

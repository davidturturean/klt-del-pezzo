import KltDP.Geometry.PrimeCurveResidueBase

/-!
# Discharging the residue-field finiteness hypothesis

`finrank_quotient_span_eq_localLength_mul` computes `dim_k (O_{C,y} ⧸ (f))` as
`localLength · [κ(y) : k]` under the hypothesis that `κ(y) = O_{C,y} ⧸ m_y` is finite
over `k` for the quotient-algebra structure induced by `stalkBaseMap`. This module
discharges that hypothesis at closed points: the quotient-algebra structure equals the
algebra structure induced by `stalkBaseResidueMap` (both `algebraMap`s are
`residue ∘ stalkBaseMap`, so `Algebra.algebra_ext` applies), and the latter is finite
by `stalkBaseResidueMap_finite`. Over an algebraically closed field the residue field
is one dimensional (`stalkBaseResidueMap_bijective`), so
`dim_k (O_{C,y} ⧸ (f)) = localLength C y f` at closed DVR points.

The sum formula for `intersectionDegree` is not proved here; see
`F03_RESTRICTION_ADAPTERS.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.RingTheory

/-- `Module.Finite` transported along an equality of algebra structures. -/
theorem module_finite_of_algebra_eq {R A : Type*} [CommSemiring R] [Semiring A]
    (P Q : Algebra R A) (h : P = Q) (hP : haveI := P; Module.Finite R A) :
    haveI := Q; Module.Finite R A := by
  subst h
  exact hP

end KltDP.RingTheory

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve) (y : C.toScheme)

/-- Stalks of the integral curve scheme are domains. -/
local instance primeCurveResidueFinrank_stalkIsDomain :
    IsDomain (C.toScheme.presheaf.stalk y) :=
  integralSchemeStalk_isDomain C.toScheme y

/-- The algebra structure on `κ(y)` induced by `stalkBaseResidueMap` is the quotient-algebra
structure of the `stalkBaseMap`-algebra structure on the stalk. -/
theorem toAlgebra_stalkBaseResidueMap :
    letI := (C.stalkBaseMap y).toAlgebra
    (C.stalkBaseResidueMap y).hom.toAlgebra =
      (Ideal.Quotient.algebra k : Algebra k (C.toScheme.presheaf.stalk y ⧸
        IsLocalRing.maximalIdeal (C.toScheme.presheaf.stalk y))) := by
  letI := (C.stalkBaseMap y).toAlgebra
  exact Algebra.algebra_ext _ _ fun _ => rfl

/-- At a closed point the residue field `κ(y)` is finite over `k` for the quotient-algebra
structure induced by `stalkBaseMap`. -/
theorem residue_module_finite (hclosed : IsClosed ({y} : Set C.toScheme)) :
    letI := (C.stalkBaseMap y).toAlgebra
    Module.Finite k (C.toScheme.presheaf.stalk y ⧸
      IsLocalRing.maximalIdeal (C.toScheme.presheaf.stalk y)) := by
  letI := (C.stalkBaseMap y).toAlgebra
  exact KltDP.RingTheory.module_finite_of_algebra_eq (R := k)
    (A := C.toScheme.presheaf.stalk y ⧸ IsLocalRing.maximalIdeal (C.toScheme.presheaf.stalk y))
    (C.stalkBaseResidueMap y).hom.toAlgebra _ (C.toAlgebra_stalkBaseResidueMap y)
    (C.stalkBaseResidueMap_finite y hclosed)

/-- Over an algebraically closed field, `[κ(y) : k] = 1` at a closed point. -/
theorem finrank_residue_eq_one [IsAlgClosed k] (hclosed : IsClosed ({y} : Set C.toScheme)) :
    letI := (C.stalkBaseMap y).toAlgebra
    Module.finrank k (C.toScheme.presheaf.stalk y ⧸
      IsLocalRing.maximalIdeal (C.toScheme.presheaf.stalk y)) = 1 := by
  letI := (C.stalkBaseMap y).toAlgebra
  have h := C.stalkBaseResidueMap_bijective y hclosed
  have hbij : Function.Bijective (Algebra.linearMap k (C.toScheme.presheaf.stalk y ⧸
      IsLocalRing.maximalIdeal (C.toScheme.presheaf.stalk y))) := by
    rw [Algebra.coe_linearMap]
    exact h
  rw [← (LinearEquiv.ofBijective _ hbij).finrank_eq, Module.finrank_self]

variable [IsDiscreteValuationRing (C.toScheme.presheaf.stalk y)]

/-- `dim_k (O_{C,y} ⧸ (f)) = localLength · [κ(y) : k]` at a closed DVR point, with no
finiteness hypothesis. -/
theorem finrank_quotient_span_eq_localLength_mul_of_isClosed
    (f : C.toScheme.presheaf.stalk y) (hf : f ≠ 0) (hclosed : IsClosed ({y} : Set C.toScheme)) :
    letI := (C.stalkBaseMap y).toAlgebra
    Module.finrank k (C.toScheme.presheaf.stalk y ⧸ Ideal.span {f}) =
      C.localLength y f *
        Module.finrank k (C.toScheme.presheaf.stalk y ⧸
          IsLocalRing.maximalIdeal (C.toScheme.presheaf.stalk y)) :=
  C.finrank_quotient_span_eq_localLength_mul y f hf (C.residue_module_finite y hclosed)

/-- Over an algebraically closed field, `dim_k (O_{C,y} ⧸ (f)) = localLength C y f` at a
closed DVR point. -/
theorem finrank_quotient_span_eq_localLength [IsAlgClosed k]
    (f : C.toScheme.presheaf.stalk y) (hf : f ≠ 0) (hclosed : IsClosed ({y} : Set C.toScheme)) :
    letI := (C.stalkBaseMap y).toAlgebra
    Module.finrank k (C.toScheme.presheaf.stalk y ⧸ Ideal.span {f}) = C.localLength y f := by
  letI := (C.stalkBaseMap y).toAlgebra
  have h1 : Module.finrank k (C.toScheme.presheaf.stalk y ⧸ Ideal.span {f}) =
      C.localLength y f *
        Module.finrank k (C.toScheme.presheaf.stalk y ⧸
          IsLocalRing.maximalIdeal (C.toScheme.presheaf.stalk y)) :=
    C.finrank_quotient_span_eq_localLength_mul_of_isClosed y f hf hclosed
  have h2 : Module.finrank k (C.toScheme.presheaf.stalk y ⧸
      IsLocalRing.maximalIdeal (C.toScheme.presheaf.stalk y)) = 1 :=
    C.finrank_residue_eq_one y hclosed
  rw [h1, h2, mul_one]

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

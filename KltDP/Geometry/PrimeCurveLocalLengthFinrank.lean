import KltDP.Geometry.PrimeCurveLocalLength
import KltDP.Geometry.ProperGlobalSectionsFinite
import KltDP.RingTheory.LocalLengthFinrank

/-!
# `k`-dimension of the local contribution on the curve

The stalk `O_{C,y}` is a `k`-algebra through the structure morphism (base field →
global sections → germ). For a nonzero stalk element `f` at a DVR point `y`,
`O_{C,y} ⧸ (f)` has finite length, so by `KltDP.RingTheory.LocalLengthFinrank`
its `k`-dimension is `localLength · [κ(y) : k]`, where `[κ(y) : k]` is the dimension
of the residue field `O_{C,y} ⧸ m_y` for the same induced `k`-structure, assumed
finite here.

Not proved here: that this induced `k → κ(y)` is the accepted
`baseToResidueFieldMap C.toSpec y` (which would supply finiteness at closed points
and `[κ(y):k] = 1` over an algebraically closed field), and the sum formula for
`intersectionDegree`; see `F03_RESTRICTION_ADAPTERS.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve) (y : C.toScheme)

/-- Stalks of the integral curve scheme are domains. -/
local instance primeCurveLocalLengthFinrank_stalkIsDomain :
    IsDomain (C.toScheme.presheaf.stalk y) :=
  integralSchemeStalk_isDomain C.toScheme y

/-- The base field acting on the stalk through the original structure morphism:
`k → Γ(C, ⊤) → O_{C,y}`. -/
def stalkBaseMap : k →+* C.toScheme.presheaf.stalk y :=
  (C.toScheme.presheaf.germ ⊤ y trivial).hom.comp (baseFieldToGlobalSections C.toSpec)

variable [IsDiscreteValuationRing (C.toScheme.presheaf.stalk y)]

/-- The quotient by a nonzero stalk element has finite length over the DVR stalk. -/
theorem isFiniteLength_quotient_span (f : C.toScheme.presheaf.stalk y) (hf : f ≠ 0) :
    IsFiniteLength (C.toScheme.presheaf.stalk y)
      (C.toScheme.presheaf.stalk y ⧸ Ideal.span {f}) :=
  Module.length_ne_top_iff.mp (C.localLength_length_ne_top y f hf)

/-- `dim_k (O_{C,y} ⧸ (f)) = localLength · [κ(y) : k]`, for the induced `k`-structure,
when the residue field `κ(y) = O_{C,y} ⧸ m_y` is finite dimensional over `k`. -/
theorem finrank_quotient_span_eq_localLength_mul (f : C.toScheme.presheaf.stalk y) (hf : f ≠ 0)
    (hκ : letI := (C.stalkBaseMap y).toAlgebra
      Module.Finite k (C.toScheme.presheaf.stalk y ⧸
        IsLocalRing.maximalIdeal (C.toScheme.presheaf.stalk y))) :
    letI := (C.stalkBaseMap y).toAlgebra
    Module.finrank k (C.toScheme.presheaf.stalk y ⧸ Ideal.span {f}) =
      C.localLength y f *
        Module.finrank k (C.toScheme.presheaf.stalk y ⧸
          IsLocalRing.maximalIdeal (C.toScheme.presheaf.stalk y)) := by
  letI := (C.stalkBaseMap y).toAlgebra
  haveI := hκ
  exact (KltDP.RingTheory.finite_and_finrank_eq_length_mul_finrank_residue (k := k)
    (C.toScheme.presheaf.stalk y ⧸ Ideal.span {f}) (C.isFiniteLength_quotient_span y f hf)).2

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

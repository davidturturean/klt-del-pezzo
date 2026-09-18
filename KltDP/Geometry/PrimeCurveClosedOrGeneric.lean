import KltDP.Geometry.PrimeCurveGenericStalkParameter
import KltDP.Geometry.PointClosureCurve
import KltDP.Geometry.MinimalResolutionCount

/-!
# Every original prime-curve point is closed or generic

The existing normal-surface point-closure construction turns a nongeneric
nonclosed ambient point into a prime curve. Its containment in the given
prime curve forces equality. The original closed inclusion then identifies
the original point as the generic point of the original curve scheme.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)

/-- The closed/generic dichotomy on the actual reduced prime-curve scheme. -/
theorem isClosed_or_eq_genericPoint (y : C.toScheme) :
    IsClosed ({y} : Set C.toScheme) ∨ y = _root_.genericPoint C.toScheme := by
  by_cases hy : IsClosed ({y} : Set C.toScheme)
  · exact Or.inl hy
  right
  let x := C.inclusion.base y
  have hxC : x ∈ (C : Set X.toScheme) := C.inclusion_base_mem y
  have hx : ¬ IsClosed ({x} : Set X.toScheme) := by
    intro h
    apply hy
    apply C.inclusion.isClosedEmbedding.isClosed_iff_image_isClosed.mpr
    simpa only [Set.image_singleton] using h
  have hη : x ≠ _root_.genericPoint X.toScheme := by
    intro h
    have hc : closure ({x} : Set X.toScheme) ⊆ (C : Set X.toScheme) :=
      closure_minimal (Set.singleton_subset_iff.mpr hxC) C.isClosed
    rw [h, (genericPoint_spec X.toScheme).def] at hc
    exact C.ne_univ (Set.Subset.antisymm (Set.subset_univ _) hc)
  let E := X.primeCurveOfNonclosedPoint x hη hx
  have hEC : E = C := by
    apply PrimeCurve.ext
    apply E.coe_eq_of_subset_irreducibleCloseds C.1 _ C.ne_univ
    exact closure_minimal (Set.singleton_subset_iff.mpr hxC) C.isClosed
  have hxη : x = C.genericPoint :=
    (X.primeCurveOfNonclosedPoint_genericPoint x hη hx).symm.trans
      (congrArg (fun P : X.PrimeCurve => P.genericPoint) hEC)
  apply C.inclusion.isClosedEmbedding.injective
  exact hxη.trans C.inclusion_genericPoint_eq.symm

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

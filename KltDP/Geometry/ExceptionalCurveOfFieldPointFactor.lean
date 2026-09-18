import KltDP.Geometry.Resolution
import KltDP.Geometry.PrimeCurvePointFiberFactorization

/-! An original field-point factorization contracts the actual prime carrier. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k] {X Y : NormalProjectiveSurface k}

/-- The original scheme factorization implies the accepted exceptional-curve predicate. -/
theorem IsExceptionalCurve.of_fieldPoint_factor
    (π : X.toScheme ⟶ Y.toScheme) (C : X.PrimeCurve)
    (p : Spec (CommRingCat.of k) ⟶ Y.toScheme)
    (h : C.inclusion ≫ π = C.toSpec ≫ p) : IsExceptionalCurve π C := by
  have hbase := PrimeCurvePointFiberFactorization.base_eq_on_prime_of_factor X C π p h
  refine ⟨fieldMorphismPoint p, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact Set.mem_singleton_iff.mpr (hbase x hx)
  · exact Set.singleton_subset_iff.mpr
      ⟨C.genericPoint, C.genericPoint_mem, hbase C.genericPoint C.genericPoint_mem⟩

end KltDP.Geometry

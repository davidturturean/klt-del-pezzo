import KltDP.Geometry.PrimeCurveExistence
import KltDP.Geometry.PrimeCurveCodimension

/-!
# Curves obtained from closures of actual surface points

The closure of a nongeneric point on an integral surface has dimension at
most one. If the point is also nonclosed, the closure has dimension one
and therefore defines a prime curve in the existing geometric carrier.

These are topological dimension arguments, using the actual order of
irreducible closed subsets. They do not infer nonclosedness from stalk
height one. That further finite-type dimension argument is separate.
The order-height and generic-point APIs are imported from the unchanged
Mathlib pin; the closed-subspace dimension adapter is already proved in
`PrimeCurveExistence`.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The actual irreducible closed closure of a scheme point. -/
def pointClosure (x : X.toScheme) : IrreducibleCloseds X.toScheme :=
  ⟨closure ({x} : Set X.toScheme), isIrreducible_singleton.closure, isClosed_closure⟩

/-- A proper point closure has dimension at most one on the surface. -/
theorem pointClosure_dimension_le_one (x : X.toScheme)
    (hx : x ≠ genericPoint X.toScheme) :
    topologicalKrullDim (X.pointClosure x : Set X.toScheme) ≤ 1 := by
  let Z := X.pointClosure x
  let T : IrreducibleCloseds X.toScheme :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X.toScheme, isClosed_univ⟩
  have hZT : Z < T := by
    refine lt_of_le_of_ne (Set.subset_univ _) ?_
    intro h
    have hgeneric : IsGenericPoint x (Set.univ : Set X.toScheme) :=
      congrArg (fun W : IrreducibleCloseds X.toScheme => (W : Set X.toScheme)) h
    exact hx (hgeneric.eq (genericPoint_spec X.toScheme))
  have hT : Order.height T ≤ (2 : ℕ∞) := by
    have h := Order.height_le_krullDim T
    rw [show Order.krullDim (IrreducibleCloseds X.toScheme) = 2 from X.dimension_two] at h
    exact WithBot.coe_le_coe.mp h
  have hZlt : Order.height Z < (2 : ℕ∞) :=
    (Order.height_le_coe_iff (x := T) (n := 2)).mp hT Z hZT
  have hZ : Order.height Z ≤ (1 : ℕ∞) := by
    apply (ENat.lt_add_one_iff (by simp : (1 : ℕ∞) ≠ ⊤)).mp
    simpa only [one_add_one_eq_two] using hZlt
  rw [KltDP.Topology.topologicalKrullDim_irreducibleClosed_eq_height]
  exact WithBot.coe_le_coe.mpr hZ

/-- A nonclosed point has a positive-dimensional actual closure. -/
theorem one_le_pointClosure_dimension (x : X.toScheme)
    (hx : ¬ IsClosed ({x} : Set X.toScheme)) :
    1 ≤ topologicalKrullDim (X.pointClosure x : Set X.toScheme) := by
  have hnot : ¬ closure ({x} : Set X.toScheme) ⊆ {x} :=
    fun h => hx (isClosed_of_closure_subset h)
  obtain ⟨y, hy, hyne⟩ := Set.not_subset.mp hnot
  have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
  have hyx : X.pointClosure y < X.pointClosure x := by
    refine lt_of_le_of_ne hxy.closure_subset ?_
    intro h
    have hgen : IsGenericPoint y (closure ({x} : Set X.toScheme)) :=
      congrArg (fun W : IrreducibleCloseds X.toScheme => (W : Set X.toScheme)) h
    exact hyne (hgen.eq isGenericPoint_closure)
  have hheight : (1 : ℕ∞) ≤ Order.height (X.pointClosure x) := by
    have h := Order.height_add_one_le hyx
    exact le_trans (by simpa only [zero_add] using
      (add_le_add_right (zero_le (Order.height (X.pointClosure y))) 1)) h
  rw [KltDP.Topology.topologicalKrullDim_irreducibleClosed_eq_height]
  exact WithBot.coe_le_coe.mpr hheight

/-- A nongeneric nonclosed point has an actual one-dimensional closure. -/
theorem pointClosure_dimension_eq_one (x : X.toScheme)
    (hgeneric : x ≠ genericPoint X.toScheme)
    (hclosed : ¬ IsClosed ({x} : Set X.toScheme)) :
    topologicalKrullDim (X.pointClosure x : Set X.toScheme) = 1 :=
  le_antisymm (X.pointClosure_dimension_le_one x hgeneric)
    (X.one_le_pointClosure_dimension x hclosed)

/-- The actual prime curve given by a nongeneric nonclosed point. Both
point conditions are explicit; neither is a supplied curve or divisor. -/
def primeCurveOfNonclosedPoint (x : X.toScheme)
    (hgeneric : x ≠ genericPoint X.toScheme)
    (hclosed : ¬ IsClosed ({x} : Set X.toScheme)) : X.PrimeCurve :=
  ⟨X.pointClosure x, X.pointClosure_dimension_eq_one x hgeneric hclosed⟩

@[simp]
theorem primeCurveOfNonclosedPoint_genericPoint (x : X.toScheme)
    (hgeneric : x ≠ genericPoint X.toScheme)
    (hclosed : ¬ IsClosed ({x} : Set X.toScheme)) :
    (X.primeCurveOfNonclosedPoint x hgeneric hclosed).genericPoint = x := by
  let C := X.primeCurveOfNonclosedPoint x hgeneric hclosed
  have hC : IsGenericPoint C.genericPoint (C : Set X.toScheme) :=
    C.isIrreducible.isGenericPoint_genericPoint C.isClosed
  exact hC.eq isGenericPoint_closure

/-- The constructed curve consists of the actual specializations of the
point used to construct it. -/
theorem mem_primeCurveOfNonclosedPoint (x y : X.toScheme)
    (hgeneric : x ≠ genericPoint X.toScheme)
    (hclosed : ¬ IsClosed ({x} : Set X.toScheme)) :
    y ∈ X.primeCurveOfNonclosedPoint x hgeneric hclosed ↔ x ⤳ y :=
  specializes_iff_mem_closure.symm

end KltDP.Geometry.NormalProjectiveSurface

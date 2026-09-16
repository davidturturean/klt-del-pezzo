import KltDP.Geometry.PointClosureCurve
import KltDP.Geometry.ClosedPointDimension
import KltDP.Geometry.CodimensionOneOpen

/-!
# Actual codimension-one point closures on an integral surface

This generalizes the existing `PointClosureCurve` order-height argument
from its normal-projective-surface wrapper to an actual integral scheme
whose global dimension is proved to be two. Finite type over the original
algebraically closed field excludes closed points with local dimension one.
No normality, projectivity or surface bundle is assumed of the new scheme.

The conclusion measures the dimension of the actual point closure. It
therefore supplies the missing dimension-one support proof when the
constructed point blowup has only its integral scheme and derived dimension.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace KltDP.Geometry.IntegralSurfacePointClosure

variable (X : Scheme.{u}) [IsIntegral X]

/-- The actual irreducible closed point closure in the given scheme. -/
def pointClosure (x : X) : IrreducibleCloseds X :=
  ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩

/-- A proper point closure lies strictly below the whole irreducible
surface in its actual order of irreducible closed subsets. -/
theorem pointClosure_dimension_le_one (hdim : topologicalKrullDim X = 2)
    (x : X) (hx : x ≠ genericPoint X) :
    topologicalKrullDim (pointClosure X x : Set X) ≤ 1 := by
  let Z := pointClosure X x
  let T : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hZT : Z < T := by
    refine lt_of_le_of_ne (Set.subset_univ _) ?_
    intro h
    have hgeneric : IsGenericPoint x (Set.univ : Set X) :=
      congrArg (fun W : IrreducibleCloseds X => (W : Set X)) h
    exact hx (hgeneric.eq (genericPoint_spec X))
  have hT : Order.height T ≤ (2 : ℕ∞) := by
    have h := Order.height_le_krullDim T
    rw [show Order.krullDim (IrreducibleCloseds X) = 2 from hdim] at h
    exact WithBot.coe_le_coe.mp h
  have hZlt : Order.height Z < (2 : ℕ∞) :=
    (Order.height_le_coe_iff (x := T) (n := 2)).mp hT Z hZT
  have hZ : Order.height Z ≤ (1 : ℕ∞) := by
    apply (ENat.lt_add_one_iff (by simp : (1 : ℕ∞) ≠ ⊤)).mp
    simpa only [one_add_one_eq_two] using hZlt
  rw [KltDP.Topology.topologicalKrullDim_irreducibleClosed_eq_height]
  exact WithBot.coe_le_coe.mpr hZ

/-- A nonclosed actual point has positive-dimensional closure. -/
theorem one_le_pointClosure_dimension (x : X) (hx : ¬ IsClosed ({x} : Set X)) :
    1 ≤ topologicalKrullDim (pointClosure X x : Set X) := by
  have hnot : ¬ closure ({x} : Set X) ⊆ {x} :=
    fun h => hx (isClosed_of_closure_subset h)
  obtain ⟨y, hy, hyne⟩ := Set.not_subset.mp hnot
  have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
  have hyx : pointClosure X y < pointClosure X x := by
    refine lt_of_le_of_ne hxy.closure_subset ?_
    intro h
    have hgen : IsGenericPoint y (closure ({x} : Set X)) :=
      congrArg (fun W : IrreducibleCloseds X => (W : Set X)) h
    exact hyne (hgen.eq isGenericPoint_closure)
  have hheight : (1 : ℕ∞) ≤ Order.height (pointClosure X x) := by
    have h := Order.height_add_one_le hyx
    exact le_trans (by simpa only [zero_add] using
      (add_le_add_right (zero_le (Order.height (pointClosure X y))) 1)) h
  rw [KltDP.Topology.topologicalKrullDim_irreducibleClosed_eq_height]
  exact WithBot.coe_le_coe.mpr hheight

/-- On an actual integral surface of finite type, a point of actual
local dimension one has actual closure dimension one. -/
theorem codimensionOnePoint_closure_dimension_one
    {k : Type u} [Field k] [IsAlgClosed k]
    (g : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (hdim : topologicalKrullDim X = 2) (x : CodimensionOnePoint X) :
    topologicalKrullDim (closure ({x.val} : Set X)) = 1 := by
  have hgeneric : x.val ≠ genericPoint X := by
    intro h
    have hd := x.property
    rw [h] at hd
    change ringKrullDim X.functionField = 1 at hd
    rw [ringKrullDim_eq_zero_of_field] at hd
    norm_num at hd
  have hclosed : ¬ IsClosed ({x.val} : Set X) := by
    intro h
    have hd := closed_stalk_dimension_eq_global X g x.val h
    rw [x.property, hdim] at hd
    norm_num at hd
  exact le_antisymm (pointClosure_dimension_le_one X hdim x.val hgeneric)
    (one_le_pointClosure_dimension X x.val hclosed)

end KltDP.Geometry.IntegralSurfacePointClosure

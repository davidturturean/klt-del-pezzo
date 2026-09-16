import KltDP.Geometry.IntegralSurfacePointClosure

/-!
# Prime curves on actual integral schemes of dimension two

This uses the same dimension-one irreducible closed carrier as the
manuscript's surface curve type, without requiring normality or projectivity
of an intermediate constructed scheme. The point/curve equivalence is
proved from actual stalk dimensions and closures. All dimension inputs
are the scheme's original topological Krull dimension, not curve data.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace KltDP.Geometry.IntegralSurfacePointClosure

variable (X : Scheme.{u}) [IsIntegral X]

/-- The actual dimension-one irreducible closed subsets of the scheme. -/
def Curve := {Z : IrreducibleCloseds X // topologicalKrullDim (Z : Set X) = 1}

/-- The actual generic point of the selected irreducible closed curve. -/
def curveGenericPoint (C : Curve X) : X := C.val.isIrreducible.genericPoint

theorem curveGenericPoint_closure (C : Curve X) :
    closure ({curveGenericPoint X C} : Set X) = (C.val : Set X) :=
  C.val.isIrreducible.closure_genericPoint C.val.isClosed

theorem curveGenericPoint_injective : Function.Injective (curveGenericPoint X) := by
  intro C D h
  apply Subtype.ext
  apply IrreducibleCloseds.ext
  rw [← curveGenericPoint_closure X C, ← curveGenericPoint_closure X D, h]

/-- Dimension one prevents the actual curve generic point from being
closed, independently of any finite-type or normality argument. -/
theorem curveGenericPoint_not_isClosed (C : Curve X) :
    ¬ IsClosed ({curveGenericPoint X C} : Set X) := by
  intro hclosed
  have heq : (C.val : Set X) = {curveGenericPoint X C} := by
    rw [← curveGenericPoint_closure X C, hclosed.closure_eq]
  have hd := C.property
  rw [heq] at hd
  have hnonpos := KltDP.Geometry.topologicalKrullDim_nonpos_of_subsingleton
    ({curveGenericPoint X C} : Set X)
  rw [hd] at hnonpos
  have hpos : (0 : WithBot ℕ∞) < 1 :=
    WithBot.coe_lt_coe.mpr (by simp : (0 : ℕ∞) < 1)
  exact hpos.not_le hnonpos

theorem curveGenericPoint_ne_genericPoint (hdim : topologicalKrullDim X = 2)
    (C : Curve X) : curveGenericPoint X C ≠ genericPoint X := by
  intro h
  have heq : (C.val : Set X) = Set.univ := by
    rw [← curveGenericPoint_closure X C, h, genericPoint_closure]
  have hd := C.property
  rw [heq] at hd
  have hwhole : topologicalKrullDim (Set.univ : Set X) = topologicalKrullDim X :=
    IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ X)
      (Homeomorph.Set.univ X).isHomeomorph
  rw [hwhole, hdim] at hd
  norm_num at hd

/-- The actual curve generic point has local-ring dimension one, using
the two directions of the existing surface dimension comparison. -/
theorem curveGenericPoint_stalk_dimension (hdim : topologicalKrullDim X = 2)
    (C : Curve X) : ringKrullDim (X.presheaf.stalk (curveGenericPoint X C)) = 1 := by
  apply le_antisymm
  · exact ringKrullDim_stalk_le_one_of_not_isClosed_singleton X hdim.le
      (curveGenericPoint X C) (curveGenericPoint_not_isClosed X C)
  · exact one_le_ringKrullDim_stalk_of_ne_genericPoint X (curveGenericPoint X C)
      (curveGenericPoint_ne_genericPoint X hdim C)

/-- Actual curves correspond bijectively to actual codimension-one
points, with inverse given by the actual point closure. -/
def curveCodimensionOneEquiv
    {k : Type u} [Field k] [IsAlgClosed k]
    (g : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (hdim : topologicalKrullDim X = 2) : Curve X ≃ CodimensionOnePoint X where
  toFun C := ⟨curveGenericPoint X C, curveGenericPoint_stalk_dimension X hdim C⟩
  invFun x := ⟨pointClosure X x.val,
    codimensionOnePoint_closure_dimension_one X g hdim x⟩
  left_inv C := by
    apply Subtype.ext
    apply IrreducibleCloseds.ext
    exact curveGenericPoint_closure X C
  right_inv x := by
    apply Subtype.ext
    exact ((pointClosure X x.val).isIrreducible.isGenericPoint_genericPoint
      (pointClosure X x.val).isClosed).eq isGenericPoint_closure

end KltDP.Geometry.IntegralSurfacePointClosure

import KltDP.Geometry.SchemeDimensionFromStalks
import KltDP.Geometry.GenericFiberStalkIso
import KltDP.Geometry.PrimeCurveCodimension
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! The original generic fiber of a proper surface-to-curve map has
dimension at most one: its points have nonclosed images in the surface. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.GenericSurfaceFiberDimensionBound

theorem genericPoint_not_closed (Y : Scheme.{u}) [IsIntegral Y]
    (hdim : topologicalKrullDim Y = 1) :
    ¬ IsClosed ({genericPoint Y} : Set Y) := by
  intro hc
  have hs : ({genericPoint Y} : Set Y) = Set.univ :=
    hc.closure_eq.symm.trans (genericPoint_spec Y).def
  have he (y : Y) : y = genericPoint Y := by
    have hy : y ∈ ({genericPoint Y} : Set Y) := hs.symm ▸ Set.mem_univ y
    exact hy
  letI : Subsingleton Y := ⟨fun x y => (he x).trans (he y).symm⟩
  have hnonpos := topologicalKrullDim_nonpos_of_subsingleton Y
  rw [hdim] at hnonpos
  exact (WithBot.coe_lt_coe.mpr (by simp : (0 : ℕ∞) < 1)).not_le hnonpos

theorem dimension_le_one {X Y : Scheme.{u}} [IsIntegral Y]
    (f : X ⟶ Y) [IsProper f]
    (hX : topologicalKrullDim X ≤ 2) (hY : topologicalKrullDim Y = 1) :
    topologicalKrullDim (f.fiber (genericPoint Y)) ≤ 1 := by
  apply SchemeDimensionFromStalks.bound
  intro x
  have hmap : f.base ((f.fiberι (genericPoint Y)).base x) = genericPoint Y :=
    (f.fiberHomeo (genericPoint Y) x).property
  have hnc : ¬ IsClosed ({(f.fiberι (genericPoint Y)).base x} : Set X) := by
    intro hc
    apply genericPoint_not_closed Y hY
    simpa only [Set.image_singleton, hmap] using
      f.isClosedMap _ hc
  exact (ringKrullDim_eq_of_ringEquiv
    (GenericFiberStalkIso.stalkIso f x).commRingCatIsoToRingEquiv).symm.le.trans
      (ringKrullDim_stalk_le_one_of_not_isClosed_singleton X hX _ hnc)

#print axioms dimension_le_one

end KltDP.Geometry.GenericSurfaceFiberDimensionBound

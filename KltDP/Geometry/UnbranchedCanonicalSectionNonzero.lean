import KltDP.Geometry.SheafSectionPullbackCoefficient
import KltDP.Geometry.PrimeCurveCartierRestriction

/-! # The original Cartier section stays nonzero away from its branch scheme -/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u

namespace KltDP.Geometry.UnbranchedCanonicalSection

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- Disjointness from the actual zero scheme prevents the literal pulled section
from vanishing. No dominant map or nonzero-section premise is required. -/
theorem pulledSection_ne_zero {X C : Scheme.{u}} [IsIntegral X] [Nonempty C]
    (E : CartierDivisor X) (hE : HasRegularCartierEquations X E) (f : C ⟶ X)
    (hdisj : Disjoint (Set.range f.base)
      (Set.range (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo.base)) :
    RationalTreePicard.pulledSection f (cartierDivisorModule X E) ⊤
      (effectiveCartierSection X E hE) ≠ 0 := by
  classical
  intro hz
  let z : C := Classical.arbitrary C
  obtain ⟨c, hzc⟩ := hE (f.base z)
  have hnot : f.base z ∉ (effectiveCartierIdealDataOfRegularEquations X E hE).support := by
    change f.base z ∉ ((effectiveCartierIdealDataOfRegularEquations X E hE).support : Set X)
    rw [← Scheme.IdealSheafData.range_gluedTo]
    exact Set.disjoint_left.mp hdisj (Set.mem_range_self z)
  have hcunit : IsUnit (X.presheaf.germ c.chart.openSet (f.base z) hzc c.coefficient) := by
    apply Classical.byContradiction
    intro hn
    exact hnot ((NormalProjectiveSurface.PrimeCurve.mem_support_iff_not_isUnit_germ
      E hE c (f.base z) hzc).2 hn)
  let τ := cartierEquationOverIso X E c.chart.openSet c.chart.equation c.chart.represents
  have heval : τ.inv.val.app (op (Over.mk (𝟙 c.chart.openSet)))
      ((cartierDivisorModule X E).val.map (homOfLE (le_top : c.chart.openSet ≤ ⊤)).op
        (effectiveCartierSection X E hE)) = c.coefficient := by
    have h := effectiveCartierSection_frame_eval X E hE c
    have hid : (cartierDivisorModule X E).val.map (𝟙 c.chart.openSet).op
        ((cartierDivisorModule X E).val.map (homOfLE (le_top : c.chart.openSet ≤ ⊤)).op
          (effectiveCartierSection X E hE)) =
        (cartierDivisorModule X E).val.map (homOfLE (le_top : c.chart.openSet ≤ ⊤)).op
          (effectiveCartierSection X E hE) :=
      CategoryTheory.congr_fun ((cartierDivisorModule X E).val.presheaf.map_id
        (op c.chart.openSet)) _
    change τ.inv.val.app (op (Over.mk (𝟙 c.chart.openSet)))
      ((cartierDivisorModule X E).val.map (𝟙 c.chart.openSet).op _) = c.coefficient at h
    rw [hid] at h
    exact h
  have hn := SheafSectionPullbackCoefficient.not_isUnit_germ_of_global_pulledSection_eq_zero
    f (cartierDivisorModule X E) (effectiveCartierSection X E hE) hz
    c.chart.openSet τ.symm z hzc
  change ¬ IsUnit (X.presheaf.germ c.chart.openSet (f.base z) hzc
    (τ.inv.val.app (op (Over.mk (𝟙 c.chart.openSet)))
      ((cartierDivisorModule X E).val.map (homOfLE (le_top : c.chart.openSet ≤ ⊤)).op
        (effectiveCartierSection X E hE)))) at hn
  rw [heval] at hn
  exact hn hcunit

end KltDP.Geometry.UnbranchedCanonicalSection

#print axioms KltDP.Geometry.UnbranchedCanonicalSection.pulledSection_ne_zero

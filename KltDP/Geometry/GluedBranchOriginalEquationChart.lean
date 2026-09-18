import KltDP.Geometry.GluedAdjunctionChartBasis
import KltDP.Geometry.TransitionUnitSheaf

/-!
# Simultaneous smooth branch charts subordinate to an original coefficient

The existing simultaneous charts are refined inside a prescribed original
affine open. The ideal restriction law retains the original branch
coefficient, and integral-scheme restriction injectivity retains its
regularity. No new equation or atlas equivalence replaces that coefficient.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.GluedBranchOriginalEquationChart

open GluedAdjunctionChartBasis TransitionUnitGluing

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
variable (f : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
variable (hI : IdealLocallyPrincipalRegular I)
variable [IsSmoothOfRelativeDimension 2 f] [IsSmoothOfRelativeDimension 1 (I.gluedTo ≫ f)]

include hI in
/-- A branch point in a prescribed original coefficient chart has a
simultaneous smooth subchart carrying the restriction of that same coefficient. -/
theorem exists_subordinate (U : X.affineOpens) (s : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {s}) (hs : s ∈ nonZeroDivisors Γ(X, U.1))
    (x : I.glueData.glued) (hx : I.gluedTo.base x ∈ U.1) :
    ∃ c : Chart f I, ∃ hc : c.U.1 ≤ U.1,
      x ∈ c.sourceOpen ∧
      I.ideal c.U = Ideal.span {res X hc s} ∧
      res X hc s ∈ nonZeroDivisors Γ(X, c.U.1) := by
  obtain ⟨c, hxc⟩ := GluedAdjunctionChartBasis.exists_mem f I hI x
  obtain ⟨r, hr, hxr⟩ := c.U.2.exists_basicOpen_le ⟨I.gluedTo.base x, hx⟩ hxc
  let e := c.basicOpen r
  have he : e.U.1 ≤ U.1 := hr
  have hxe : x ∈ e.sourceOpen := hxr
  refine ⟨e, he, hxe, ?_, ?_⟩
  · simpa only [hU, Ideal.map_span, Set.image_singleton, res] using (I.map_ideal he).symm
  · letI : Nonempty U.1 := ⟨⟨I.gluedTo.base x, hx⟩⟩
    letI : Nonempty e.U.1 := ⟨⟨I.gluedTo.base x, hxe⟩⟩
    letI : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
    letI : IsDomain Γ(X, e.U.1) := IsIntegral.component_integral e.U.1
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro hzero
    apply (mem_nonZeroDivisors_iff_ne_zero.mp hs)
    apply map_injective_of_isIntegral X (homOfLE he)
    simpa only [map_zero] using hzero

end KltDP.Geometry.GluedBranchOriginalEquationChart

#print axioms KltDP.Geometry.GluedBranchOriginalEquationChart.exists_subordinate

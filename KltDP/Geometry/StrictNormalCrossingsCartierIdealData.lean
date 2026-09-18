import KltDP.Geometry.StrictNormalCrossingsCartierLocality
import KltDP.Geometry.EffectiveCartierIdeal
import KltDP.Geometry.RationalTreePicardStalkTransport
import KltDP.Geometry.DivisorOrder

/-!
# SNC from generators of the original Cartier ideal at its stalks

The ideal is the existing regular-equation Cartier ideal. Its stalk ideal
is computed by the original germ map from any affine neighborhood. The
accepted affine-chart independence transports a given SNC generator to
an actual regular Cartier equation, whose unit-association then gives SNC.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
namespace KltDP.Geometry
attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X]

/-- The actual Cartier ideal on any affine chart maps to the principal
ideal of any original regular Cartier equation through the same point. -/
theorem regularCartierIdealData_map_germ_eq_span (D : CartierDivisor X)
    (hD : HasRegularCartierEquations X D) (c : RegularCartierEquationChart X D)
    (U : X.affineOpens) (x : X) (hxU : x ∈ U.1) (hxc : x ∈ c.chart.openSet) :
    ((effectiveCartierIdealDataOfRegularEquations X D hD).ideal U).map
        (X.presheaf.germ U.1 x hxU).hom =
      Ideal.span ({X.presheaf.germ c.chart.openSet x hxc c.coefficient} :
        Set (X.presheaf.stalk x)) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVc⟩ :=
    (isBasis_affine_open X).exists_subset_of_mem_open hxc c.chart.openSet.2
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  let d := RegularCartierEquationChart.restrict X D c V hVc
  rw [RationalTreePicard.ideal_map_germ_eq
    (effectiveCartierIdealDataOfRegularEquations X D hD)
    (U := U) (W := ⟨V, hV⟩) x hxU hxV]
  have hideal : (effectiveCartierIdealDataOfRegularEquations X D hD).ideal ⟨V, hV⟩ =
      Ideal.span ({d.coefficient} : Set Γ(X, V)) :=
    effectiveCartierIdealDataOfRegularEquations_ideal_chart X D hD d hV
  rw [hideal, Ideal.map_span, Set.image_singleton]
  change Ideal.span ({X.presheaf.germ V x hxV
    (X.presheaf.map (homOfLE hVc).op c.coefficient)} : Set (X.presheaf.stalk x)) = _
  exact congrArg (fun z : X.presheaf.stalk x => Ideal.span ({z} : Set (X.presheaf.stalk x)))
    (X.presheaf.germ_res_apply (homOfLE hVc) x hxV c.coefficient)

/-- An actual equality of ideal data lets original stalk-ideal SNC
generators prove SNC of the original Cartier divisor. -/
theorem isStrictNormalCrossingsCartier_of_idealData_generators [IsLocallyNoetherian X]
    (D : CartierDivisor X) (hD : HasRegularCartierEquations X D)
    (I : X.IdealSheafData)
    (hI : effectiveCartierIdealDataOfRegularEquations X D hD = I)
    (hlocal : ∀ x : X, ∃ (U : X.affineOpens) (hx : x ∈ U.1)
      (t : X.presheaf.stalk x),
      (I.ideal U).map (X.presheaf.germ U.1 x hx).hom = Ideal.span ({t} : Set _) ∧
        IsStrictNormalCrossingsEquation (X.presheaf.stalk x) t) :
    IsStrictNormalCrossingsCartier X D := by
  refine ⟨hD, ?_⟩
  intro c x hxc
  letI : IsDomain (X.presheaf.stalk x) := integralSchemeStalk_isDomain X x
  obtain ⟨U, hxU, t, ht, hsnc⟩ := hlocal x
  have heq := regularCartierIdealData_map_germ_eq_span X D hD c U x hxU hxc
  rw [hI, ht] at heq
  exact hsnc.of_span_eq heq

end KltDP.Geometry

#print axioms KltDP.Geometry.isStrictNormalCrossingsCartier_of_idealData_generators

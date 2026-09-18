import KltDP.Geometry.CartierDivisorPullbackIdeal

/-!
# Cartier pullback on an original principal ideal chart

An actual regular generator of the canonical Cartier ideal gives a
regular chart of that same divisor: the existing ideal-to-equation
comparison proves its representative identity. The existing Cartier
pullback formula then applies to the original generator on every
subordinate affine open. No alternative Cartier divisor is substituted.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- An actual regular generator of the original canonical ideal represents that original divisor. -/
def regularChartOfIdealGenerator (D : CartierDivisor Y)
    (hD : HasRegularCartierEquations Y D) (U : Y.affineOpens) [Nonempty U.1]
    (d : Γ(Y, U.1))
    (hspan : (effectiveCartierIdealDataOfRegularEquations Y D hD).ideal U = Ideal.span {d})
    (hreg : d ∈ nonZeroDivisors Γ(Y, U.1)) : RegularCartierEquationChart Y D := by
  let I := effectiveCartierIdealDataOfRegularEquations Y D hD
  let c : PrincipalRegularChart Y I := ⟨U, inferInstance, d, hspan, hreg⟩
  exact
    { chart :=
        { openSet := U.1
          nonempty := inferInstance
          equation := c.equation
          represents := (restrict_eq_of_idealData Y I D hD rfl c).symm }
      coefficient := d
      germ_eq := rfl }

/-- The original ideal generator pulls back by the original scheme section map. -/
theorem pullbackIdealData_ideal_of_generator (π : X ⟶ Y) [GenericPointPreserving π]
    (D : CartierDivisor Y) (hD : HasRegularCartierEquations Y D)
    (U : Y.affineOpens) [Nonempty U.1] (d : Γ(Y, U.1))
    (hspan : (effectiveCartierIdealDataOfRegularEquations Y D hD).ideal U = Ideal.span {d})
    (hreg : d ∈ nonZeroDivisors Γ(Y, U.1))
    (W : X.affineOpens) (hW : W.1 ≤ π ⁻¹ᵁ U.1) :
    (pullbackIdealData π D hD).ideal W = Ideal.span {π.appLE U.1 W.1 hW d} := by
  by_cases hne : Nonempty W.1
  · letI : Nonempty W.1 := hne
    exact pullbackIdealData_ideal π D hD (regularChartOfIdealGenerator D hD U d hspan hreg) W hW
  · have hb : W.1 = ⊥ := by
      apply Opens.ext
      rw [Opens.coe_bot]
      exact Set.eq_empty_of_forall_not_mem fun x hx => hne ⟨⟨x, hx⟩⟩
    letI : Subsingleton Γ(X, W.1) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hb)
    apply Ideal.ext
    intro x
    rw [Subsingleton.elim x 0]
    simp

end KltDP.Geometry

#print axioms KltDP.Geometry.regularChartOfIdealGenerator
#print axioms KltDP.Geometry.pullbackIdealData_ideal_of_generator

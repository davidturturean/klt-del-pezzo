import KltDP.Geometry.EffectiveCartierDegree

/-!
# The zero divisor is effective with unit ideal and degree zero

On an integral scheme the zero Cartier divisor has the regular equation `1` on
the whole scheme; its divisor ideal `O ∩ O(-0)` is the unit ideal, so its
effective Cartier subscheme is empty and `effectiveCartierDegree` vanishes.
Ordinary proofs only; no literature input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (Y : Scheme.{u}) [IsIntegral Y]

/-- The global chart with equation `1` for the zero Cartier divisor. -/
def zeroCartierChart : RegularCartierEquationChart Y 0 where
  chart :=
    { openSet := ⊤
      nonempty := ⟨⟨genericPoint Y, Set.mem_univ _⟩⟩
      equation := 1
      represents := by
        letI : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, Set.mem_univ _⟩⟩
        show cartierEquationClassHom Y ⊤ (Additive.ofMul (1 : Y.functionFieldˣ)) =
          (cartierDivisorSheaf Y).val.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op
            (0 : CartierDivisor Y)
        rw [ofMul_one, map_zero, map_zero] }
  coefficient := 1
  germ_eq := by
    letI : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, Set.mem_univ _⟩⟩
    show Y.germToFunctionField ⊤ 1 = 1
    exact map_one _

/-- The zero divisor has regular equations everywhere. -/
theorem hasRegularCartierEquations_zero : HasRegularCartierEquations Y 0 :=
  fun _ => ⟨zeroCartierChart Y, Set.mem_univ _⟩

/-- The divisor ideal of the zero divisor is the unit ideal. -/
theorem effectiveCartierIdealDataOfRegularEquations_zero :
    effectiveCartierIdealDataOfRegularEquations Y 0 (hasRegularCartierEquations_zero Y) = ⊤ := by
  apply Scheme.IdealSheafData.ext
  funext U
  show (effectiveCartierIdealDataOfRegularEquations Y 0 (hasRegularCartierEquations_zero Y)).ideal U = ⊤
  by_cases hU : Nonempty (U.1 : Y.Opens)
  · letI := hU
    have h := effectiveCartierIdealDataOfRegularEquations_ideal_chart Y 0
      (hasRegularCartierEquations_zero Y)
      (RegularCartierEquationChart.restrict Y 0 (zeroCartierChart Y) U.1 le_top) U.2
    refine h.trans ?_
    show Ideal.span {Y.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op (1 : Γ(Y, ⊤))} = ⊤
    rw [map_one, Ideal.span_singleton_one]
  · have hbot : U.1 = ⊥ := by
      rw [← Opens.coe_eq_empty]
      exact Set.not_nonempty_iff_eq_empty.mp (fun ⟨x, hx⟩ => hU ⟨⟨x, hx⟩⟩)
    haveI : Subsingleton Γ(Y, U.1) :=
      CommRingCat.subsingleton_of_isTerminal (Y.sheaf.isTerminalOfEqEmpty hbot)
    exact Subsingleton.elim _ _

/-- The effective Cartier subscheme of the zero divisor is empty. -/
theorem effectiveCartierScheme_zero_isEmpty :
    IsEmpty (effectiveCartierScheme Y 0 (hasRegularCartierEquations_zero Y)) :=
  effectiveCartierScheme_isEmpty_of_eq_top Y 0 (hasRegularCartierEquations_zero Y)
    (effectiveCartierIdealDataOfRegularEquations_zero Y)

/-- `deg(0) = 0`. -/
theorem effectiveCartierDegree_zero {k : Type u} [Field k] (f : Y ⟶ Spec (CommRingCat.of k)) :
    effectiveCartierDegree Y 0 (hasRegularCartierEquations_zero Y) f = 0 := by
  haveI := effectiveCartierScheme_zero_isEmpty Y
  exact effectiveCartierDegree_eq_zero_of_isEmpty Y 0 (hasRegularCartierEquations_zero Y) f

end KltDP.Geometry

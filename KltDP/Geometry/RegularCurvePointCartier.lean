import KltDP.Geometry.RegularCurvePointEquation
import KltDP.Geometry.EffectiveCartierOfInvertibleIdeal

/-! The actual regular closed point of the original integral algebraic
curve is an effective Cartier divisor. Its local equation is proved at
the point and is one off the point. The existing Cartier gluing theorem
then retains the kernel of the original rational point section. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RegularCurvePointCartier

variable {k : Type u} [Field k] [IsAlgClosed k]
  {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
  (x : X) (hclosed : IsClosed ({x} : Set X))
  (hregular : RegularPoint X x) (hdim : topologicalKrullDim X = 1)

include f hregular hdim in
/-- Local regular equations on the entire original curve, including off the point. -/
theorem ideal_locallyPrincipalRegular :
    IdealLocallyPrincipalRegular (ClosedPointVanishingIdeal.ideal X x hclosed) := by
  intro y
  by_cases hy : y = x
  · subst y
    exact RegularCurvePointEquation.exists_regular_equation f x hclosed hregular hdim
  · obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVle⟩ :=
      (isBasis_affine_open X).exists_subset_of_mem_open
        (show y ∈ ({x} : Set X)ᶜ from hy) hclosed.isOpen_compl
    refine ⟨⟨V, hV⟩, hyV, 1, ?_, one_mem _⟩
    have hxV : x ∉ V := fun hx => (hVle hx) (Set.mem_singleton x)
    rw [ClosedPointVanishingIdeal.ideal_eq_top X x hclosed ⟨V, hV⟩ hxV,
      Ideal.span_singleton_one]

include hregular hdim in
/-- A Cartier divisor with the kernel of the actual rational point section.
No local equation, invertibility, or replacement ideal is supplied. -/
theorem exists_cartierDivisor :
    ∃ E : CartierDivisor X, ∃ hE : HasRegularCartierEquations X E,
      (closedPointSection f x hclosed).ker =
        effectiveCartierIdealDataOfRegularEquations X E hE := by
  let I := ClosedPointVanishingIdeal.ideal X x hclosed
  have hI : IdealLocallyPrincipalRegular I :=
    ideal_locallyPrincipalRegular f x hclosed hregular hdim
  refine ⟨cartierDivisorOfIdeal X I hI,
    cartierDivisorOfIdeal_hasRegularEquations X I hI, ?_⟩
  exact (ClosedPointVanishingIdeal.closedPointSection_ker X x hclosed f).trans
    (cartierDivisorOfIdeal_idealData X I hI).symm

#print axioms ideal_locallyPrincipalRegular
#print axioms exists_cartierDivisor

end KltDP.Geometry.RegularCurvePointCartier

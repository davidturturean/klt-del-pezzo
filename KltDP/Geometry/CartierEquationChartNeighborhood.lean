import KltDP.Geometry.CartierDivisorTrivialization

/-!
# Original Cartier equation charts inside a prescribed neighborhood

Restrict an actual quotient-sheaf equation to the intersection with the
prescribed open. This gives compatible original source and target charts
for an arbitrary morphism, without any regular-equations assumption.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.CartierEquationChartNeighborhood

/-- Every actual signed Cartier divisor has an equation chart inside any
prescribed neighborhood of the point. -/
theorem exists_contained (X : Scheme.{u}) [IsIntegral X] (D : CartierDivisor X)
    (x : X) (W : X.Opens) (hxW : x ∈ W) :
    ∃ c : CartierEquationChart X D, x ∈ c.openSet ∧ c.openSet ≤ W := by
  obtain ⟨U, i, hxU, f, hf⟩ := exists_local_cartier_equation X ⊤ D x trivial
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hi : i = homOfLE (show U ≤ ⊤ from le_top) := Subsingleton.elim _ _
  have he : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D := by
    simpa only [hi] using hf
  let T : X.Opens := U ⊓ W
  letI : Nonempty T := ⟨⟨x, hxU, hxW⟩⟩
  let c : CartierEquationChart X D := {
    openSet := T
    nonempty := inferInstance
    equation := f
    represents := cartierGlobalEquation_restrict X D
      (homOfLE (show T ≤ U from inf_le_left)) f he }
  exact ⟨c, ⟨hxU, hxW⟩, inf_le_right⟩

/-- The actual source chart can be chosen inside the preimage of an actual
target chart through the same given morphism. -/
theorem exists_compatible {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (q : Y ⟶ X) (DX : CartierDivisor X) (DY : CartierDivisor Y) (y : Y) :
    ∃ (cS : CartierEquationChart Y DY) (cT : CartierEquationChart X DX),
      y ∈ cS.openSet ∧ cS.openSet ≤ q ⁻¹ᵁ cT.openSet := by
  obtain ⟨cT, hyT, _⟩ := exists_contained X DX (q.base y) ⊤ trivial
  obtain ⟨cS, hyS, hST⟩ := exists_contained Y DY y (q ⁻¹ᵁ cT.openSet) hyT
  exact ⟨cS, cT, hyS, hST⟩

end KltDP.Geometry.CartierEquationChartNeighborhood

#check @KltDP.Geometry.CartierEquationChartNeighborhood.exists_compatible
#print axioms KltDP.Geometry.CartierEquationChartNeighborhood.exists_compatible

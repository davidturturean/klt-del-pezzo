import KltDP.Geometry.CartierDivisorModule

/-!
# Common equation neighborhoods for two Cartier divisors

The existing local quotient representative theorem supplies an equation
for each actual Cartier divisor. Intersecting those neighborhoods with
the requested open and using the proved equation restriction identity
gives simultaneous equations near every point.

This is an adapter of the existing sheaf-local representative theorem,
not a global surjectivity assertion for the quotient on sections. No
tensor-additivity or Picard correspondence is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

variable (X : Scheme.{u}) [IsIntegral X]

/-- Every point of an open has a smaller nonempty neighborhood carrying
actual equations for both Cartier divisors at once. -/
theorem exists_common_cartier_equations (D E : CartierDivisor X)
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (i : V ⟶ U) (hxV : x ∈ V) (f g : X.functionFieldˣ),
      letI : Nonempty V := ⟨⟨x, hxV⟩⟩
      cartierEquationClassHom X V (Additive.ofMul f) =
          (cartierDivisorSheaf X).val.map (homOfLE (show V ≤ ⊤ from le_top)).op D ∧
        cartierEquationClassHom X V (Additive.ofMul g) =
          (cartierDivisorSheaf X).val.map (homOfLE (show V ≤ ⊤ from le_top)).op E := by
  obtain ⟨V, iV, hxV, f, hf⟩ := exists_local_cartier_equation X ⊤ D x trivial
  obtain ⟨W, iW, hxW, g, hg⟩ := exists_local_cartier_equation X ⊤ E x trivial
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  letI : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hiV : iV = homOfLE (show V ≤ ⊤ from le_top) := Subsingleton.elim _ _
  have hiW : iW = homOfLE (show W ≤ ⊤ from le_top) := Subsingleton.elim _ _
  let T : X.Opens := U ⊓ (V ⊓ W)
  have hxT : x ∈ T := ⟨hx, hxV, hxW⟩
  letI : Nonempty T := ⟨⟨x, hxT⟩⟩
  refine ⟨T, homOfLE inf_le_left, hxT, f, g, ?_, ?_⟩
  · apply cartierGlobalEquation_restrict X D
      (homOfLE (show T ≤ V from inf_le_right.trans inf_le_left)) f
    simpa only [hiV] using hf
  · apply cartierGlobalEquation_restrict X E
      (homOfLE (show T ≤ W from inf_le_right.trans inf_le_right)) g
    simpa only [hiW] using hg

end KltDP.Geometry

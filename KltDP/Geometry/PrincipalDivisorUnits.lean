import KltDP.Geometry.PrincipalDivisor

/-!
# Global units have zero actual principal divisor

A unit of the original structure-sheaf section ring maps to a unit in every
actual curve stalk. The canonical section-to-function-field map factors
through that stalk, so the already proved local-unit order theorem makes
every prime-curve coefficient zero.

This is a kernel statement for the existing principal-divisor homomorphism.
It does not construct a Cartier-divisor sheaf or a comparison with Picard.

Source reuse: pinned Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b
(Apache-2.0), `AlgebraicGeometry.functionField_isScalarTower` in
`AlgebraicGeometry/FunctionField.lean`, `IsScalarTower.algebraMap_apply` in
`Algebra/Algebra/Tower.lean`, and `Units.map` and `Units.ext`. The local order
vanishing is the project's existing `PrimeCurve.order_map_local_unit`;
finite support and the principal-divisor homomorphism are reused unchanged.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k]

/-- The actual top open contains the integral surface's generic point. -/
instance top_open_nonempty (X : NormalProjectiveSurface k) : Nonempty (⊤ : X.toScheme.Opens) :=
  ⟨⟨genericPoint X.toScheme, trivial⟩⟩

namespace PrimeCurve

variable {X : NormalProjectiveSurface k}

/-- The rational function induced by an actual global structure-sheaf unit
has zero order along every actual prime curve. -/
@[simp]
theorem order_map_global_unit (C : X.PrimeCurve) (a : Γ(X.toScheme, ⊤)ˣ) :
    C.order (Units.map
      (algebraMap Γ(X.toScheme, ⊤) X.toScheme.functionField).toMonoidHom a) = 0 := by
  let x : (⊤ : X.toScheme.Opens) := ⟨C.genericPoint, trivial⟩
  letI : Algebra Γ(X.toScheme, ⊤) (X.stalk C.genericPoint) :=
    TopCat.Presheaf.algebra_section_stalk X.toScheme.presheaf x
  letI : IsScalarTower Γ(X.toScheme, ⊤) (X.stalk C.genericPoint)
      X.toScheme.functionField :=
    functionField_isScalarTower X.toScheme ⊤ x
  let aₓ : (X.stalk C.genericPoint)ˣ :=
    Units.map (algebraMap Γ(X.toScheme, ⊤) (X.stalk C.genericPoint)).toMonoidHom a
  have hfactor : Units.map
      (algebraMap Γ(X.toScheme, ⊤) X.toScheme.functionField).toMonoidHom a =
      Units.map (algebraMap (X.stalk C.genericPoint) X.toScheme.functionField).toMonoidHom aₓ := by
    apply Units.ext
    exact IsScalarTower.algebraMap_apply Γ(X.toScheme, ⊤)
      (X.stalk C.genericPoint) X.toScheme.functionField (a : Γ(X.toScheme, ⊤))
  rw [hfactor]
  exact C.order_map_local_unit aₓ

end PrimeCurve

variable (X : NormalProjectiveSurface k)

/-- Every actual global unit has zero principal Weil divisor on the
original surface. -/
@[simp]
theorem principalDivisor_map_global_unit (a : Γ(X.toScheme, ⊤)ˣ) :
    X.principalDivisor (Units.map
      (algebraMap Γ(X.toScheme, ⊤) X.toScheme.functionField).toMonoidHom a) = 0 := by
  apply Finsupp.ext
  intro C
  exact C.order_map_global_unit a

/-- The same vanishing expressed through the actual additive
principal-divisor homomorphism. -/
@[simp]
theorem principalDivisorHom_map_global_unit (a : Γ(X.toScheme, ⊤)ˣ) :
    X.principalDivisorHom (Additive.ofMul (Units.map
      (algebraMap Γ(X.toScheme, ⊤) X.toScheme.functionField).toMonoidHom a)) = 0 :=
  X.principalDivisor_map_global_unit a

/-- Multiplying a rational function by an actual global unit leaves its
principal divisor unchanged. -/
theorem principalDivisor_mul_map_global_unit
    (f : X.toScheme.functionFieldˣ) (a : Γ(X.toScheme, ⊤)ˣ) :
    X.principalDivisor (f * Units.map
      (algebraMap Γ(X.toScheme, ⊤) X.toScheme.functionField).toMonoidHom a) =
      X.principalDivisor f := by
  rw [X.principalDivisor_mul, X.principalDivisor_map_global_unit, add_zero]

end KltDP.Geometry.NormalProjectiveSurface

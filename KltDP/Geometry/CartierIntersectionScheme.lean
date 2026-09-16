import KltDP.Geometry.EffectiveCartierDegree

/-!
# The symmetric intersection scheme of two effective Cartier divisors

For two effective Cartier divisors `D₁`, `D₂` (regular local equations) on an integral scheme `X`,
the ideal sheaf of `Z(D₁) ∩ Z(D₂)` is the sum `I(D₁) ⊔ I(D₂)` of the two divisor ideals, and the
intersection scheme is its glued closed subscheme. Symmetry in `D₁`, `D₂` is the commutativity of
`⊔` (`cartierIntersectionIdealData_comm`), hence the degree `dim_k Γ(Z(D₁) ∩ Z(D₂), O)` is
symmetric (`cartierIntersectionDegree_symm`).

Not proved here: the identification of `Z(C) ∩ Z(D)` with the intersection scheme `C ∩ D` of the
prime curve `C` (when `C` is itself Cartier, on a regular surface); it would give
`intersectionDegree_symm` for distinct prime curves. See `F03_RESTRICTION_ADAPTERS.md` (task 14).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X]

section IdealDegree

variable {k : Type u} [Field k]

/-- The degree of the closed subscheme of an ideal sheaf datum: `dim_k H⁰(Z(I), O)` for the
composite structure morphism. -/
def idealSheafDataDegree (I : X.IdealSheafData) (f : X ⟶ Spec (CommRingCat.of k)) : ℕ :=
  cohomologyDimension (I.gluedTo ≫ f)
    (_root_.SheafOfModules.unit I.glueData.glued.ringCatSheaf) 0

/-- The effective Cartier degree is the degree of the divisor ideal's subscheme. -/
theorem effectiveCartierDegree_eq_idealSheafDataDegree (D : CartierDivisor X)
    (hD : HasRegularCartierEquations X D) (f : X ⟶ Spec (CommRingCat.of k)) :
    effectiveCartierDegree X D hD f =
      idealSheafDataDegree X (effectiveCartierIdealDataOfRegularEquations X D hD) f := rfl

end IdealDegree

variable (D₁ D₂ : CartierDivisor X) (hD₁ : HasRegularCartierEquations X D₁)
  (hD₂ : HasRegularCartierEquations X D₂)

/-- The ideal sheaf of `Z(D₁) ∩ Z(D₂)`: the sum of the two divisor ideals. -/
def cartierIntersectionIdealData : X.IdealSheafData :=
  effectiveCartierIdealDataOfRegularEquations X D₁ hD₁ ⊔
    effectiveCartierIdealDataOfRegularEquations X D₂ hD₂

/-- The intersection ideal is symmetric. -/
theorem cartierIntersectionIdealData_comm :
    cartierIntersectionIdealData X D₁ D₂ hD₁ hD₂ = cartierIntersectionIdealData X D₂ D₁ hD₂ hD₁ :=
  sup_comm _ _

/-- **The intersection scheme `Z(D₁) ∩ Z(D₂)`**: the glued closed subscheme of the sum ideal. -/
def cartierIntersectionScheme : Scheme.{u} :=
  (cartierIntersectionIdealData X D₁ D₂ hD₁ hD₂).glueData.glued

/-- The closed immersion `Z(D₁) ∩ Z(D₂) → X`. -/
def cartierIntersectionInclusion : cartierIntersectionScheme X D₁ D₂ hD₁ hD₂ ⟶ X :=
  (cartierIntersectionIdealData X D₁ D₂ hD₁ hD₂).gluedTo

instance cartierIntersectionInclusion_isClosedImmersion :
    IsClosedImmersion (cartierIntersectionInclusion X D₁ D₂ hD₁ hD₂) :=
  inferInstanceAs (IsClosedImmersion (cartierIntersectionIdealData X D₁ D₂ hD₁ hD₂).gluedTo)

/-- The image of `Z(D₁) ∩ Z(D₂)` is the support of the sum ideal. -/
theorem range_cartierIntersectionInclusion :
    Set.range (cartierIntersectionInclusion X D₁ D₂ hD₁ hD₂).base =
      (cartierIntersectionIdealData X D₁ D₂ hD₁ hD₂).support :=
  Scheme.IdealSheafData.range_gluedTo _

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))

/-- **The symmetric intersection degree** `dim_k Γ(Z(D₁) ∩ Z(D₂), O)`. -/
def cartierIntersectionDegree : ℕ :=
  idealSheafDataDegree X (cartierIntersectionIdealData X D₁ D₂ hD₁ hD₂) f

/-- **Symmetry** of the intersection degree of two effective Cartier divisors. -/
theorem cartierIntersectionDegree_symm :
    cartierIntersectionDegree X D₁ D₂ hD₁ hD₂ f = cartierIntersectionDegree X D₂ D₁ hD₂ hD₁ f :=
  congrArg (fun I : X.IdealSheafData => idealSheafDataDegree X I f)
    (cartierIntersectionIdealData_comm X D₁ D₂ hD₁ hD₂)

end KltDP.Geometry

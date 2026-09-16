import KltDP.Geometry.SchemeModulePullbackUnit
import KltDP.Geometry.SchemeModuleFunctorial

/-!
# Pullback of module sheaves along an isomorphism of schemes

Pullback along an actual isomorphism `g` of schemes is an equivalence of module
categories, with quasi-inverse the pullback along `inv g`: the unit and counit are
the accepted identity and composition comparisons together with the equations
`inv g ≫ g = 𝟙` and `g ≫ inv g = 𝟙`. Hence the pullback functor is full and
faithful, and a trivialization of a module sheaf is determined by its pullback
along `g` followed by the canonical unit comparison (`unitIso_ext_of_pullback_isIso`).

This is the tool used to compare trivializations on an open of a reduced curve
lying inside a component, where the restricted closed immersion of the component
is an isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

variable {Y Z : Scheme.{u}} (g : Y ⟶ Z) [IsIso g]

/-- Pullback along an isomorphism of schemes is an equivalence of module categories,
with quasi-inverse the pullback along the inverse. -/
def schemeModulePullbackEquivalenceOfIsIso : Z.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (schemeModulePullback g) (schemeModulePullback (inv g))
    ((schemeModulePullbackIdIso Z).symm ≪≫
      eqToIso (congrArg schemeModulePullback (IsIso.inv_hom_id g).symm) ≪≫
      (schemeModulePullbackCompIso (inv g) g).symm)
    (schemeModulePullbackCompIso g (inv g) ≪≫
      eqToIso (congrArg schemeModulePullback (IsIso.hom_inv_id g)) ≪≫
      schemeModulePullbackIdIso Y)

/-- Pullback along an isomorphism is faithful. -/
instance schemeModulePullback_faithful_of_isIso : (schemeModulePullback g).Faithful :=
  (schemeModulePullbackEquivalenceOfIsIso g).faithful_functor

/-- Pullback along an isomorphism is full. -/
instance schemeModulePullback_full_of_isIso : (schemeModulePullback g).Full :=
  (schemeModulePullbackEquivalenceOfIsIso g).full_functor

/-- Two unit trivializations of a module sheaf agreeing after pullback along an
isomorphism (and the canonical unit comparison) are equal. -/
theorem unitIso_ext_of_pullback_isIso {M : Z.Modules}
    (a b : M ≅ _root_.SheafOfModules.unit Z.ringCatSheaf)
    (h : (schemeModulePullback g).map a.hom ≫ (schemeModulePullbackUnitIso g).hom =
      (schemeModulePullback g).map b.hom ≫ (schemeModulePullbackUnitIso g).hom) :
    a = b := by
  apply Iso.ext
  apply (schemeModulePullback g).map_injective
  exact (cancel_mono (schemeModulePullbackUnitIso g).hom).mp h

end KltDP.Geometry

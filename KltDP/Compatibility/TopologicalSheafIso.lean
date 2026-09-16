import Mathlib.Topology.Sheaves.Functors
import Mathlib.CategoryTheory.Equivalence

/-!
# Sheaf pushforward along an isomorphism of spaces

The original sheaf pushforward is inverse-image precomposition on
presheaves. Its identity and composition comparisons therefore retain
the original section maps. The two inverse equations of a topological
isomorphism give an equivalence with the original pushforward functors.

The pinned equivalence constructor adjusts its unit to obtain the
triangle identity. No formula for that adjusted unit is asserted here.
-/

noncomputable section

open CategoryTheory

universe u v w

namespace KltDP.TopologicalSheafIso

variable (C : Type v) [Category.{w} C]
variable {X Y Z : TopCat.{u}}

/-- Pushforward along the identity retains every original sheaf section and map. -/
def pushforwardIdIso (X : TopCat.{u}) :
    TopCat.Sheaf.pushforward C (𝟙 X) ≅ 𝟭 (X.Sheaf C) := Iso.refl _

/-- Iterated pushforward is the original pushforward of the composite. -/
def pushforwardCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pushforward C f ⋙ TopCat.Sheaf.pushforward C g ≅
      TopCat.Sheaf.pushforward C (f ≫ g) := Iso.refl _

/-- The two original inverse-image pushforwards form an equivalence.
The actual inverse equations supply its two preliminary comparisons. -/
def pushforwardEquivalence (e : X ≅ Y) : X.Sheaf C ≌ Y.Sheaf C :=
  CategoryTheory.Equivalence.mk (TopCat.Sheaf.pushforward C e.hom)
    (TopCat.Sheaf.pushforward C e.inv)
    (pushforwardCompIso C e.hom e.inv ≪≫
      eqToIso (congrArg (fun f : X ⟶ X => TopCat.Sheaf.pushforward C f) e.hom_inv_id) ≪≫
      pushforwardIdIso C X).symm
    (pushforwardCompIso C e.inv e.hom ≪≫
      eqToIso (congrArg (fun f : Y ⟶ Y => TopCat.Sheaf.pushforward C f) e.inv_hom_id) ≪≫
      pushforwardIdIso C Y)

/-- The forward functor remains the literal original sheaf pushforward. -/
theorem pushforwardEquivalence_functor (e : X ≅ Y) :
    (pushforwardEquivalence C e).functor = TopCat.Sheaf.pushforward C e.hom := rfl

/-- The inverse functor remains pushforward along the original inverse map. -/
theorem pushforwardEquivalence_inverse (e : X ≅ Y) :
    (pushforwardEquivalence C e).inverse = TopCat.Sheaf.pushforward C e.inv := rfl

/-- Pushforward by an actual isomorphism is an equivalence, with no
additional assumption on the coefficient category or the sheaves. -/
instance pushforward_isEquivalence (f : X ⟶ Y) [IsIso f] :
    (TopCat.Sheaf.pushforward C f).IsEquivalence :=
  (pushforwardEquivalence C (asIso f)).isEquivalence_functor

end KltDP.TopologicalSheafIso

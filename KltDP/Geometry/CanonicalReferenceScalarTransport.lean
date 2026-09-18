import KltDP.Geometry.OpenCartierWeil
import KltDP.Geometry.DominantCartierPullbackFunctorial
import KltDP.Geometry.CartierOrderOpenRestriction

/-!
# The same original target scalar on an actual common open

A scalar of the original target reference is transported to the target's
function field and pulled back to the model. Restricting it to an actual
common open gives exactly its original pullback from the target reference,
by the original scheme-map triangle and generic-stalk composition law.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CanonicalReferenceScalar

local instance scalarOpenGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (f : A ⟶ B) [IsOpenImmersion f] : GenericPointPreserving f :=
  ⟨genericPoint_eq_of_isOpenImmersion f⟩

private theorem unitMap_congr {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (f g : A ⟶ B) [GenericPointPreserving f] [GenericPointPreserving g]
    (h : f = g) (q : B.functionFieldˣ) :
    Units.map (functionFieldMap f).hom.toMonoidHom q =
      Units.map (functionFieldMap g).hom.toMonoidHom q := by
  cases h
  rfl

local instance scalarIntegralOpen {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (U : X.toScheme.Opens) [Nonempty U.toScheme] :
    IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

/-- The original target scalar agrees on the two actual paths to the common open. -/
theorem map_transportUnit_of_triangle
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (U : X.toScheme.Opens) [Nonempty U.toScheme]
    {W Z : Scheme.{u}} [IsIntegral W] [IsIntegral Z]
    (a : W ⟶ X.toScheme) [GenericPointPreserving a]
    (l : Z ⟶ W) (j : Z ⟶ U.toScheme) [IsOpenImmersion l] [IsOpenImmersion j]
    (h : l ≫ a = j ≫ U.ι) (q : U.toScheme.functionFieldˣ) :
    letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
    Units.map (OpenImmersionRational.functionFieldIso l).hom.hom.toMonoidHom
        (Units.map (functionFieldMap a).hom.toMonoidHom (OpenCartierWeil.transportUnit U q)) =
      Units.map (OpenImmersionRational.functionFieldIso j).hom.hom.toMonoidHom q := by
  letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  change Units.map (functionFieldMap l).hom.toMonoidHom
      (Units.map (functionFieldMap a).hom.toMonoidHom (OpenCartierWeil.transportUnit U q)) =
    Units.map (functionFieldMap j).hom.toMonoidHom q
  calc
    _ = Units.map (functionFieldMap (l ≫ a)).hom.toMonoidHom
        (OpenCartierWeil.transportUnit U q) :=
      (DominantCartierPullback.functionFieldUnitMap_comp l a
        (OpenCartierWeil.transportUnit U q)).symm
    _ = Units.map (functionFieldMap (j ≫ U.ι)).hom.toMonoidHom
        (OpenCartierWeil.transportUnit U q) :=
      unitMap_congr (l ≫ a) (j ≫ U.ι) h (OpenCartierWeil.transportUnit U q)
    _ = Units.map (functionFieldMap j).hom.toMonoidHom
        (Units.map (functionFieldMap U.ι).hom.toMonoidHom (OpenCartierWeil.transportUnit U q)) :=
      DominantCartierPullback.functionFieldUnitMap_comp j U.ι
        (OpenCartierWeil.transportUnit U q)
    _ = _ := congrArg (Units.map (functionFieldMap j).hom.toMonoidHom)
      (OpenCartierWeil.transportUnit_hom U q)

end KltDP.Geometry.CanonicalReferenceScalar

#check @KltDP.Geometry.CanonicalReferenceScalar.map_transportUnit_of_triangle
#print axioms KltDP.Geometry.CanonicalReferenceScalar.map_transportUnit_of_triangle

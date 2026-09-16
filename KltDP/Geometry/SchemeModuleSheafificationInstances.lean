import KltDP.Geometry.SchemeModulePullbackTensor
import Mathlib.CategoryTheory.Sites.ConcreteSheafification

/-!
# Cached original additive sheafification on scheme open sites

These are the pinned concrete sheafification adjunction and its original
local-bijectivity theorem. The proof is the accepted
`FiniteLocallyFreeCoherent` provider on the ordinary open site.
It is factored before concrete conormal objects enter instance search.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.SchemeModuleSheafificationInstances

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The original plus-plus adjunction supplies additive sheafification. -/
theorem hasWeakSheafify (X : Scheme.{u}) :
    HasWeakSheafify (_root_.Opens.grothendieckTopology X) AddCommGrp.{u} :=
  (CategoryTheory.plusPlusAdjunction
    (_root_.Opens.grothendieckTopology X) AddCommGrp.{u}).isRightAdjoint

/-- The original additive sheafification inverts exactly the locally bijective maps. -/
theorem wEqualsLocallyBijective (X : Scheme.{u}) :
    (_root_.Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrp.{u} := by
  let J := _root_.Opens.grothendieckTopology X
  letI : HasWeakSheafify J AddCommGrp.{u} := hasWeakSheafify X
  letI : J.PreservesSheafification (forget AddCommGrp.{u}) :=
    GrothendieckTopology.instPreservesSheafification J (forget AddCommGrp.{u})
  letI (P : X.Opensᵒᵖ ⥤ AddCommGrp.{u}) :
      Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P) :=
    Presheaf.isLocallyInjective_toSheafify' J P
  letI (P : X.Opensᵒᵖ ⥤ AddCommGrp.{u}) :
      Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P) :=
    Presheaf.isLocallySurjective_toSheafify' J P
  exact GrothendieckTopology.WEqualsLocallyBijective.mk' J AddCommGrp.{u}

end KltDP.Geometry.SchemeModuleSheafificationInstances

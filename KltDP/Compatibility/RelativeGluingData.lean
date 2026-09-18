/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Bounded adaptation of Mathlib 80cbd0498ab39e21d24d6730b3f932cec672a702,
AlgebraicGeometry/RelativeGluing.lean:55-92. The datum consists only of
an actual scheme diagram, its original maps to the directed base cover,
and the cartesian transition squares. All transition open immersions
and the source diagram's local directedness are proved from those data.
-/
import KltDP.Compatibility.RelativeGluingDirectedness

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Cover

variable {S : Scheme.{u}} (𝒰 : OpenCover.{u} S)
  [SmallCategory 𝒰.J] [LocallyDirected 𝒰]

/-- An original scheme diagram with cartesian transition squares over
an actual directed open cover. No glued object or existence conclusion
is included among the data. -/
structure RelativeGluingData where
  functor : 𝒰.J ⥤ Scheme.{u}
  natTrans : functor ⟶ functorOfLocallyDirected 𝒰
  equifibered : NatTrans.Equifibered natTrans

variable {𝒰} (d : RelativeGluingData 𝒰)

namespace RelativeGluingData

/-- Each original transition is a base change of an open immersion. -/
instance map_isOpenImmersion {i j : 𝒰.J} (hij : i ⟶ j) :
    IsOpenImmersion (d.functor.map hij) := by
  apply MorphismProperty.of_isPullback (d.equifibered hij).flip
  exact trans_isOpenImmersion 𝒰 hij

/-- The original cartesian squares derive the source diagram's local directedness. -/
instance isLocallyDirected [Quiver.IsThin 𝒰.J] :
    (d.functor ⋙ Scheme.forget).IsLocallyDirected := by
  apply Scheme.isLocallyDirected_of_equifibered_of_injective d.natTrans d.equifibered
  intro i j hij
  exact (show IsOpenImmersion (d.functor.map hij) from inferInstance).base_open.injective

end RelativeGluingData
end AlgebraicGeometry.Scheme.Cover

import KltDP.Geometry.PresheafedSpaceMorphismDescent
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Actual locally ringed-space descent along a quotient map

The presheaf map is constructed using the original direct-image isomorphism.
Locality descends by choosing an original point above each target point: the
composite stalk map is the stalk map of the original morphism and is local.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopCat Topology

universe u

namespace KltDP.Geometry.LocallyRingedSpaceMorphismDescent

variable {X Y Z : LocallyRingedSpace.{u}}

/-- A presheafed-space factor of an actual locally ringed-space morphism
is local when every target point has an original point above it. -/
theorem isLocalHom_of_surjective_comp (b : X ⟶ Y)
    (hb : Function.Surjective b.base) (f : X ⟶ Z)
    (q : Y.toPresheafedSpace ⟶ Z.toPresheafedSpace)
    (hq : b.toShHom ≫ q = f.toShHom) :
    ∀ y : Y, IsLocalHom (q.stalkMap y).hom := by
  intro y
  obtain ⟨x, rfl⟩ := hb y
  have h := PresheafedSpace.stalkMap.congr_hom _ _ hq x
  have hcomp := (PresheafedSpace.stalkMap.comp b.toShHom q x).symm.trans h
  letI : IsLocalHom
      ((q.stalkMap (b.base x) ≫ b.toShHom.stalkMap x).hom) := by
    rw [hcomp]
    dsimp
    infer_instance
  exact isLocalHom_of_comp (q.stalkMap (b.base x)).hom (b.toShHom.stalkMap x).hom

/-- The original quotient topology and original direct-image sheaf
isomorphism construct a unique morphism from a fiber-constant original map. -/
theorem existsUnique_lift (b : X ⟶ Y) [IsIso b.c]
    (hb : IsQuotientMap b.base) (f : X ⟶ Z)
    (hconst : Function.FactorsThrough f.base b.base) :
    ∃! q : Y ⟶ Z, b ≫ q = f := by
  let g : Y.carrier ⟶ Z.carrier :=
    TopCat.ofHom (hb.lift f.base.hom hconst)
  have hg : b.base ≫ g = f.base := by
    apply TopCat.hom_ext
    exact hb.lift_comp f.base.hom hconst
  obtain ⟨q, ⟨-, hq⟩, -⟩ :=
    PresheafedSpaceMorphismDescent.existsUnique_lift_of_base
      b.toShHom f.toShHom g hg
  let q' : Y ⟶ Z :=
    ⟨q, isLocalHom_of_surjective_comp b hb.surjective f q hq⟩
  have hq' : b ≫ q' = f := LocallyRingedSpace.Hom.ext' hq
  refine ⟨q', hq', ?_⟩
  intro m hm
  apply LocallyRingedSpace.Hom.ext'
  apply PresheafedSpaceMorphismDescent.hom_ext_of_surjective_comp_eq
    b.toShHom hb.surjective
  exact congrArg LocallyRingedSpace.Hom.toShHom (hm.trans hq'.symm)

end KltDP.Geometry.LocallyRingedSpaceMorphismDescent

#print axioms KltDP.Geometry.LocallyRingedSpaceMorphismDescent.existsUnique_lift

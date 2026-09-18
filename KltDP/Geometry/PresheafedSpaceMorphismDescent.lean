import Mathlib.Geometry.RingedSpace.PresheafedSpace

/-!
# Descending an actual presheaf map through an isomorphism on direct images

For a fixed factorization of the original continuous map, the inverse of the
original structure-presheaf map constructs the descended presheaf map. The
factorization and uniqueness follow from cancellation of that same map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopCat

universe u v w

namespace KltDP.Geometry.PresheafedSpaceMorphismDescent

variable {C : Type u} [Category.{v} C]
  {X Y Z : PresheafedSpace.{u, v, w} C}

/-- With a fixed continuous base map, a morphism can be cancelled through
an actual isomorphism on direct-image presheaves. -/
theorem hom_ext_of_comp_eq (b : X ⟶ Y) [IsIso b.c]
    (f g : Y ⟶ Z) (hbase : f.base = g.base) (hcomp : b ≫ f = b ≫ g) :
    f = g := by
  cases f with
  | mk fbase fc =>
    cases g with
    | mk gbase gc =>
      change fbase = gbase at hbase
      subst gbase
      apply congrArg (PresheafedSpace.Hom.mk fbase)
      apply NatTrans.ext
      funext U
      apply (cancel_mono (((Presheaf.pushforward C fbase).map b.c).app U)).1
      have h := PresheafedSpace.congr_app hcomp U
      simp only [PresheafedSpace.comp_c_app, eqToHom_refl,
        CategoryTheory.Functor.map_id] at h
      exact h.trans (CategoryTheory.Category.comp_id _)

/-- Descend the original presheaf morphism along its actual direct-image
isomorphism, retaining the prescribed factorization of the point map. -/
theorem existsUnique_lift_of_base (b : X ⟶ Y) [IsIso b.c]
    (f : X ⟶ Z) (g : Y.carrier ⟶ Z.carrier)
    (hbase : b.base ≫ g = f.base) :
    ∃! q : Y ⟶ Z, q.base = g ∧ b ≫ q = f := by
  cases f with
  | mk fbase fc =>
    change b.base ≫ g = fbase at hbase
    subst fbase
    let q : Y ⟶ Z :=
      { base := g
        c := fc ≫ (Presheaf.pushforward C g).map (inv b.c) }
    have hfac : b ≫ q = PresheafedSpace.Hom.mk (b.base ≫ g) fc := by
      change PresheafedSpace.Hom.mk (b.base ≫ g)
        ((fc ≫ (Presheaf.pushforward C g).map (inv b.c)) ≫
          (Presheaf.pushforward C g).map b.c) =
        PresheafedSpace.Hom.mk (b.base ≫ g) fc
      apply congrArg (PresheafedSpace.Hom.mk (b.base ≫ g))
      rw [Category.assoc, ← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id,
        CategoryTheory.Functor.map_id]
      exact CategoryTheory.Category.comp_id fc
    refine ⟨q, ⟨rfl, hfac⟩, ?_⟩
    intro q' hq'
    exact hom_ext_of_comp_eq b q' q hq'.1 (hq'.2.trans hfac.symm)

/-- If the original map is surjective on points, no separate equality of
base maps is needed for cancellation. -/
theorem hom_ext_of_surjective_comp_eq (b : X ⟶ Y) [IsIso b.c]
    (hb : Function.Surjective b.base) (f g : Y ⟶ Z)
    (hcomp : b ≫ f = b ≫ g) : f = g := by
  apply hom_ext_of_comp_eq b f g _ hcomp
  apply TopCat.hom_ext
  ext y
  obtain ⟨x, rfl⟩ := hb y
  exact congrArg (fun q : X ⟶ Z => q.base x) hcomp

end KltDP.Geometry.PresheafedSpaceMorphismDescent

#print axioms KltDP.Geometry.PresheafedSpaceMorphismDescent.existsUnique_lift_of_base
#print axioms KltDP.Geometry.PresheafedSpaceMorphismDescent.hom_ext_of_surjective_comp_eq

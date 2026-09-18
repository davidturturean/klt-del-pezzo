import Mathlib.AlgebraicGeometry.Pullbacks

/-! Transport of the original fiber projection through an actual
isomorphism of its field-valued base point. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.FieldFiberIsoTransport

/-- Precomposing the point map with an actual isomorphism does not
change whether the original fiber projection is an isomorphism. -/
theorem isIso_snd_of_precomp_iso
    {X Y K K' : Scheme.{u}} (f : X ⟶ Y) (g : K ⟶ Y)
    (e : K' ⟶ K) [IsIso e] [IsIso (pullback.snd f (e ≫ g))] :
    IsIso (pullback.snd f g) := by
  let m := pullback.map f (e ≫ g) f g (𝟙 _) e (𝟙 _)
    (by simp only [Category.id_comp, Category.comp_id]) (Category.comp_id _)
  letI : IsIso m := by dsimp only [m]; infer_instance
  have hm : m ≫ pullback.snd f g = pullback.snd f (e ≫ g) ≫ e :=
    pullback.lift_snd _ _ _
  letI : IsIso (m ≫ pullback.snd f g) := by rw [hm]; infer_instance
  exact IsIso.of_isIso_comp_left m (pullback.snd f g)

#check KltDP.Geometry.FieldFiberIsoTransport.isIso_snd_of_precomp_iso
#print axioms KltDP.Geometry.FieldFiberIsoTransport.isIso_snd_of_precomp_iso

end KltDP.Geometry.FieldFiberIsoTransport

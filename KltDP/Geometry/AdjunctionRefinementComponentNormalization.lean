import Mathlib.CategoryTheory.EqToHom

/-!
# Normalize a square of original natural-isomorphism components

Only categorical component projections, equality transport and inverse
cancellation are simplified here, before any scheme or differential sheaf
is substituted into the equation.
-/
noncomputable section
open CategoryTheory
namespace KltDP.Geometry.AdjunctionRefinementComponentNormalization

private theorem cancel_square {C : Type*} [Category C] {S₀ T₀ S T : C}
    (eS : S₀ ≅ S) (eT : T₀ ≅ T) (a : S₀ ⟶ T₀) (b : S ⟶ T)
    (h : a ≫ eT.hom = eS.hom ≫ b) : eS.inv ≫ a ≫ eT.hom = b := by
  rw [h, Iso.inv_hom_id_assoc]

/-- The original square, conjugated by its original component isomorphisms. -/
theorem component_square {C D : Type*} [Category C] [Category D]
    {F G H : C ⥤ D} (e : F ≅ G) (p : G = H) (S T : C)
    {a : F.obj S ⟶ F.obj T} {b : H.obj S ⟶ H.obj T}
    (h : a ≫ (e.hom.app T ≫ (eqToHom p).app T) =
      (e.hom.app S ≫ (eqToHom p).app S) ≫ b) :
    (e.app S ≪≫ eqToIso (Functor.congr_obj p S)).inv ≫ a ≫
      (e.app T ≪≫ eqToIso (Functor.congr_obj p T)).hom = b := by
  apply cancel_square
  simpa only [Iso.trans_hom, Iso.app_hom, eqToHom_app, Category.assoc] using h

end KltDP.Geometry.AdjunctionRefinementComponentNormalization

namespace KltDP.Geometry.AdjunctionRefinementComponentNormalization

/-- Retain the original object equality in the source component of the square. -/
theorem object_source_square {C D : Type*} [Category C] [Category D]
    {F G H : C ⥤ D} (e : F ≅ G) (p : G = H) (S T : C)
    (pS : G.obj S = H.obj S)
    {a : F.obj S ⟶ F.obj T} {b : H.obj S ⟶ H.obj T}
    (h : a ≫ (e.hom.app T ≫ (eqToHom p).app T) =
      (e.hom.app S ≫ (eqToIso pS).hom) ≫ b) :
    (e.app S ≪≫ eqToIso pS).inv ≫ a ≫
      (e.app T ≪≫ eqToIso (Functor.congr_obj p T)).hom = b := by
  apply cancel_square
  simpa only [Iso.trans_hom, Iso.app_hom, eqToHom_app, Category.assoc] using h

end KltDP.Geometry.AdjunctionRefinementComponentNormalization

namespace KltDP.Geometry.AdjunctionRefinementComponentNormalization

/-- Keep both original object-equality proofs in the conjugated square. -/
theorem original_object_square {C D : Type*} [Category C] [Category D]
    {F G H : C ⥤ D} (e : F ≅ G) (p : G = H) (S T : C)
    (qS pS : G.obj S = H.obj S) (pT : G.obj T = H.obj T)
    {a : F.obj S ⟶ F.obj T} {b : H.obj S ⟶ H.obj T}
    (h : a ≫ (e.hom.app T ≫ (eqToHom p).app T) =
      (e.hom.app S ≫ (eqToIso qS).hom) ≫ b) :
    (e.app S ≪≫ eqToIso pS).inv ≫ a ≫
      (e.app T ≪≫ eqToIso pT).hom = b := by
  apply cancel_square
  simpa only [Iso.trans_hom, Iso.app_hom, eqToHom_app, Category.assoc] using h

end KltDP.Geometry.AdjunctionRefinementComponentNormalization

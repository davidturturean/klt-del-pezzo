import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# A closed immersion on an original affine preimage chart

Surjectivity of the original app gives surjectivity on the top sections of
the actual restriction. The pinned affine closed-immersion criterion then
applies to that restriction itself.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ClosedImmersionAffineRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- An original affine chart and affine preimage with surjective original
section map give a closed-immersion restriction. -/
theorem of_app_surjective {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.Opens)
    (hX : IsAffineOpen (g ⁻¹ᵁ U)) (hY : IsAffineOpen U)
    (hs : Function.Surjective (g.app U).hom) : IsClosedImmersion (g ∣_ U) := by
  letI : IsAffine (g ⁻¹ᵁ U).toScheme := hX
  letI : IsAffine U.toScheme := hY
  apply IsClosedImmersion.of_surjective_of_isAffine
  change Function.Surjective ((g ∣_ U).appTop).hom
  rw [morphismRestrict_appTop, CommRingCat.hom_comp,
    RingHom.surjective_respectsIso.cancel_right_isIso]
  change Function.Surjective (g.app (U.ι ''ᵁ (⊤ : U.toScheme.Opens))).hom
  have htop : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := U.ι_image_top
  exact Eq.mpr (congrArg
    (fun V : Y.Opens => Function.Surjective (g.app V).hom) htop) hs

end KltDP.Geometry.ClosedImmersionAffineRestriction

import KltDP.Geometry.RationalTreePicardSurjectiveReduction
import KltDP.Geometry.ModuleOpenRestriction

/-!
# Pushforward along a morphism, restricted to an open of the target: the scalar comparison

BRIEF15, step 1 (started). For a morphism `f : Z ⟶ X` and an open `U` of `X`, the restriction to `U`
of the pushforward `f_* M` and the pushforward along `f ∣_ U` of the restriction of `M` to `f ⁻¹ᵁ U`
have, over an open `V` of `U`, the sections `M(f ⁻¹ᵁ (U.ι ''ᵁ V))` and
`M((f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V))` over the same open (`image_morphismRestrict_preimage`), and the
two scalar maps from `Γ(U, V)` agree through the identification of these opens
(`baseChange_scalar`, from `morphismRestrict_app` and `Scheme.Opens.ι_appIso`). The assembly of the
sheaf-of-modules isomorphism (`PresheafOfModules.homMk` with these components) remains; see
`LEMMA22_PROGRESS.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

variable {Z X : Scheme.{u}} (f : Z ⟶ X) (U : X.Opens)

/-- The scalar maps of the two composite pushforwards agree through the identification of the
opens: as morphisms `Γ(U, V) ⟶ Γ(Z, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V))`. -/
theorem baseChange_scalar (V : U.toScheme.Opens) :
    (U.ι.appIso V).inv ≫ f.app (U.ι ''ᵁ V) ≫
        Z.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op =
      (f ∣_ U).app V ≫ ((f ⁻¹ᵁ U).ι.appIso ((f ∣_ U) ⁻¹ᵁ V)).inv := by
  rw [Scheme.Opens.ι_appIso, Scheme.Opens.ι_appIso, Iso.refl_inv, Iso.refl_inv]
  erw [Category.id_comp, Category.comp_id]
  exact (morphismRestrict_app f U V).symm

end KltDP.Geometry.RationalTreePicard

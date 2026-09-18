import KltDP.Geometry.PushforwardAffinizationCharts

/-!
# The original chart affinization triangle

The original open affinization intertwines the original restricted
morphism and the spectrum map of its original section-ring map. On an
affine base chart this recovers the original morphism after the original
map from the affine spectrum. No geometric hypothesis on `f` is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PushforwardAffinizationCharts

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Original open affinization commutes with the original restricted morphism. -/
@[reassoc] theorem toSpecΓ_SpecMap_app (U : Y.Opens) :
    (f ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (f.app U) = (f ∣_ U) ≫ U.toSpecΓ := by
  have ha : (f ∣_ U).appTop =
      U.topIso.hom ≫ f.app U ≫ (f ⁻¹ᵁ U).topIso.inv :=
    Γ_map_morphismRestrict f U
  calc
    (f ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (f.app U) =
        (f ⁻¹ᵁ U).toScheme.toSpecΓ ≫ Spec.map (f.app U ≫ (f ⁻¹ᵁ U).topIso.inv) := by
      simp only [Scheme.Opens.toSpecΓ, Spec.map_comp, Category.assoc]
    _ = (f ⁻¹ᵁ U).toScheme.toSpecΓ ≫ Spec.map (U.topIso.inv ≫ (f ∣_ U).appTop) := by
      rw [ha, Iso.inv_hom_id_assoc]
    _ = (f ∣_ U) ≫ U.toSpecΓ := by
      rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
      rfl

/-- The actual chart affinization and actual affine-base map recover the original morphism. -/
@[reassoc] theorem affinization_toBase_fromSpec (U : Y.AffineZariskiSite) :
    (affinization f).app U ≫ (PushforwardAffineDiagram.toBaseSpectra f).app U ≫
      U.2.fromSpec = (f ⁻¹ᵁ U.1).ι ≫ f := by
  change (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (f.app U.1) ≫ U.2.fromSpec = _
  rw [toSpecΓ_SpecMap_app_assoc, IsAffineOpen.toSpecΓ_fromSpec, morphismRestrict_ι]

end KltDP.Geometry.PushforwardAffinizationCharts

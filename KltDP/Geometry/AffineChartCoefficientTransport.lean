import KltDP.Geometry.PrincipalQuotientOpenChart
import KltDP.Geometry.KernelIdealIsoTransport
import KltDP.Geometry.AffineOpenModuleDenominators

/-!
# Original affine-chart coefficient maps on image section rings

A proved triangle between an actual affine chart, an original scheme
morphism, and the canonical affine chart of its base determines the
original section map. Canonical global-section naturality transports
that map to the literal coefficient ring homomorphism.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u

namespace KltDP.Geometry.PrincipalQuotientOpenChart

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

/-- Actual pullback of a base affine section is the transported original coefficient-ring image. -/
theorem appLE_coefficient (f : Y ⟶ X) (U : X.affineOpens)
    (j : Spec (.of R) ⟶ Y) [IsOpenImmersion j]
    (φ : Γ(X, U.1) →+* R)
    (htri : j ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec)
    (h : (imageAffineOpen j).1 ≤ f ⁻¹ᵁ U.1) (r : Γ(X, U.1)) :
    f.appLE U.1 (imageAffineOpen j).1 h r = sectionEquiv j (φ r) := by
  have hpre : (⊤ : (Spec Γ(X, U.1)).Opens) ≤ U.2.fromSpec ⁻¹ᵁ U.1 := by
    rw [U.2.fromSpec_preimage_self]
  have htop : (⊤ : (Spec (.of R)).Opens) ≤
      (Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ (⊤ : (Spec Γ(X, U.1)).Opens) := by
    rw [Opens.map_top]
  have hm : f.appLE U.1 (imageAffineOpen j).1 h ≫ (j.appIso ⊤).hom =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (.of R)).inv := by
    dsimp only [imageAffineOpen]
    rw [Scheme.Hom.appIso_hom', Scheme.appLE_comp_appLE, appLE_congr_hom htri]
    rw [← Scheme.appLE_comp_appLE (Spec.map (CommRingCat.ofHom φ)) U.2.fromSpec
      U.1 ⊤ ⊤ hpre htop]
    rw [AffineOpenModule.fromSpec_appLE]
    simp only [homOfLE_refl, op_id, Functor.map_id, Category.comp_id]
    change (Scheme.ΓSpecIso Γ(X, U.1)).inv ≫
      (Spec.map (CommRingCat.ofHom φ)).appTop =
        CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (.of R)).inv
    exact (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm
  apply (j.appIso ⊤).commRingCatIsoToRingEquiv.injective
  change (j.appIso ⊤).hom (f.appLE U.1 (imageAffineOpen j).1 h r) =
    (j.appIso ⊤).hom ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (.of R)).inv (φ r)))
  rw [Iso.inv_hom_id_apply]
  change (f.appLE U.1 (imageAffineOpen j).1 h ≫ (j.appIso ⊤).hom) r = _
  rw [hm]
  rfl

end KltDP.Geometry.PrincipalQuotientOpenChart

#print axioms KltDP.Geometry.PrincipalQuotientOpenChart.appLE_coefficient

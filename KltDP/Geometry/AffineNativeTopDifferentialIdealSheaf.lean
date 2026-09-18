import KltDP.Geometry.AffineNativeTopDifferentialSheaf
import KltDP.Geometry.AffineDifferentialExteriorTildeIso

/-!
# Sheafifying the original native ideal factor

This ordinary transport adapter lifts a proved factor of the actual native
map by the original affine tilde functor and the original pullback comparison.
The actual differential bases identify the native and intrinsic sheaves, and
the compiled whole-map square identifies the resulting intrinsic map. The
point-blowup consumer supplies the bases and native factor internally.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry.AffineNativeTopDifferentialIdealSheaf

open AffineKaehlerTildeDerivation AffineTopDifferentialFrame
open AffineNativeTopDifferential

universe u

variable (k : Type u) [CommRing k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
variable (φ : A →ₐ[k] B)
variable (β : Basis (Fin 2) A (KaehlerDifferential k A))
variable (γ : Basis (Fin 2) B (KaehlerDifferential k B)) (J : Ideal B)

/-- Include the original ideal, then apply the inverse of the actual native frame. -/
def idealToNative : ModuleCat.of B J ⟶ (differentialModule k B).exteriorPower 2 :=
  ModuleCat.ofHom (X := ModuleCat.of B J) (Y := (differentialModule k B).exteriorPower 2)
    ((determinantEquiv γ).symm.toLinearMap.comp J.subtype)

variable (e : (ModuleCat.extendScalars φ.toRingHom).obj
  ((differentialModule k A).exteriorPower 2) ≃ₗ[B] J)

/-- The original affine pullback followed by the tilde of the actual ideal equivalence. -/
def nativeSheafIso :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom φ.toRingHom))).obj
      ((differentialModule k A).exteriorPower 2).tilde ≅ (ModuleCat.of B J).tilde :=
  AffineModuleTilde.pullbackIso φ.toRingHom ((differentialModule k A).exteriorPower 2) ≪≫
    AffineModuleTilde.linearEquivIso
      (M := (ModuleCat.extendScalars φ.toRingHom).obj ((differentialModule k A).exteriorPower 2))
      (N := ModuleCat.of B J) e

variable (hfactor : (determinantEquiv γ).symm.toLinearMap.comp
  (J.subtype.comp e.toLinearMap) = (AffineNativeTopDifferential.map k φ 2).hom)

include hfactor in
/-- The original tilde functor preserves the proved whole native factor. -/
theorem nativeSheafIso_factor :
    (nativeSheafIso k φ J e).hom ≫ AffineModuleTilde.map (idealToNative k γ J) =
      nativeSheafMap k φ 2 := by
  have hm : e.toModuleIso.hom ≫ idealToNative k γ J = AffineNativeTopDifferential.map k φ 2 := by
    apply ModuleCat.hom_ext
    exact hfactor
  change ((AffineModuleTilde.pullbackIso φ.toRingHom
    ((differentialModule k A).exteriorPower 2)).hom ≫ AffineModuleTilde.map e.toModuleIso.hom) ≫
      AffineModuleTilde.map (idealToNative k γ J) =
    (AffineModuleTilde.pullbackIso φ.toRingHom
      ((differentialModule k A).exteriorPower 2)).hom ≫
        AffineModuleTilde.map (AffineNativeTopDifferential.map k φ 2)
  rw [Category.assoc, ← AffineModuleTilde.map_comp, hm]

/-- The actual intrinsic source is identified with the original ideal tilde. -/
def intrinsicSheafIso :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom φ.toRingHom))).obj
      (intrinsic k A 2) ≅ (ModuleCat.of B J).tilde :=
  (schemeModulePullback (Spec.map (CommRingCat.ofHom φ.toRingHom))).mapIso
    (AffineDifferentialExteriorTildeMap.isoOfBasis k A β).symm ≪≫ nativeSheafIso k φ J e

/-- The actual ideal map into the original intrinsic target differential sheaf. -/
def idealToIntrinsic : (ModuleCat.of B J).tilde ⟶ intrinsic k B 2 :=
  AffineModuleTilde.map (idealToNative k γ J) ≫
    (AffineDifferentialExteriorTildeMap.isoOfBasis k B γ).hom

include hfactor in
/-- The whole original intrinsic differential factors through this same ideal.
The whole-map square is proved from the actual coordinate basis, not assumed. -/
theorem intrinsicSheafIso_factor (x : Fin 2 → A)
    (hx : ∀ i, β i = KaehlerDifferential.D k A (x i)) :
    (intrinsicSheafIso k φ β J e).hom ≫ idealToIntrinsic k γ J = intrinsicMap k φ 2 := by
  let F := schemeModulePullback (Spec.map (CommRingCat.ofHom φ.toRingHom))
  change (F.map (AffineDifferentialExteriorTildeMap.isoOfBasis k A β).inv ≫
      (nativeSheafIso k φ J e).hom) ≫
    (AffineModuleTilde.map (idealToNative k γ J) ≫
      (AffineDifferentialExteriorTildeMap.isoOfBasis k B γ).hom) = _
  rw [Category.assoc, ← Category.assoc (nativeSheafIso k φ J e).hom,
    nativeSheafIso_factor k φ γ J e hfactor]
  change F.map (AffineDifferentialExteriorTildeMap.isoOfBasis k A β).inv ≫
    (nativeSheafMap k φ 2 ≫ AffineDifferentialExteriorTildeMap.map k B 2) = _
  rw [← native_intrinsic_square_of_coordinate_basis k φ 2 β x hx]
  change F.map (AffineDifferentialExteriorTildeMap.isoOfBasis k A β).inv ≫
    F.map (AffineDifferentialExteriorTildeMap.isoOfBasis k A β).hom ≫ intrinsicMap k φ 2 = _
  rw [← Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id, Category.id_comp]

end KltDP.Geometry.AffineNativeTopDifferentialIdealSheaf

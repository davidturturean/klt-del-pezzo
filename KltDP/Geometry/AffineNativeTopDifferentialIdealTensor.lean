import KltDP.Geometry.AffineNativeTopDifferentialIdealSheaf
import KltDP.Geometry.IdealTensorFrameNormalization
import KltDP.Geometry.SchemeModuleStructureUnit

/-!
# The actual intrinsic ideal tensor factor

The original ideal inclusion and the actual native target frame give the
intrinsic tensor inclusion. The existing frame normalization turns the proved
intrinsic ideal factor into an isomorphism with the ideal tensored with the
original intrinsic top-differential sheaf, retaining the entire original map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

namespace KltDP.Geometry.AffineNativeTopDifferentialIdealTensor

open AffineKaehlerTildeDerivation AffineTopDifferentialFrame
open AffineNativeTopDifferential AffineNativeTopDifferentialIdealSheaf

universe u

variable (k B : Type u) [CommRing k] [CommRing B] [Algebra k B]

local instance targetMonoidal : MonoidalCategory (Spec (CommRingCat.of B)).Modules :=
  Scheme.Modules.monoidalCategory _

variable (γ : Basis (Fin 2) B (KaehlerDifferential k B)) (J : Ideal B)

/-- The actual original ideal inclusion, in the original module category. -/
def inclusionMorphism : ModuleCat.of B J ⟶ ModuleCat.of B B :=
  ModuleCat.ofHom J.subtype

/-- The original affine structure module compared with the actual tensor unit. -/
def ringTildeUnitIso : (ModuleCat.of B B).tilde ≅ 𝟙_ (Spec (CommRingCat.of B)).Modules :=
  AffineModuleTilde.unitIso B ≪≫ SchemeModuleStructureUnit.iso (Spec (CommRingCat.of B))

/-- The original ideal inclusion, sheafified into the actual tensor unit. -/
def idealInclusionSheaf : (ModuleCat.of B J).tilde ⟶ 𝟙_ (Spec (CommRingCat.of B)).Modules :=
  AffineModuleTilde.map (inclusionMorphism B J) ≫ (ringTildeUnitIso B).hom

/-- The actual native target determinant frame on the original tilde sheaf. -/
def nativeFrameIso : ((differentialModule k B).exteriorPower 2).tilde ≅
    𝟙_ (Spec (CommRingCat.of B)).Modules :=
  AffineModuleTilde.linearEquivIso (M := (differentialModule k B).exteriorPower 2)
    (N := ModuleCat.of B B) (determinantEquiv γ) ≪≫ ringTildeUnitIso B

/-- The actual intrinsic target frame, through the original normalized exterior map. -/
def intrinsicFrame : intrinsic k B 2 ≅ 𝟙_ (Spec (CommRingCat.of B)).Modules :=
  (AffineDifferentialExteriorTildeMap.isoOfBasis k B γ).symm ≪≫ nativeFrameIso k B γ

private theorem idealToNative_frame :
    idealToNative k γ J ≫ (determinantEquiv γ).toModuleIso.hom = inclusionMorphism B J := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change determinantEquiv γ ((determinantEquiv γ).symm (z : B)) = (z : B)
  exact (determinantEquiv γ).apply_symm_apply _

/-- The target frame carries the actual ideal map to its original inclusion. -/
theorem idealToIntrinsic_frame :
    idealToIntrinsic k γ J ≫ (intrinsicFrame k B γ).hom = idealInclusionSheaf B J := by
  change (AffineModuleTilde.map (idealToNative k γ J) ≫
      (AffineDifferentialExteriorTildeMap.isoOfBasis k B γ).hom) ≫
    ((AffineDifferentialExteriorTildeMap.isoOfBasis k B γ).inv ≫
      (nativeFrameIso k B γ).hom) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  change AffineModuleTilde.map (idealToNative k γ J) ≫
    (AffineModuleTilde.map (determinantEquiv γ).toModuleIso.hom ≫ (ringTildeUnitIso B).hom) =
      AffineModuleTilde.map (inclusionMorphism B J) ≫ (ringTildeUnitIso B).hom
  rw [← Category.assoc, ← AffineModuleTilde.map_comp, idealToNative_frame]

/-- Retain the original ideal inclusion after undoing the actual target frame. -/
theorem idealToIntrinsic_eq :
    idealToIntrinsic k γ J = idealInclusionSheaf B J ≫ (intrinsicFrame k B γ).inv := by
  calc
    _ = (idealToIntrinsic k γ J ≫ (intrinsicFrame k B γ).hom) ≫
        (intrinsicFrame k B γ).inv := by
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = _ := by rw [idealToIntrinsic_frame]

/-- The tensor of the ORIGINAL ideal inclusion with the ORIGINAL intrinsic top sheaf. -/
def tensorInclusion : (ModuleCat.of B J).tilde ⊗ intrinsic k B 2 ⟶ intrinsic k B 2 :=
  (idealInclusionSheaf B J ▷ intrinsic k B 2) ≫ (λ_ (intrinsic k B 2)).hom

variable {A : Type u} [CommRing A] [Algebra k A] (φ : A →ₐ[k] B)
variable (β : Basis (Fin 2) A (KaehlerDifferential k A))
variable (e : (ModuleCat.extendScalars φ.toRingHom).obj
  ((differentialModule k A).exteriorPower 2) ≃ₗ[B] J)

/-- The proved ideal equivalence and actual frame give the original intrinsic tensor isomorphism. -/
def tensorIso :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom φ.toRingHom))).obj (intrinsic k A 2) ≅
      (ModuleCat.of B J).tilde ⊗ intrinsic k B 2 :=
  intrinsicSheafIso k φ β J e ≪≫
    (IdealTensorFrameNormalization.frameIso (ModuleCat.of B J).tilde (intrinsicFrame k B γ)).symm

/-- The whole actual tensor factor preserves the original intrinsic differential.
The native factor here is the proved input consumed by this ordinary transport adapter. -/
theorem tensorIso_factor
    (hfactor : (determinantEquiv γ).symm.toLinearMap.comp
      (J.subtype.comp e.toLinearMap) = (AffineNativeTopDifferential.map k φ 2).hom)
    (x : Fin 2 → A) (hx : ∀ i, β i = KaehlerDifferential.D k A (x i)) :
    (tensorIso k B γ J φ β e).hom ≫ tensorInclusion k B J = intrinsicMap k φ 2 := by
  change ((intrinsicSheafIso k φ β J e).hom ≫
      (IdealTensorFrameNormalization.frameIso
        (ModuleCat.of B J).tilde (intrinsicFrame k B γ)).inv) ≫
    ((idealInclusionSheaf B J ▷ intrinsic k B 2) ≫ (λ_ (intrinsic k B 2)).hom) = _
  rw [Category.assoc, IdealTensorFrameNormalization.frameIso_inv_inclusion,
    ← idealToIntrinsic_eq]
  exact intrinsicSheafIso_factor k φ β γ J e hfactor x hx

end KltDP.Geometry.AffineNativeTopDifferentialIdealTensor

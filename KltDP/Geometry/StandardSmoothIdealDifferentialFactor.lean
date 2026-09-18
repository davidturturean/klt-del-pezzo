import KltDP.Geometry.AffineNativeTopDifferentialIdealTensor
import KltDP.Geometry.StandardSmoothNativeTopDifferential

/-!
# Ideal differential factors with an arbitrary original source basis

Standard smoothness supplies the whole native-to-intrinsic differential
square independently of the basis used to construct the ideal factor.
Thus an adapted branch basis may contain an arbitrary second differential
form. Both conclusions retain the existing sheaf isomorphisms and the
original intrinsic differential map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

namespace KltDP.Geometry.AffineNativeTopDifferentialIdealTensor

open AffineKaehlerTildeDerivation AffineTopDifferentialFrame
open AffineNativeTopDifferential AffineNativeTopDifferentialIdealSheaf

universe u

variable (k B : Type u) [CommRing k] [CommRing B] [Algebra k B]
variable {A : Type u} [CommRing A] [Algebra k A]
variable [Algebra.IsStandardSmoothOfRelativeDimension 2 k A]
variable (φ : A →ₐ[k] B)
variable (β : Basis (Fin 2) A (KaehlerDifferential k A))
variable (γ : Basis (Fin 2) B (KaehlerDifferential k B)) (J : Ideal B)
variable (e : (ModuleCat.extendScalars φ.toRingHom).obj
  ((differentialModule k A).exteriorPower 2) ≃ₗ[B] J)
variable (hfactor : (determinantEquiv γ).symm.toLinearMap.comp
  (J.subtype.comp e.toLinearMap) = (AffineNativeTopDifferential.map k φ 2).hom)

include hfactor in
/-- The same intrinsic ideal factor works for every actual source basis. -/
theorem intrinsicSheafIso_factor_of_standardSmooth :
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
  rw [← native_intrinsic_square k 2 φ]
  change F.map (AffineDifferentialExteriorTildeMap.isoOfBasis k A β).inv ≫
    F.map (AffineDifferentialExteriorTildeMap.isoOfBasis k A β).hom ≫ intrinsicMap k φ 2 = _
  rw [← Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id, Category.id_comp]

local instance standardSmoothTargetMonoidal : MonoidalCategory (Spec (CommRingCat.of B)).Modules :=
  Scheme.Modules.monoidalCategory _

include hfactor in
/-- The original tensor factor preserves the original intrinsic map, without
requiring the supplied branch-adapted basis to consist of exact forms. -/
theorem tensorIso_factor_of_standardSmooth :
    (tensorIso k B γ J φ β e).hom ≫ tensorInclusion k B J = intrinsicMap k φ 2 := by
  change ((intrinsicSheafIso k φ β J e).hom ≫
      (IdealTensorFrameNormalization.frameIso
        (ModuleCat.of B J).tilde (intrinsicFrame k B γ)).inv) ≫
    ((idealInclusionSheaf B J ▷ intrinsic k B 2) ≫ (λ_ (intrinsic k B 2)).hom) = _
  rw [Category.assoc, IdealTensorFrameNormalization.frameIso_inv_inclusion,
    ← idealToIntrinsic_eq]
  exact intrinsicSheafIso_factor_of_standardSmooth k B φ β γ J e hfactor

end KltDP.Geometry.AffineNativeTopDifferentialIdealTensor

#print axioms KltDP.Geometry.AffineNativeTopDifferentialIdealTensor.intrinsicSheafIso_factor_of_standardSmooth
#print axioms KltDP.Geometry.AffineNativeTopDifferentialIdealTensor.tensorIso_factor_of_standardSmooth

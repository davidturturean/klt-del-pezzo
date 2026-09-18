/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.RelativeSymmetricProjBasis
import KltDP.Geometry.RelativeProjectiveBaseChange
import KltDP.Geometry.Surface

/-!
# Intrinsic symmetric Proj over an original affine open is a local product

The original structure morphism determines the coefficient map. An actual basis
of the module over the affine section ring then identifies its symmetric Proj
with the pullback of projective space along that original structure morphism.
The section ring is an arbitrary commutative ring, not an assumed field.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace KltDP.Geometry.RelativeSymmetricProj
open RelativeProjectiveChart

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (σ : X ⟶ Spec (CommRingCat.of k)) {U : X.Opens} (hU : IsAffineOpen U)

/-- Coefficients supplied by the original affine-open structure morphism. -/
def affineCoefficientHom : k →+* Γ(X, U) :=
  (Spec.preimage (hU.isoSpec.inv ≫ U.ι ≫ σ)).hom

variable {M : Type u} [AddCommGroup M] [Module Γ(X, U) M]
  {n : ℕ} (b : Basis (Fin (n + 1)) Γ(X, U) M)

/-- The original projective-space projection in the chosen actual basis. -/
def affineProductFirst : scheme Γ(X, U) M ⟶ projectiveSpace k n :=
  (basisIso b).hom ≫ coefficientMorphism n (affineCoefficientHom σ hU)

/-- The intrinsic symmetric Proj has its actual cartesian local-product square. -/
theorem isPullback_affineProduct :
    IsPullback (affineProductFirst σ hU b) (toBase Γ(X, U) M ≫ hU.isoSpec.inv)
      (projectiveSpaceToSpec k n) (U.ι ≫ σ) := by
  refine (isPullback_freeProjectivization n (affineCoefficientHom σ hU)).of_iso
    (basisIso b).symm (Iso.refl _) hU.isoSpec.symm (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [affineProductFirst, Category.assoc]
  · simp only [Iso.symm_hom, Category.assoc, basisIso_inv_toBase_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id]
    change Spec.map (Spec.preimage (hU.isoSpec.inv ≫ U.ι ≫ σ)) =
      hU.isoSpec.inv ≫ U.ι ≫ σ
    exact Spec.map_preimage _

/-- The two original projections commute over the original field structure. -/
@[reassoc] theorem affineProductFirst_toBase :
    affineProductFirst σ hU b ≫ projectiveSpaceToSpec k n =
      (toBase Γ(X, U) M ≫ hU.isoSpec.inv) ≫ (U.ι ≫ σ) :=
  (isPullback_affineProduct σ hU b).w

/-- The actual affine local product of the original symmetric Proj. -/
def affineProductIso : scheme Γ(X, U) M ≅
    pullback (projectiveSpaceToSpec k n) (U.ι ≫ σ) :=
  (isPullback_affineProduct σ hU b).isoPullback

@[reassoc (attr := simp)] theorem affineProductIso_hom_fst :
    (affineProductIso σ hU b).hom ≫ pullback.fst _ _ =
      affineProductFirst σ hU b :=
  (isPullback_affineProduct σ hU b).isoPullback_hom_fst

@[reassoc (attr := simp)] theorem affineProductIso_hom_snd :
    (affineProductIso σ hU b).hom ≫ pullback.snd _ _ =
      toBase Γ(X, U) M ≫ hU.isoSpec.inv :=
  (isPullback_affineProduct σ hU b).isoPullback_hom_snd

end KltDP.Geometry.RelativeSymmetricProj

#print axioms KltDP.Geometry.RelativeSymmetricProj.isPullback_affineProduct
#print axioms KltDP.Geometry.RelativeSymmetricProj.affineProductIso

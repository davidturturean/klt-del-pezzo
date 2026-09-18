/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.RelativeSymmetricProjBasis

/-!
# Actual free projective changes of frame and their cocycle

All bases belong to the same original module over the same original ring.
The transition passes through its intrinsic symmetric Proj, using the actual
basis comparisons. Thus identity and cocycle laws follow from scheme inverse
laws, without adding transition maps or compatibility as hypotheses.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.RelativeSymmetricProj

open KltDP.SymmetricAlgebra
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  {n : ℕ} (b c d : Basis (Fin (n + 1)) R M)

/-- The original change of polynomial coordinates through the symmetric algebra. -/
def coordinateChange :
    RelativeProjectiveChart.homogeneousRing R n ≃ₐ[R]
      RelativeProjectiveChart.homogeneousRing R n :=
  (equivMvPolynomial b).symm.trans (equivMvPolynomial c)

@[simp] theorem coordinateChange_X (i : Fin (n + 1)) :
    coordinateChange b c (MvPolynomial.X i) =
      equivMvPolynomial c (ι R M (b i)) := by
  simp [coordinateChange]

@[simp] theorem coordinateChange_C (r : R) :
    coordinateChange b c (MvPolynomial.C r) = MvPolynomial.C r :=
  (coordinateChange b c).commutes r

/-- The actual coordinate change preserves and reflects the polynomial grading. -/
theorem coordinateChange_mem_iff (m : ℕ)
    (p : RelativeProjectiveChart.homogeneousRing R n) :
    coordinateChange b c p ∈ RelativeProjectiveChart.grading R n m ↔
      p ∈ RelativeProjectiveChart.grading R n m :=
  basisChange_mem_homogeneous_iff b c m p

@[simp] theorem coordinateChange_self :
    coordinateChange b b = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro p
  simp [coordinateChange]

@[simp] theorem coordinateChange_trans :
    (coordinateChange b c).trans (coordinateChange c d) = coordinateChange b d := by
  apply AlgEquiv.ext
  intro p
  simp [coordinateChange]

/-- The genuine scheme transition between two free projective frames. -/
def transition : RelativeProjectiveChart.freeProjectivization R n ≅
    RelativeProjectiveChart.freeProjectivization R n :=
  (basisIso b).symm ≪≫ basisIso c

/-- Its diagram commutes with the original map to the coefficient base. -/
@[reassoc] theorem transition_toBase :
    (transition b c).hom ≫ RelativeProjectiveChart.freeProjectivizationToBase R n =
      RelativeProjectiveChart.freeProjectivizationToBase R n := by
  dsimp only [transition, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, basisIso_toBase, basisIso_inv_toBase]

@[simp] theorem transition_self : transition b b = Iso.refl _ := by
  apply Iso.ext
  simp [transition]

@[simp] theorem transition_symm : (transition b c).symm = transition c b := by
  apply Iso.ext
  rfl

/-- Original changes of frame satisfy the actual scheme cocycle law. -/
@[simp] theorem transition_trans :
    transition b c ≪≫ transition c d = transition b d := by
  apply Iso.ext
  simp [transition, Category.assoc]

@[reassoc (attr := simp)] theorem transition_comp_hom :
    (transition b c).hom ≫ (transition c d).hom = (transition b d).hom := by
  simp [transition, Category.assoc]

/-- The three changes around an original triple of frames compose to identity. -/
theorem transition_three_cycle :
    (transition b c).hom ≫ (transition c d).hom ≫ (transition d b).hom = 𝟙 _ := by
  simp [transition, Category.assoc]

/-- The original homogeneous basic opens transform by the inverse original
coordinate change, as required for the contravariant Proj construction. -/
@[simp] theorem transition_preimage_basicOpen
    (p : RelativeProjectiveChart.homogeneousRing R n) :
    (transition b c).hom ⁻¹ᵁ Proj.basicOpen (RelativeProjectiveChart.grading R n) p =
      Proj.basicOpen (RelativeProjectiveChart.grading R n)
        (coordinateChange c b p) := rfl

end KltDP.Geometry.RelativeSymmetricProj

#print axioms KltDP.Geometry.RelativeSymmetricProj.transition_toBase
#print axioms KltDP.Geometry.RelativeSymmetricProj.transition_trans
#print axioms KltDP.Geometry.RelativeSymmetricProj.transition_preimage_basicOpen

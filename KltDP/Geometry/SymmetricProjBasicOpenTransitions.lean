/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.FreeProjectiveBasisTransitions

/-!
# Actual basic-open transitions through the same intrinsic symmetric Proj

An original symmetric element determines one intrinsic open and a polynomial
basic open in each basis. Native restriction of the actual basis isomorphism
gives their isomorphism. The resulting chart transitions commute with the
original open inclusions and base maps, and satisfy identity and cocycle laws.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.RelativeSymmetricProj

open KltDP.SymmetricAlgebra
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  {n : ℕ} (b c d : Basis (Fin (n + 1)) R M) (s : KltDP.SymmetricAlgebra R M)

/-- The actual polynomial open representing the same intrinsic symmetric element. -/
abbrev basisOpen : (RelativeProjectiveChart.freeProjectivization R n).Opens :=
  Proj.basicOpen (RelativeProjectiveChart.grading R n) (equivMvPolynomial b s)

/-- Native restriction of the inverse actual basis comparison. -/
def basisOpenIso : (basisOpen b s).toScheme ≅ (Proj.basicOpen (grading R M) s).toScheme :=
  (basisIso b).inv.preimageIso (Proj.basicOpen (grading R M) s)

@[reassoc (attr := simp)] theorem basisOpenIso_hom_ι :
    (basisOpenIso b s).hom ≫ (Proj.basicOpen (grading R M) s).ι =
      (basisOpen b s).ι ≫ (basisIso b).inv :=
  Scheme.Hom.preimageIso_hom_ι _ _

@[reassoc (attr := simp)] theorem basisOpenIso_inv_ι :
    (basisOpenIso b s).inv ≫ (basisOpen b s).ι =
      (Proj.basicOpen (grading R M) s).ι ≫ (basisIso b).hom := by
  rw [← cancel_mono (basisIso b).inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact Scheme.Hom.preimageIso_inv_ι (basisIso b).inv (Proj.basicOpen (grading R M) s)

/-- The actual chart transition between the same original open in two bases. -/
def basisOpenTransition : (basisOpen b s).toScheme ≅ (basisOpen c s).toScheme :=
  basisOpenIso b s ≪≫ (basisOpenIso c s).symm

/-- The chart transition is the restriction of the original whole-Proj transition. -/
@[reassoc (attr := simp)] theorem basisOpenTransition_hom_ι :
    (basisOpenTransition b c s).hom ≫ (basisOpen c s).ι =
      (basisOpen b s).ι ≫ (transition b c).hom := by
  simp [basisOpenTransition, transition, Category.assoc]

/-- The original chart maps to the same base ring commute with the transition. -/
@[reassoc] theorem basisOpenTransition_toBase :
    (basisOpenTransition b c s).hom ≫ (basisOpen c s).ι ≫
        RelativeProjectiveChart.freeProjectivizationToBase R n =
      (basisOpen b s).ι ≫ RelativeProjectiveChart.freeProjectivizationToBase R n := by
  rw [← Category.assoc, basisOpenTransition_hom_ι, Category.assoc, transition_toBase]

@[simp] theorem basisOpenTransition_self : basisOpenTransition b b s = Iso.refl _ := by
  apply Iso.ext
  simp [basisOpenTransition]

@[simp] theorem basisOpenTransition_symm :
    (basisOpenTransition b c s).symm = basisOpenTransition c b s := by
  apply Iso.ext
  rfl

/-- The cocycle holds on the literal original basic-open schemes. -/
@[simp] theorem basisOpenTransition_trans :
    basisOpenTransition b c s ≪≫ basisOpenTransition c d s =
      basisOpenTransition b d s := by
  apply Iso.ext
  simp [basisOpenTransition, Category.assoc]

@[reassoc (attr := simp)] theorem basisOpenTransition_comp_hom :
    (basisOpenTransition b c s).hom ≫ (basisOpenTransition c d s).hom =
      (basisOpenTransition b d s).hom := by
  simp [basisOpenTransition, Category.assoc]

end KltDP.Geometry.RelativeSymmetricProj

#print axioms KltDP.Geometry.RelativeSymmetricProj.basisOpenTransition_hom_ι
#print axioms KltDP.Geometry.RelativeSymmetricProj.basisOpenTransition_toBase
#print axioms KltDP.Geometry.RelativeSymmetricProj.basisOpenTransition_trans

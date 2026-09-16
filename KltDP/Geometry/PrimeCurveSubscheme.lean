/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

The generic glued-inclusion block is adapted from Mathlib
5aedf732b6987e8c26ab3c9ebc855314f82b045f,
Mathlib/AlgebraicGeometry/IdealSheaf/Subscheme.lean, lines 332-443.
It uses the quotient-chart glue data already present at the project pin.
-/
import KltDP.Geometry.PrimeDivisor
import KltDP.Geometry.ProjectiveFiniteType
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Reduced closed subschemes representing actual prime curves

The pinned library constructs quotient-chart glue data for an ideal sheaf.
This module supplies its actual inclusion into the ambient scheme, using
the later official Mathlib proof. We keep the glued scheme itself as the
model, with its proved homeomorphism to the ideal's support.

For a prime curve, the ideal is its existing vanishing ideal. Radical chart
quotients prove reducedness. Irreducibility of the support proves
integrality. The closed immersion gives the inherited projective embedding.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The inclusion from the actual quotient-chart gluing into the scheme. -/
def gluedTo : I.glueData.glued ⟶ X :=
  Multicoequalizer.desc _ _ (fun U ↦ I.glueDataObjι U ≫ U.1.ι)
    (by simp [GlueData.diagram, pullback.condition_assoc])

@[reassoc]
theorem ι_gluedTo (U : X.affineOpens) :
    I.glueData.ι U ≫ I.gluedTo = I.glueDataObjι U ≫ U.1.ι :=
  Multicoequalizer.π_desc _ _ _ _ _

@[reassoc]
theorem glueDataObjMap_ι (U V : X.affineOpens) (h : U ≤ V) :
    I.glueDataObjMap h ≫ I.glueData.ι V = I.glueData.ι U := by
  have : IsIso (X.homOfLE inf_le_left : (U.1 ⊓ V.1).toScheme ⟶ U) :=
    ⟨X.homOfLE (by simpa), by simp, by simp⟩
  have H : inv (X.homOfLE inf_le_left : (U.1 ⊓ V.1).toScheme ⟶ U) =
      X.homOfLE (by simpa) := by
    rw [eq_comm, ← hom_comp_eq_id]
    simp
  have hglue := I.glueData.glue_condition U V
  simp only [glueData_J, glueData_V, glueData_t, glueData_U, glueData_f] at hglue
  rw [← IsIso.inv_comp_eq] at hglue
  rw [← Category.id_comp (I.glueData.ι U), ← hglue]
  simp_rw [← Category.assoc]
  congr 1
  rw [← cancel_mono (glueDataObjι _ _)]
  simp [pullback_inv_fst_snd_of_right_isIso_assoc, H]

theorem gluedTo_injective : Function.Injective I.gluedTo.base := by
  intro a b e
  obtain ⟨ia, a, rfl⟩ := I.glueData.ι_jointly_surjective a
  obtain ⟨ib, b, rfl⟩ := I.glueData.ι_jointly_surjective b
  have hab : ((I.glueDataObjι ia).base a).1 = ((I.glueDataObjι ib).base b).1 := by
    have hcomp : (I.glueData.ι ia ≫ I.gluedTo).base a =
        (I.glueData.ι ib ≫ I.gluedTo).base b := e
    rwa [ι_gluedTo, ι_gluedTo] at hcomp
  obtain ⟨f, g, hfg, H⟩ := exists_basicOpen_le_affine_inter ia.2 ib.2
    ((I.glueDataObjι ia).base a).1
      ⟨((I.glueDataObjι ia).base a).2, hab ▸ ((I.glueDataObjι ib).base b).2⟩
  have hmem (W) (hW : W = X.affineBasicOpen g) :
      b ∈ Set.range (I.glueDataObjMap (hW.trans_le (X.affineBasicOpen_le g))).base := by
    subst hW
    refine (I.opensRange_glueDataObjMap g).ge ?_
    change ((I.glueDataObjι ib).base b).1 ∈ X.basicOpen g
    rwa [← hab, ← hfg]
  obtain ⟨a, rfl⟩ := (I.opensRange_glueDataObjMap f).ge H
  obtain ⟨b, rfl⟩ := hmem (X.affineBasicOpen f) (Subtype.ext hfg)
  simp only [glueData_U, ← Scheme.comp_base_apply, glueDataObjMap_glueDataObjι] at hab ⊢
  simp only [Scheme.affineBasicOpen_coe, Scheme.comp_base, TopCat.coe_comp,
    Function.comp_apply, Scheme.homOfLE_apply, SetLike.coe_eq_coe] at hab
  obtain rfl := (I.glueDataObjι (X.affineBasicOpen f)).isEmbedding.injective hab
  simp only [glueDataObjMap_ι]

theorem range_glueDataObjι_ι_eq_support_inter (U : X.affineOpens) :
    Set.range (I.glueDataObjι U ≫ U.1.ι).base = (I.support : Set X) ∩ U :=
  (I.range_glueDataObjι_ι U).trans (I.coe_support_inter U).symm

theorem range_gluedTo : Set.range I.gluedTo.base = I.support := by
  refine Set.Subset.antisymm (Set.range_subset_iff.mpr fun x ↦ ?_) ?_
  · obtain ⟨U, x, rfl⟩ := I.glueData.ι_jointly_surjective x
    change (I.glueData.ι U ≫ I.gluedTo).base x ∈ I.support
    rw [ι_gluedTo]
    exact ((I.range_glueDataObjι_ι_eq_support_inter U).le ⟨_, rfl⟩).1
  · intro x hx
    let U : X.affineOpens :=
      ⟨(X.affineCover.map x).opensRange, isAffineOpen_opensRange (X.affineCover.map x)⟩
    have hxU : x ∈ U.1 := X.affineCover.covers x
    obtain ⟨y, hy⟩ := (I.range_glueDataObjι_ι_eq_support_inter U).ge ⟨hx, hxU⟩
    refine ⟨(I.glueData.ι U).base y, ?_⟩
    change (I.glueData.ι U ≫ I.gluedTo).base y = x
    rwa [ι_gluedTo]

theorem range_glueData_ι (U : X.affineOpens) :
    Set.range (I.glueData.ι U).base =
      (I.gluedTo ⁻¹ᵁ U : Set I.glueData.glued) := by
  simp only [TopologicalSpace.Opens.map_coe]
  apply I.gluedTo_injective.image_injective
  rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.comp_base, ι_gluedTo]
  calc
    _ = (I.support : Set X) ∩ (U.1 : Set X) :=
      I.range_glueDataObjι_ι_eq_support_inter U
    _ = (U.1 : Set X) ∩ Set.range I.gluedTo.base := by
      rw [I.range_gluedTo, Set.inter_comm]
    _ = _ := Set.image_preimage_eq_inter_range.symm

/-- The quotient chart is isomorphic to the inverse image of its ambient
affine open under the actual inclusion. -/
def glueDataObjIso (U : X.affineOpens) :
    I.glueDataObj U ≅ I.gluedTo ⁻¹ᵁ U :=
  IsOpenImmersion.isoOfRangeEq (I.glueData.ι U) (Scheme.Opens.ι _) (by
    simpa only [Scheme.Opens.range_ι] using I.range_glueData_ι U)

@[reassoc]
theorem glueDataObjIso_hom_ι (U : X.affineOpens) :
    (I.glueDataObjIso U).hom ≫ (I.gluedTo ⁻¹ᵁ U).ι = I.glueData.ι U :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

theorem glueDataObjIso_hom_restrict (U : X.affineOpens) :
    (I.glueDataObjIso U).hom ≫ I.gluedTo ∣_ ↑U = I.glueDataObjι U := by
  rw [← cancel_mono U.1.ι]
  simp [glueDataObjIso_hom_ι_assoc, ι_gluedTo]

instance gluedTo_isPreimmersion : IsPreimmersion I.gluedTo := by
  rw [IsLocalAtTarget.iff_of_iSup_eq_top (P := @IsPreimmersion)
    _ (iSup_affineOpens_eq_top X)]
  intro U
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsPreimmersion
    (I.glueDataObjIso U).hom, glueDataObjIso_hom_restrict]
  infer_instance

instance gluedTo_isClosedImmersion : IsClosedImmersion I.gluedTo :=
  .of_isPreimmersion _ (I.range_gluedTo ▸ I.support.isClosed)

/-- The actual glued scheme has exactly the topology of the ideal support. -/
def gluedSupportHomeomorph : I.glueData.glued ≃ₜ I.support :=
  I.gluedTo.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr I.range_gluedTo)

/-- Radical ideal sheaves give reduced glued schemes. Each stalk is
identified with a stalk of an actual reduced quotient chart. -/
theorem glued_isReduced (hI : I.radical = I) :
    AlgebraicGeometry.IsReduced I.glueData.glued := by
  haveI : ∀ x : I.glueData.glued,
      _root_.IsReduced (I.glueData.glued.presheaf.stalk x) := by
    intro x
    obtain ⟨U, x, rfl⟩ := I.glueData.ι_jointly_surjective x
    have hrad : (I.ideal U).radical = I.ideal U := by
      simpa only [radical_ideal] using congrArg (fun J : X.IdealSheafData ↦ J.ideal U) hI
    letI : _root_.IsReduced (Γ(X, (U : X.affineOpens).1) ⧸ I.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_eq_iff.mp hrad)
    letI : AlgebraicGeometry.IsReduced (I.glueData.U U) := by
      change AlgebraicGeometry.IsReduced
        (Spec (CommRingCat.of (Γ(X, (U : X.affineOpens).1) ⧸ I.ideal U)))
      infer_instance
    exact isReduced_of_injective ((I.glueData.ι U).stalkMap x).hom
      (asIso ((I.glueData.ι U).stalkMap x)).commRingCatIsoToRingEquiv.injective
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk _

end AlgebraicGeometry.Scheme.IdealSheafData

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k}

/-- The scheme obtained by gluing the quotients by the curve's actual
vanishing ideal. -/
def toScheme (C : X.PrimeCurve) : Scheme.{u} := C.vanishingIdeal.glueData.glued

/-- The actual closed immersion of the curve scheme into the surface. -/
def inclusion (C : X.PrimeCurve) : C.toScheme ⟶ X.toScheme := C.vanishingIdeal.gluedTo

instance (C : X.PrimeCurve) : IsClosedImmersion C.inclusion :=
  C.vanishingIdeal.gluedTo_isClosedImmersion

@[simp]
theorem range_inclusion (C : X.PrimeCurve) :
    Set.range C.inclusion.base = (C : Set X.toScheme) :=
  C.vanishingIdeal.range_gluedTo

/-- Identification with the original curve's subspace topology. -/
def underlyingHomeomorph (C : X.PrimeCurve) : C.toScheme ≃ₜ (C : Set X.toScheme) :=
  C.vanishingIdeal.gluedSupportHomeomorph

instance (C : X.PrimeCurve) : AlgebraicGeometry.IsReduced C.toScheme :=
  C.vanishingIdeal.glued_isReduced C.vanishingIdeal_radical

instance (C : X.PrimeCurve) : IrreducibleSpace C.toScheme := by
  letI : IrreducibleSpace (C : Set X.toScheme) := Subtype.irreducibleSpace C.isIrreducible
  apply (irreducibleSpace_def C.toScheme).mpr
  have h := (IrreducibleSpace.isIrreducible_univ (C : Set X.toScheme)).image
    C.underlyingHomeomorph.symm C.underlyingHomeomorph.symm.continuous.continuousOn
  simpa only [Set.image_univ, C.underlyingHomeomorph.symm.surjective.range_eq] using h

/-- The scheme representing the prime curve is integral. This follows from
proved reducedness and the original curve's irreducibility. -/
instance (C : X.PrimeCurve) : IsIntegral C.toScheme :=
  isIntegral_of_irreducibleSpace_of_isReduced C.toScheme

/-- The structure morphism is the composition with the surface's map. -/
def toSpec (C : X.PrimeCurve) : C.toScheme ⟶ Spec (CommRingCat.of k) :=
  C.inclusion ≫ X.structureMorphism

/-- The inherited projective embedding is an actual composition of closed
immersions. -/
theorem projective (C : X.PrimeCurve) : IsProjectiveOverField C.toSpec := by
  obtain ⟨n, i, hi, hcomp⟩ := X.projective
  letI : IsClosedImmersion i := hi
  refine ⟨n, C.inclusion ≫ i, inferInstance, ?_⟩
  change (C.inclusion ≫ i) ≫ projectiveSpaceToSpec k n =
    C.inclusion ≫ X.structureMorphism
  rw [Category.assoc, hcomp]

instance (C : X.PrimeCurve) : LocallyOfFiniteType C.toSpec := C.projective.locallyOfFiniteType

instance (C : X.PrimeCurve) : QuasiCompact C.toSpec := C.projective.quasiCompact

instance (C : X.PrimeCurve) : NoetherianSpace C.toScheme := C.projective.noetherianSpace

instance (C : X.PrimeCurve) (x : C.toScheme) :
    IsNoetherianRing (C.toScheme.presheaf.stalk x) :=
  C.projective.isNoetherianRing_stalk x

theorem dimension_one_toScheme (C : X.PrimeCurve) :
    topologicalKrullDim C.toScheme = 1 := by
  rw [IsHomeomorph.topologicalKrullDim_eq C.underlyingHomeomorph
    C.underlyingHomeomorph.isHomeomorph]
  exact C.dimension_one

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

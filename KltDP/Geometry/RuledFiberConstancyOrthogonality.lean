import KltDP.Geometry.RuledFiberOriginalPullback
import KltDP.Geometry.PrimeCurvePointFiberFactorization

/-!
# Actual curve-map constancy makes the pulled ruled fibre orthogonal

The full Picard decomposition and degree on the original fibre show that
its original line class comes from the base curve. Constancy of an original
prime under the original composite map supplies a scheme factorization
through a field point. The existing pullback restriction theorem then
gives degree zero, including when the prime lies in that very fibre.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.RuledFiberOriginalPullback

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S V : NormalProjectiveSurface k}
  (hV : ∀ v : V.Point, RegularPoint V.toScheme v)
  (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k))
  [IsIntegral C] [LocallyOfFiniteType c] [QuasiCompact c] [IsSeparated c]
  (hCdim : topologicalKrullDim C = 1) (hCreg : ∀ y : C, RegularPoint C y)
  (q : V.toScheme ⟶ C) (hbase : q ≫ c = V.structureMorphism)
  (hsurj : Function.Surjective q.base)
  (hfib : ∀ y : C, IsClosed ({y} : Set C) →
    ∃ e : q.fiber y ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 = q.fiberι y ≫ V.structureMorphism)
  (σ : C ⟶ V.toScheme) (hσ : σ ≫ q = 𝟙 C)

include hCdim hCreg hbase hsurj hfib hσ in
/-- The actual fibre line is in the image of the original base Picard
pullback. Its section coefficient is zero by degree on the same fibre. -/
theorem fiberPicard_from_base
    (y : C) (hy : IsClosed ({y} : Set C)) (F : V.PrimeCurve)
    (eF : F.toScheme ≅ q.fiber y) (heF : eF.hom ≫ q.fiberι y = F.inclusion) :
    ∃ l : C.Pic, cartierPicardClass V.toScheme (V.primeCurveCartier hV F) =
      schemePicardPullbackHom q l := by
  obtain ⟨A, eA, heA, _heAbase, _hA⟩ :=
    RuledSurfaceSourceGeometry.exists_sectionPrimeCurve V c q hbase hCdim σ hσ
  obtain ⟨ePic, _eNum, hePic, _heNum, hAF, hFF⟩ :=
    Literature.Hartshorne.ruled_surface_picard_literal
      k V hV C c hCdim hCreg q hbase hsurj hfib σ hσ A eA heA y hy F eF heF
  let PA := cartierPicardHom V.toScheme (V.primeCurveCartier hV A)
  let PF := cartierPicardHom V.toScheme (V.primeCurveCartier hV F)
  obtain ⟨⟨n, l⟩, hp⟩ := ePic.surjective PF
  rw [hePic] at hp
  have hfac : F.inclusion ≫ q =
      (eF.hom ≫ q.fiberToSpecResidueField y) ≫ C.fromSpecResidueField y := by
    have hfq : q.fiberι y ≫ q =
        q.fiberToSpecResidueField y ≫ C.fromSpecResidueField y :=
      Limits.pullback.condition
    rw [← heF, Category.assoc, hfq, ← Category.assoc]
  have hdegA : V.picardRestrictionDegreeHom F PA = 1 := by
    change V.picardRestrictionDegreeHom F
      (cartierPicardHom V.toScheme (V.primeCurveCartier hV A)) = 1
    rw [F.picardRestrictionDegreeHom_cartierPicardHom,
      ← V.intersectionPairing_primeCurve hV]
    exact hAF
  have hdegF : V.picardRestrictionDegreeHom F PF = 0 := by
    change V.picardRestrictionDegreeHom F
      (cartierPicardHom V.toScheme (V.primeCurveCartier hV F)) = 0
    rw [F.picardRestrictionDegreeHom_cartierPicardHom,
      ← V.intersectionPairing_primeCurve hV]
    exact hFF
  have hdegPull : V.picardRestrictionDegreeHom F
      ((schemePicardPullbackHom q).toAdditive l) = 0 :=
    PrimeCurveInclusionLift.picardRestrictionDegreeHom_pullback_eq_zero
      F F.inclusion F.range_inclusion.symm q
      (eF.hom ≫ q.fiberToSpecResidueField y) (C.fromSpecResidueField y) hfac l
  have hn : n = 0 := by
    have hh := congrArg (V.picardRestrictionDegreeHom F) hp
    change V.picardRestrictionDegreeHom F
      (n • PA + (schemePicardPullbackHom q).toAdditive l) =
        V.picardRestrictionDegreeHom F PF at hh
    simpa only [map_add, map_zsmul, hdegA, hdegPull, hdegF, smul_eq_mul,
      mul_one, add_zero] using hh
  have hp' : (schemePicardPullbackHom q).toAdditive l = PF := by
    simpa only [hn, zero_smul, zero_add] using hp
  exact ⟨l.toMul, (congrArg Additive.toMul hp').symm⟩

include hCdim hCreg hbase hsurj hfib hσ in
/-- Constancy under the original composite, rather than a supplied
intersection value, makes an original prime orthogonal to the pulled fibre. -/
theorem pullbackCurveClass_degree_zero_of_constant
    (b : S.toScheme ⟶ V.toScheme) (hb : IsPointBlowupSequence S V b)
    (y : C) (hy : IsClosed ({y} : Set C)) (F : V.PrimeCurve)
    (eF : F.toScheme ≅ q.fiber y) (heF : eF.hom ≫ q.fiberι y = F.inclusion)
    (E : S.PrimeCurve) (z : C)
    (hconstant : ∀ x ∈ (E : Set S.toScheme), (b ≫ q).base x = z) :
    S.numericalRestrictionDegree E (pullbackCurveClass b hV F) = 0 := by
  obtain ⟨l, hl⟩ := fiberPicard_from_base
    hV C c hCdim hCreg q hbase hsurj hfib σ hσ y hy F eF heF
  have hover : (b ≫ q) ≫ c = S.structureMorphism := by
    rw [Category.assoc, hbase, hb.over_base]
  obtain ⟨p, hfac, _hpbase, _hpz⟩ :=
    PrimeCurvePointFiberFactorization.exists_factor_of_constant
      S E c (b ≫ q) hover z hconstant
  have hzero : E.picardRestrictionDegree (schemePicardPullbackHom (b ≫ q) l) = 0 :=
    PrimeCurveInclusionLift.picardRestrictionDegree_pullback_eq_zero
      E E.inclusion E.range_inclusion.symm (b ≫ q) E.toSpec p hfac l
  have hcomp : schemePicardPullbackHom b (schemePicardPullbackHom q l) =
      schemePicardPullbackHom (b ≫ q) l :=
    (congrArg (fun f : C.Pic →* S.toScheme.Pic => f l)
      (schemePicardPullbackHom_comp q b)).symm
  change S.numericalRestrictionDegree E
    (S.picardNumericalMap (Additive.ofMul
      (schemePicardPullbackHom b
        (cartierPicardClass V.toScheme (V.primeCurveCartier hV F))))) = 0
  rw [S.numericalRestrictionDegree_picardNumericalMap]
  change (E.picardRestrictionDegree
    (schemePicardPullbackHom b
      (cartierPicardClass V.toScheme (V.primeCurveCartier hV F))) : ℚ) = 0
  rw [hl, hcomp, hzero, Int.cast_zero]

include hV hCdim hCreg hbase hsurj hfib hσ in
/-- The full original ruling produces one nonzero isotropic class on the
original surface, annihilating every original prime on which the actual
composite ruling is constant. -/
theorem exists_original_isotropic_class_with_constant_degrees
    (b : S.toScheme ⟶ V.toScheme) (hb : IsPointBlowupSequence S V b)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s) :
    ∃ u : S.NumericalClassGroup,
      u ≠ 0 ∧ S.numericalIntersectionBilinForm hS u u = 0 ∧
      ∀ E : S.PrimeCurve,
        (∃ z : C, ∀ x ∈ (E : Set S.toScheme), (b ≫ q).base x = z) →
        S.numericalRestrictionDegree E u = 0 := by
  obtain ⟨y, hy, A, F, _eA, eF, _heA, heF, _hAF, _hFF, _hAFpull, hne, hsq⟩ :=
    exists_original_isotropic_fiber b hb hS hV C c hCdim hCreg q hbase hsurj hfib σ hσ
  refine ⟨pullbackCurveClass b hV F, hne, hsq, ?_⟩
  intro E hE
  obtain ⟨z, hz⟩ := hE
  exact pullbackCurveClass_degree_zero_of_constant
    hV C c hCdim hCreg q hbase hsurj hfib σ hσ b hb y hy F eF heF E z hz

end KltDP.Geometry.RuledFiberOriginalPullback

#check @KltDP.Geometry.RuledFiberOriginalPullback.exists_original_isotropic_class_with_constant_degrees
#print axioms KltDP.Geometry.RuledFiberOriginalPullback.fiberPicard_from_base
#print axioms KltDP.Geometry.RuledFiberOriginalPullback.pullbackCurveClass_degree_zero_of_constant
#print axioms KltDP.Geometry.RuledFiberOriginalPullback.exists_original_isotropic_class_with_constant_degrees

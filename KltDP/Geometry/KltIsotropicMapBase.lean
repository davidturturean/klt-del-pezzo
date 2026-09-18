import KltDP.Geometry.KltExceptionalOrthogonalPositive
import KltDP.Geometry.KltResolutionExceptionalProjectiveLine
import KltDP.Geometry.PrimeCurvePointFiberFactorization
import KltDP.Geometry.ProjectiveLineCurveMapDichotomy
import KltDP.Geometry.ProjectiveLineSurjectionRatFunc
import KltDP.Geometry.ProperCurveRatFuncIsomorphism

/-! An actual curve base of the original rank-one klt del Pezzo resolution
is P1 whenever one original pulled-back line class is nonzero and isotropic.
No ruling, section, fiber isomorphisms or rationality hypothesis is used.
This applies in particular to the actual Stein base of a square-zero pencil. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.KltIsotropicMapBase

open NormalProjectiveSurface ActualExceptionalNumerical

/-- The actual nonzero isotropic pullback forces an original exceptional
P1 to dominate the same base; native Luroth then gives the original base iso. -/
theorem exists_projectiveLine_iso
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (hmin : IsMinimalResolution S X π)
    (hDP : IsKltDelPezzo X) (hrank : X.picardRank = 1)
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (C : Scheme.{u}) [IsIntegral C]
    (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c]
    (hCdim : topologicalKrullDim C = 1)
    (hCreg : ∀ z : C, RegularPoint C z)
    (q : S.toScheme ⟶ C) (hbase : q ≫ c = S.structureMorphism)
    (l : C.Pic)
    (hne : S.picardNumericalMap (Additive.ofMul (schemePicardPullbackHom q l)) ≠ 0)
    (hsq : S.numericalIntersectionBilinForm hmin.regular
      (S.picardNumericalMap (Additive.ofMul (schemePicardPullbackHom q l)))
      (S.picardNumericalMap (Additive.ofMul (schemePicardPullbackHom q l))) = 0) :
    ∃ e : C ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 = c := by
  let u := S.picardNumericalMap (Additive.ofMul (schemePicardPullbackHom q l))
  have hnonconstant : ∃ E : S.PrimeCurve, IsExceptionalCurve π E ∧
      ¬ (∃ z : C, ∀ x ∈ (E : Set S.toScheme), q.base x = z) := by
    by_contra hnone
    push_neg at hnone
    have hu : u ∈ exceptionalOrthogonal π := by
      apply (mem_exceptionalOrthogonal_iff π u).mpr
      intro E
      obtain ⟨z, hz⟩ := hnone E.val E.property
      obtain ⟨a, hfac, _habase, _haz⟩ :=
        PrimeCurvePointFiberFactorization.exists_factor_of_constant
          S E.val c q hbase z hz
      have hzero : E.val.picardRestrictionDegree (schemePicardPullbackHom q l) = 0 :=
        PrimeCurveInclusionLift.picardRestrictionDegree_pullback_eq_zero
          E.val E.val.inclusion E.val.range_inclusion.symm q E.val.toSpec a hfac l
      change S.numericalRestrictionDegree E.val
        (S.picardNumericalMap (Additive.ofMul (schemePicardPullbackHom q l))) = 0
      rw [S.numericalRestrictionDegree_picardNumericalMap]
      change (E.val.picardRestrictionDegree (schemePicardPullbackHom q l) : ℚ) = 0
      rw [hzero, Int.cast_zero]
    exact hne ((hmin.exceptionalOrthogonal_square_eq_zero_iff_of_kltDelPezzo
      hDP p hp hrank u hu).mp hsq)
  obtain ⟨E, hE, hnonconstant⟩ := hnonconstant
  have hklt : IsKlt X := by
    obtain ⟨KX, hKX, _⟩ := (isLogDelPezzoPair_zero_iff X).mp hDP
    exact ⟨KX, hKX⟩
  obtain ⟨η, hη⟩ := hmin.toIsResolution.exceptional_projectiveLine_iso_of_klt hklt E hE
  let f : projectiveSpace k 1 ⟶ C := η.inv ≫ E.inclusion ≫ q
  have hηbase : η.inv ≫ E.toSpec = projectiveSpaceToSpec k 1 := by
    rw [← hη, η.inv_hom_id_assoc]
  have hf : f ≫ c = projectiveSpaceToSpec k 1 := by
    change (η.inv ≫ E.inclusion ≫ q) ≫ c = _
    simp only [Category.assoc, hbase]
    exact hηbase
  have hηf : η.hom ≫ f = E.inclusion ≫ q := by
    simp only [f, η.hom_inv_id_assoc]
  have hsurj : Function.Surjective f.base := by
    rcases ProjectiveLineCurveMapDichotomy.constant_or_dominant_surjective
      c hCdim.le f hf with hconstant | hdominant
    · obtain ⟨z, hz⟩ := hconstant
      apply False.elim
      apply hnonconstant
      refine ⟨z, ?_⟩
      intro x hx
      obtain ⟨y, rfl⟩ := E.range_inclusion.symm ▸ hx
      have heq := congrArg (fun g : E.toScheme ⟶ C => g.base y) hηf
      exact heq.symm.trans (hz (η.hom.base y))
    · exact hdominant.2.2.1
  letI := IntrinsicNodal.stalkAlgebra c (genericPoint C)
  obtain ⟨φ, _⟩ := ProjectiveLineSurjectionRatFunc.exists_embedding c f hf hsurj
  exact ProperCurveRatFuncIsomorphism.exists_iso_of_embedding c hCreg hCdim φ

end KltDP.Geometry.KltIsotropicMapBase

#check @KltDP.Geometry.KltIsotropicMapBase.exists_projectiveLine_iso
#print axioms KltDP.Geometry.KltIsotropicMapBase.exists_projectiveLine_iso

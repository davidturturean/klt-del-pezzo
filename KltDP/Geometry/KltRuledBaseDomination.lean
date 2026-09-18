import KltDP.Geometry.RuledFiberConstancyOrthogonality
import KltDP.Geometry.KltExceptionalOrthogonalPositive
import KltDP.Geometry.KltResolutionExceptionalProjectiveLine
import KltDP.Geometry.ProjectiveLineCurveMapDichotomy

/-! A ruling obtained from an original rank-one klt del Pezzo resolution
has a base dominated by an actual projective line. If all original
exceptional curves were constant over that base, the actual pulled fibre
would contradict positivity of the original exceptional complement. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.KltRuledBaseDomination

open NormalProjectiveSurface ActualExceptionalNumerical

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X V : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) (hmin : IsMinimalResolution S X π)
  (hDP : IsKltDelPezzo X) (hrank : X.picardRank = 1)
  (p : ℕ) [CharP k p] (hp : 0 < p)
  (b : S.toScheme ⟶ V.toScheme) (hb : IsPointBlowupSequence S V b)
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

include hmin hDP hrank hp hb hV hCdim hCreg hbase hsurj hfib hσ in
/-- At least one original exceptional prime is nonconstant over the ruled base. -/
theorem exists_nonconstant_exceptional :
    ∃ E : S.PrimeCurve, IsExceptionalCurve π E ∧
      ¬ (∃ z : C, ∀ x ∈ (E : Set S.toScheme), (b ≫ q).base x = z) := by
  classical
  by_contra hnone
  push_neg at hnone
  obtain ⟨u, hne, hsq, hdegrees⟩ :=
    RuledFiberOriginalPullback.exists_original_isotropic_class_with_constant_degrees
      hV C c hCdim hCreg q hbase hsurj hfib σ hσ b hb hmin.regular
  have hu : u ∈ exceptionalOrthogonal π := by
    apply (mem_exceptionalOrthogonal_iff π u).mpr
    intro E
    exact hdegrees E.val (hnone E.val E.property)
  exact hne ((hmin.exceptionalOrthogonal_square_eq_zero_iff_of_kltDelPezzo
    hDP p hp hrank u hu).mp hsq)

include hmin hDP hrank hp hb hV hCdim hCreg hbase hsurj hfib hσ in
/-- An actual surjective map from P1 to the same original ruled base is
constructed from one original exceptional curve and its actual P1 isomorphism. -/
theorem exists_projectiveLine_surjection :
    ∃ f : projectiveSpace k 1 ⟶ C,
      f ≫ c = projectiveSpaceToSpec k 1 ∧ Function.Surjective f.base := by
  obtain ⟨E, hE, hnonconstant⟩ := exists_nonconstant_exceptional
    π hmin hDP hrank p hp b hb hV C c hCdim hCreg q hbase hsurj hfib σ hσ
  have hklt : IsKlt X := by
    obtain ⟨KX, hKX, _⟩ := (isLogDelPezzoPair_zero_iff X).mp hDP
    exact ⟨KX, hKX⟩
  obtain ⟨η, hη⟩ := hmin.toIsResolution.exceptional_projectiveLine_iso_of_klt hklt E hE
  let f : projectiveSpace k 1 ⟶ C := η.inv ≫ E.inclusion ≫ b ≫ q
  have hηbase : η.inv ≫ E.toSpec = projectiveSpaceToSpec k 1 := by
    rw [← hη, η.inv_hom_id_assoc]
  have hf : f ≫ c = projectiveSpaceToSpec k 1 := by
    change (η.inv ≫ E.inclusion ≫ b ≫ q) ≫ c = _
    simp only [Category.assoc, hbase, hb.over_base]
    exact hηbase
  have hηf : η.hom ≫ f = E.inclusion ≫ b ≫ q := by
    simp only [f, η.hom_inv_id_assoc]
  letI : IsProper c := RuledSurfaceSourceGeometry.base_isProper V c q hbase hsurj
  rcases ProjectiveLineCurveMapDichotomy.constant_or_dominant_surjective
    c (le_of_eq hCdim) f hf with hconstant | hdominant
  · obtain ⟨z, hz⟩ := hconstant
    apply False.elim
    apply hnonconstant
    refine ⟨z, ?_⟩
    intro x hx
    obtain ⟨y, rfl⟩ := E.range_inclusion.symm ▸ hx
    have heq := congrArg (fun g : E.toScheme ⟶ C => g.base y) hηf
    exact heq.symm.trans (hz (η.hom.base y))
  · exact ⟨f, hf, hdominant.2.2.1⟩

end KltDP.Geometry.KltRuledBaseDomination

#check @KltDP.Geometry.KltRuledBaseDomination.exists_projectiveLine_surjection
#print axioms KltDP.Geometry.KltRuledBaseDomination.exists_nonconstant_exceptional
#print axioms KltDP.Geometry.KltRuledBaseDomination.exists_projectiveLine_surjection

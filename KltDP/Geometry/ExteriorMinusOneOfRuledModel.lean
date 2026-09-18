import KltDP.Geometry.AbsoluteMinimalBirationalIso
import KltDP.Geometry.IsomorphismCanonicalNumericalInvariants
import KltDP.Geometry.SurfacePointBlowupSequenceGeometry
import KltDP.Geometry.SurfacePointBlowupSequenceBirational
import KltDP.Geometry.HartshorneRuledLiteralUse
import KltDP.Geometry.RuledNumericalBasis
import KltDP.Geometry.RuledSurfaceSourceGeometry

/-!
# An original exterior minus-one curve from an actual ruled model

The actual section and closed fibre give rank two on the ruled target.
If an original point-blowup sequence lowers rank, the source has a
minus-one prime; minimality of the original resolution makes it exterior.
No rational-minimal-surface classification is used or claimed here.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ExteriorMinusOneOfRuledModel

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A genuine drop in rank along the original blowup sequence forces a
minus-one prime outside the exceptional locus of the original resolution. -/
theorem exists_of_rank_drop
    {S X V : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}
    (hmin : IsMinimalResolution S X π)
    (hV : ∀ v : V.Point, RegularPoint V.toScheme v)
    (b : S.toScheme ⟶ V.toScheme) (hb : IsPointBlowupSequence S V b)
    (hrank : V.picardRank < S.picardRank) :
    ∃ E : S.PrimeCurve, IsMinusOneCurve hmin.regular E ∧
      ¬ IsExceptionalCurve π E := by
  classical
  by_contra hnone
  have hminimal : ∀ E : S.PrimeCurve, ¬ IsMinusOneCurve hmin.regular E := by
    intro E hE
    have hexterior : ¬ IsExceptionalCurve π E :=
      fun hExceptional => hmin.no_minusOne_curve E hExceptional hE
    exact hnone ⟨E, hE, hexterior⟩
  letI : IsIso b := S.isIso_of_no_minusOneCurve hmin.regular hminimal
    V hV b hb.over_base
    ((isBirational_iff_isBirationalScheme b).mpr hb.isBirationalScheme)
  have heq : S.picardRank = V.picardRank :=
    IsomorphismSurfaceInvariants.picardRank_eq b hb.over_base hmin.regular hV
  omega

/-- The original ruled surface has rank two, with its section and fibre
prime curves constructed from the actual ruling rather than supplied. -/
theorem ruled_picardRank_eq_two
    (V : NormalProjectiveSurface k)
    (hV : ∀ v : V.Point, RegularPoint V.toScheme v)
    (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [LocallyOfFiniteType c] [QuasiCompact c] [IsSeparated c]
    (hCdim : topologicalKrullDim C = 1)
    (hCreg : ∀ y : C, RegularPoint C y)
    (q : V.toScheme ⟶ C) (hbase : q ≫ c = V.structureMorphism)
    (hsurj : Function.Surjective q.base)
    (hfib : ∀ y : C, IsClosed ({y} : Set C) →
      ∃ e : q.fiber y ≅ projectiveSpace k 1,
        e.hom ≫ projectiveSpaceToSpec k 1 = q.fiberι y ≫ V.structureMorphism)
    (σ : C ⟶ V.toScheme) (hσ : σ ≫ q = 𝟙 C) :
    V.picardRank = 2 := by
  obtain ⟨S₀, e₀, he₀, _, _⟩ :=
    RuledSurfaceSourceGeometry.exists_sectionPrimeCurve V c q hbase hCdim σ hσ
  letI : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace c
  obtain ⟨y, _, hy⟩ := nonempty_inter_closedPoints
    (show (Set.univ : Set C).Nonempty from ⟨genericPoint C, Set.mem_univ _⟩)
    isOpen_univ.isLocallyClosed
  obtain ⟨e, he⟩ := hfib y hy
  obtain ⟨F, eF, heF, _, _⟩ :=
    RuledSurfaceSourceGeometry.exists_fiberPrimeCurve V q y hy e he
  obtain ⟨_, eNum, _⟩ := HartshorneRuledLiteralUse.decomposition_at
    V hV C c hCdim hCreg q hbase hsurj hfib σ hσ S₀ e₀ he₀ y hy F eF heF
  exact V.picardRank_eq_two_of_integralNumericalEquiv eNum

/-- The ruled branch produces an actual exterior minus-one prime on the
original minimal resolution as soon as its rank is greater than two. -/
theorem exists_of_ruled_model
    {S X V : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}
    (hmin : IsMinimalResolution S X π) (hrank : 2 < S.picardRank)
    (hV : ∀ v : V.Point, RegularPoint V.toScheme v)
    (b : S.toScheme ⟶ V.toScheme) (hb : IsPointBlowupSequence S V b)
    (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [LocallyOfFiniteType c] [QuasiCompact c] [IsSeparated c]
    (hCdim : topologicalKrullDim C = 1)
    (hCreg : ∀ y : C, RegularPoint C y)
    (q : V.toScheme ⟶ C) (hbase : q ≫ c = V.structureMorphism)
    (hsurj : Function.Surjective q.base)
    (hfib : ∀ y : C, IsClosed ({y} : Set C) →
      ∃ e : q.fiber y ≅ projectiveSpace k 1,
        e.hom ≫ projectiveSpaceToSpec k 1 = q.fiberι y ≫ V.structureMorphism)
    (σ : C ⟶ V.toScheme) (hσ : σ ≫ q = 𝟙 C) :
    ∃ E : S.PrimeCurve, IsMinusOneCurve hmin.regular E ∧
      ¬ IsExceptionalCurve π E := by
  have hVrank := ruled_picardRank_eq_two V hV C c hCdim hCreg
    q hbase hsurj hfib σ hσ
  exact exists_of_rank_drop hmin hV b hb (by omega)

end KltDP.Geometry.ExteriorMinusOneOfRuledModel

#check @KltDP.Geometry.ExteriorMinusOneOfRuledModel.exists_of_rank_drop
#check @KltDP.Geometry.ExteriorMinusOneOfRuledModel.ruled_picardRank_eq_two
#check @KltDP.Geometry.ExteriorMinusOneOfRuledModel.exists_of_ruled_model
#print axioms KltDP.Geometry.ExteriorMinusOneOfRuledModel.exists_of_rank_drop
#print axioms KltDP.Geometry.ExteriorMinusOneOfRuledModel.ruled_picardRank_eq_two
#print axioms KltDP.Geometry.ExteriorMinusOneOfRuledModel.exists_of_ruled_model

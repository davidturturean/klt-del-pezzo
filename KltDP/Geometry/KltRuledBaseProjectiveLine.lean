import KltDP.Geometry.KltRuledBaseDomination
import KltDP.Geometry.ProjectiveLineSurjectionRatFunc
import KltDP.Geometry.ProperCurveRatFuncIsomorphism

/-! The actual ruled base obtained from an original rank-one positive-
characteristic klt del Pezzo resolution is the original projective line.
The surjection, intrinsic function-field embedding, and curve isomorphism
are all constructed from the original data. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.KltRuledBaseProjectiveLine

open NormalProjectiveSurface

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
/-- The same original ruled base has an actual over-k isomorphism with P1. -/
theorem exists_iso :
    ∃ e : C ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 = c := by
  obtain ⟨f, hf, hfsurj⟩ := KltRuledBaseDomination.exists_projectiveLine_surjection
    π hmin hDP hrank p hp b hb hV C c hCdim hCreg q hbase hsurj hfib σ hσ
  letI : IsProper c := RuledSurfaceSourceGeometry.base_isProper V c q hbase hsurj
  letI := IntrinsicNodal.stalkAlgebra c (genericPoint C)
  obtain ⟨φ, _⟩ := ProjectiveLineSurjectionRatFunc.exists_embedding c f hf hfsurj
  exact ProperCurveRatFuncIsomorphism.exists_iso_of_embedding c hCreg hCdim φ

end KltDP.Geometry.KltRuledBaseProjectiveLine

#check @KltDP.Geometry.KltRuledBaseProjectiveLine.exists_iso
#print axioms KltDP.Geometry.KltRuledBaseProjectiveLine.exists_iso

import KltDP.Geometry.AbsoluteMinimalCartierCanonicalVanishing
import KltDP.Geometry.HartshorneClassificationLiteralUse

/-!
# Classification of the actual minimal target of a negative-nef surface

The contraction induction constructs the original minimal target and proves
all positive Cartier canonical vanishings there. The full reviewed surface
classification is then applied to that same target and its original maps.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- An actual negative-nef canonical pairing produces a rational or
geometrically ruled minimal target by an original point-blowup sequence. -/
theorem exists_rational_or_ruled_minimalModel_of_negative_nef
    (S : NormalProjectiveSurface k)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (K : CartierDivisor S.toScheme)
    (eK : cartierDivisorModule S.toScheme K ≅
      relativeDifferentialExterior S.structureMorphism 2)
    (H : InvertibleSheaf S.toScheme)
    (hH : Positivity.IsNef S.structureMorphism H)
    (hnegative : S.picardPairing hS (cartierPicardClass S.toScheme K) H.toPic < 0) :
    ∃ (V : NormalProjectiveSurface k)
      (hV : ∀ v : V.Point, RegularPoint V.toScheme v)
      (b : S.toScheme ⟶ V.toScheme),
      IsPointBlowupSequence S V b ∧
      b ≫ V.structureMorphism = S.structureMorphism ∧
      IsSmoothOfRelativeDimension 2 V.structureMorphism ∧
      V.picardRank ≤ S.picardRank ∧
      (Scheme.BirationalOver V.structureMorphism (projectiveSpaceToSpec k 2) ∨
        ∃ (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)),
          IsIntegral C ∧ LocallyOfFiniteType c ∧ QuasiCompact c ∧ IsSeparated c ∧
          topologicalKrullDim C = 1 ∧
          (∀ y : C, RegularPoint C y) ∧
          ∃ π : V.toScheme ⟶ C,
            π ≫ c = V.structureMorphism ∧
            Function.Surjective π.base ∧
            (∀ y : C, IsClosed ({y} : Set C) →
              ∃ e : π.fiber y ≅ projectiveSpace k 1,
                e.hom ≫ projectiveSpaceToSpec k 1 =
                  π.fiberι y ≫ V.structureMorphism) ∧
            ∃ σ : C ⟶ V.toScheme, σ ≫ π = 𝟙 C) := by
  obtain ⟨V, hV, b, hseq, _hmin, hover, hsmooth, hrank, hminimal,
      KV, eKV, _A, _hA, _hnegativeA, hvanish⟩ :=
    S.exists_absoluteMinimalModel_with_cartier_canonical_vanishing
      hS K eK H hH hnegative
  exact ⟨V, hV, b, hseq, hover, hsmooth, hrank,
    HartshorneClassificationLiteralUse.rational_or_ruled_of_positive_vanishing
      V hV hminimal KV eKV hvanish⟩

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.exists_rational_or_ruled_minimalModel_of_negative_nef
#print axioms KltDP.Geometry.NormalProjectiveSurface.exists_rational_or_ruled_minimalModel_of_negative_nef

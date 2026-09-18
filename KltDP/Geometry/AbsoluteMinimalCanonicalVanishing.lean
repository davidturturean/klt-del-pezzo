import KltDP.Geometry.AbsoluteMinimalNegativeNef
import KltDP.Geometry.NegativeNefCanonicalLinePowers

/-! The actual minimal target constructed by contraction has vanishing
positive pluricanonical spaces. This is the existing actual line-power
vanishing theorem applied to the nef line produced on that same target. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open SmoothCanonicalExteriorComparison SmoothSurfaceKaehlerAtlas
  InvertibleSheafSectionPowers

variable {k : Type u} [Field k] [IsAlgClosed k]

local instance minimalVanishingIntegral (T : NormalProjectiveSurface k) :
    IsIntegral T.toScheme := T.integral

/-- The original source nef/sign input yields a genuine absolute minimal
target with vanishing of every actual positive canonical tensor power. -/
theorem exists_absoluteMinimalModel_with_canonical_vanishing
    (S : NormalProjectiveSurface k)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (K : CartierDivisor S.toScheme)
    (eK : cartierDivisorModule S.toScheme K ≅ relativeDifferentialExterior S.structureMorphism 2)
    (H : InvertibleSheaf S.toScheme)
    (hH : Positivity.IsNef S.structureMorphism H)
    (hnegative : S.picardPairing hS (cartierPicardClass S.toScheme K) H.toPic < 0) :
    ∃ (V : NormalProjectiveSurface k)
      (hV : ∀ v : V.Point, RegularPoint V.toScheme v)
      (b : S.toScheme ⟶ V.toScheme),
      IsPointBlowupSequence S V b ∧
      (∀ C : V.PrimeCurve, ¬ IsMinusOneCurve hV C) ∧
      b ≫ V.structureMorphism = S.structureMorphism ∧ V.picardRank ≤ S.picardRank ∧
      letI : IsSmoothOfRelativeDimension 2 V.structureMorphism :=
        V.isSmoothOfRelativeDimension_two_of_regularPoints hV
      ∀ (n : ℕ), 0 < n → cohomologyDimension V.structureMorphism
        (power (canonicalSheafOfSmoothSurface V.structureMorphism) n).obj 0 = 0 := by
  obtain ⟨V, hV, b, hseq, hmin, hover, hsmooth, hrank, KV, eKV, A, hA, hnegativeA⟩ :=
    S.exists_absoluteMinimalModel_with_negative_nef hS K eK H hH hnegative
  refine ⟨V, hV, b, hseq, hmin, hover, hrank, ?_⟩
  letI : IsSmoothOfRelativeDimension 2 V.structureMorphism :=
    V.isSmoothOfRelativeDimension_two_of_regularPoints hV
  intro n hn
  exact NegativeNefCanonicalTensorPowers.canonicalTensorPower_hZero_of_negative_nef_line
    V hV KV eKV A hA hnegativeA n hn

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.exists_absoluteMinimalModel_with_canonical_vanishing
#print axioms KltDP.Geometry.NormalProjectiveSurface.exists_absoluteMinimalModel_with_canonical_vanishing

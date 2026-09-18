import KltDP.Geometry.AbsoluteMinimalNegativeNef
import KltDP.Geometry.AbsoluteMinimalBirationalIso
import KltDP.Geometry.NegativeNefLineCartierMultiples

/-!
# Literal Cartier pluricanonical vanishing on the actual minimal target

The target, its canonical divisor and its nef line are the same objects
constructed by the original contraction induction. The existing universal
birational-morphism minimality theorem and the original Cartier-multiple
vanishing theorem supply the two literal hypotheses of the surface criterion.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open SmoothCanonicalExteriorComparison

variable {k : Type u} [Field k] [IsAlgClosed k]

local instance minimalCartierVanishingIntegral (T : NormalProjectiveSurface k) :
    IsIntegral T.toScheme := T.integral

/-- The actual minimal target satisfies universal birational-morphism
minimality and vanishing of every literal O(nK) for its constructed K. -/
theorem exists_absoluteMinimalModel_with_cartier_canonical_vanishing
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
      b ≫ V.structureMorphism = S.structureMorphism ∧
      IsSmoothOfRelativeDimension 2 V.structureMorphism ∧ V.picardRank ≤ S.picardRank ∧
      (∀ (T : NormalProjectiveSurface k)
        (hT : ∀ t : T.Point, RegularPoint T.toScheme t)
        (g : V.toScheme ⟶ T.toScheme),
        g ≫ T.structureMorphism = V.structureMorphism → IsBirational g → IsIso g) ∧
      ∃ (KV : CartierDivisor V.toScheme)
        (_ : cartierDivisorModule V.toScheme KV ≅ relativeDifferentialExterior V.structureMorphism 2)
        (A : InvertibleSheaf V.toScheme),
        Positivity.IsNef V.structureMorphism A ∧
        V.picardPairing hV (cartierPicardClass V.toScheme KV) A.toPic < 0 ∧
        ∀ (n : ℕ), 0 < n → cohomologyDimension V.structureMorphism
          (cartierDivisorModule V.toScheme (n • KV)) 0 = 0 := by
  obtain ⟨V, hV, b, hseq, hmin, hover, hsmooth, hrank, KV, eKV, A, hA, hnegativeA⟩ :=
    S.exists_absoluteMinimalModel_with_negative_nef hS K eK H hH hnegative
  exact ⟨V, hV, b, hseq, hmin, hover, hsmooth, hrank,
    V.isIso_of_no_minusOneCurve hV hmin, KV, eKV, A, hA, hnegativeA,
    fun n hn => NegativeNefCanonicalTensorPowers.hZero_multiple_of_negative_nef_line
      V hV KV A hA hnegativeA n hn⟩

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.exists_absoluteMinimalModel_with_cartier_canonical_vanishing
#print axioms KltDP.Geometry.NormalProjectiveSurface.exists_absoluteMinimalModel_with_cartier_canonical_vanishing

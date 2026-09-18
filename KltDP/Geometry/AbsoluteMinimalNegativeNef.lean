import KltDP.Geometry.ContractionNegativeNef
import KltDP.Geometry.AbsoluteMinimalSurface
import KltDP.Geometry.SmoothCanonicalCartierExterior

/-!
# An actual minimal target retaining negative canonical nef pairing

Use the existing contraction induction on the original Picard rank. Every
step descends the actual nef line by the proved Picard decomposition. The
final target, its morphism, canonical divisor and nef line are all constructed.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open SmoothCanonicalExteriorComparison SmoothCanonicalCartierRepresentative
  SmoothCanonicalCartierExterior

variable {k : Type u} [Field k] [IsAlgClosed k]

local instance negativeMinimalIntegral (T : NormalProjectiveSurface k) :
    IsIntegral T.toScheme := T.integral

/-- There is an original point-blowup sequence to an actual smooth absolute
minimal surface carrying an actual nef line with negative canonical pairing. -/
theorem exists_absoluteMinimalModel_with_negative_nef
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
      ∃ (KV : CartierDivisor V.toScheme)
        (_ : cartierDivisorModule V.toScheme KV ≅ relativeDifferentialExterior V.structureMorphism 2)
        (A : InvertibleSheaf V.toScheme),
        Positivity.IsNef V.structureMorphism A ∧
        V.picardPairing hV (cartierPicardClass V.toScheme KV) A.toPic < 0 := by
  let P := fun (T : NormalProjectiveSurface k)
      (hT : ∀ t : T.Point, RegularPoint T.toScheme t) =>
    ∀ (KT : CartierDivisor T.toScheme)
      (_ : cartierDivisorModule T.toScheme KT ≅ relativeDifferentialExterior T.structureMorphism 2)
      (L : InvertibleSheaf T.toScheme),
      Positivity.IsNef T.structureMorphism L →
      T.picardPairing hT (cartierPicardClass T.toScheme KT) L.toPic < 0 →
      ∃ (V : NormalProjectiveSurface k)
        (hV : ∀ v : V.Point, RegularPoint V.toScheme v)
        (g : T.toScheme ⟶ V.toScheme),
        IsPointBlowupSequence T V g ∧
        (∀ C : V.PrimeCurve, ¬ IsMinusOneCurve hV C) ∧
        g ≫ V.structureMorphism = T.structureMorphism ∧
        IsSmoothOfRelativeDimension 2 V.structureMorphism ∧ V.picardRank ≤ T.picardRank ∧
        ∃ (KV : CartierDivisor V.toScheme)
          (_ : cartierDivisorModule V.toScheme KV ≅ relativeDifferentialExterior V.structureMorphism 2)
          (A : InvertibleSheaf V.toScheme),
          Positivity.IsNef V.structureMorphism A ∧
          V.picardPairing hV (cartierPicardClass V.toScheme KV) A.toPic < 0
  have hP : P S hS := by
    apply S.absolute_contraction_induction hS P
    · intro T hT hminimal KT eKT L hL hneg
      exact ⟨T, hT, 𝟙 T.toScheme,
        IsPointBlowupSequence.of_isIso _ (by infer_instance) (by simp),
        hminimal, by simp, T.isSmoothOfRelativeDimension_two_of_regularPoints hT,
        le_rfl, KT, eKT, L, hL, hneg⟩
    · intro T T' hT E b hminus hb ih KT eKT L hL hneg
      letI : IsSmoothOfRelativeDimension 2 T'.structureMorphism :=
        T'.isSmoothOfRelativeDimension_two_of_regularPoints hb.regular
      let KT' := cartierRepresentative T'.structureMorphism
      let eKT' : cartierDivisorModule T'.toScheme KT' ≅
          relativeDifferentialExterior T'.structureMorphism 2 :=
        representativeIsoExterior T'.structureMorphism
      obtain ⟨A, hA, hnegA⟩ := hb.exists_nef_canonical_negative
        hT hminus KT KT' eKT eKT' L hL hneg
      obtain ⟨V, hV, g, hseq, hmin, hg, hsmooth, hrank, KV, eKV, B, hB, hnegB⟩ :=
        ih KT' eKT' A hA hnegA
      obtain ⟨z, _, _, _, hbl⟩ := hb.center
      refine ⟨V, hV, b ≫ g, IsPointBlowupSequence.step b g z hbl hseq,
        hmin, ?_, hsmooth, ?_, KV, eKV, B, hB, hnegB⟩
      · rw [Category.assoc, hg, hb.over_base]
      · exact hrank.trans (by have h := hb.picardRank_eq_add_one hT hminus; omega)
  exact hP K eK H hH hnegative

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.exists_absoluteMinimalModel_with_negative_nef
#print axioms KltDP.Geometry.NormalProjectiveSurface.exists_absoluteMinimalModel_with_negative_nef

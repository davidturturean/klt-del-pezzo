import KltDP.Geometry.ContractionNefDescent
import KltDP.Geometry.ContractionCanonicalPicard

/-! Negative canonical pairing with an actual nef line descends through
the original contraction. Both the target line and its nefness are produced
internally. The original canonical representatives may be independently chosen. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.IsContraction

open SmoothCanonicalExteriorComparison

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S T : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme}
  {E : S.PrimeCurve}

local instance negativeNefSourceIntegral : IsIntegral S.toScheme := S.integral
local instance negativeNefTargetIntegral : IsIntegral T.toScheme := T.integral

/-- An actual nef line with negative canonical pairing produces an actual
target nef line with negative canonical pairing under a minus-one contraction. -/
theorem exists_nef_canonical_negative
    (hb : IsContraction S T b E)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (hminus : IsMinusOneCurve hS E)
    (KS : CartierDivisor S.toScheme) (KT : CartierDivisor T.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅ relativeDifferentialExterior S.structureMorphism 2)
    (eKT : cartierDivisorModule T.toScheme KT ≅ relativeDifferentialExterior T.structureMorphism 2)
    (H : InvertibleSheaf S.toScheme)
    (hH : Positivity.IsNef S.structureMorphism H)
    (hnegative : S.picardPairing hS (cartierPicardClass S.toScheme KS) H.toPic < 0) :
    ∃ A : InvertibleSheaf T.toScheme,
      Positivity.IsNef T.structureMorphism A ∧
      T.picardPairing hb.regular (cartierPicardClass T.toScheme KT) A.toPic < 0 := by
  obtain ⟨A, m, hm, hA, hHclass⟩ := hb.exists_nef_picardDecomposition hS hminus H hH
  let e := hb.picardDecomposition hS hminus
  have hKSclass : cartierPicardClass S.toScheme KS =
      e.symm (cartierPicardClass T.toScheme KT, Multiplicative.ofAdd (1 : ℤ)) := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact hb.canonical_picardDecomposition hS hminus KS KT eKS eKT
  have hpair := hb.picardDecomposition_pairing hS hminus
    (cartierPicardClass T.toScheme KT) (cartierPicardClass T.toScheme A) 1 m
  rw [← hKSclass, ← hHclass, one_mul] at hpair
  refine ⟨cartierDivisorInvertibleSheaf T.toScheme A, hA, ?_⟩
  change T.picardPairing hb.regular (cartierPicardClass T.toScheme KT)
    (cartierPicardClass T.toScheme A) < 0
  omega

end KltDP.Geometry.IsContraction

#check @KltDP.Geometry.IsContraction.exists_nef_canonical_negative
#print axioms KltDP.Geometry.IsContraction.exists_nef_canonical_negative

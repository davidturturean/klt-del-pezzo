import KltDP.Geometry.SmoothOpenCanonicalWeil

/-!
# Canonical Weil divisors from the original top differential sheaf

A canonical Weil divisor is the extension of a Cartier representative of
the original top differential sheaf on a smooth open containing every
prime generic point. Extension uses the original local rational equations
and their original discrete valuation orders. No numerical class,
discrepancy bound, resolution or classification conclusion defines it.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry

variable {k : Type u} [Field k]

def IsCanonicalWeilDivisor (X : NormalProjectiveSurface k) (KX : X.WeilDivisor) : Prop :=
  ∃ (U : X.toScheme.Opens) (hne : Nonempty U.toScheme),
    letI : Nonempty U.toScheme := hne
    letI : Nonempty U := ⟨Classical.choice hne⟩
    letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
    IsSmoothOfRelativeDimension 2 (U.ι ≫ X.structureMorphism) ∧
      (∀ C : X.PrimeCurve, C.genericPoint ∈ U) ∧
      ∃ KU : CartierDivisor U.toScheme,
        Nonempty (cartierDivisorModule U.toScheme KU ≅
          SmoothCanonicalExteriorComparison.relativeDifferentialExterior
            (U.ι ≫ X.structureMorphism) 2) ∧
        OpenCartierWeil.restrictedWeilHom U KU = KX

namespace IsCanonicalWeilDivisor

variable (X : NormalProjectiveSurface k) (U : X.toScheme.Opens) [Nonempty U.toScheme]
local instance : Nonempty U := ⟨Classical.choice inferInstance⟩
local instance : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

theorem of_smooth_open
    [IsSmoothOfRelativeDimension 2 (U.ι ≫ X.structureMorphism)]
    (hU : ∀ C : X.PrimeCurve, C.genericPoint ∈ U)
    (KU : CartierDivisor U.toScheme)
    (eKU : cartierDivisorModule U.toScheme KU ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ X.structureMorphism) 2) :
    IsCanonicalWeilDivisor X (OpenCartierWeil.restrictedWeilHom U KU) :=
  ⟨U, inferInstance, inferInstance, hU, KU, ⟨eKU⟩, rfl⟩

theorem smoothOpen_weilRepresentative
    [IsSmoothOfRelativeDimension 2 (U.ι ≫ X.structureMorphism)]
    (hU : ∀ C : X.PrimeCurve, C.genericPoint ∈ U) :
    IsCanonicalWeilDivisor X (SmoothOpenCanonicalWeil.weilRepresentative X U) :=
  of_smooth_open X U hU (SmoothOpenCanonicalWeil.cartierRepresentative X U)
    (SmoothOpenCanonicalWeil.representativeIsoExterior X U)

end IsCanonicalWeilDivisor
end KltDP.Geometry

#check @KltDP.Geometry.IsCanonicalWeilDivisor
#print axioms KltDP.Geometry.IsCanonicalWeilDivisor.of_smooth_open
#print axioms KltDP.Geometry.IsCanonicalWeilDivisor.smoothOpen_weilRepresentative

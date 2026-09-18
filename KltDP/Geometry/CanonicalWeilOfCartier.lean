import KltDP.Geometry.CanonicalWeilDivisor
import KltDP.Geometry.CanonicalCartierOpenPullback
import KltDP.Geometry.OpenCartierWeilRestriction

/-!
# An actual canonical Cartier representative defines a canonical Weil divisor

Use the whole open as the smooth open in the existing definition. The original
Cartier restriction carries the given exterior-square isomorphism, and its
original Weil extension is exactly the global Cartier-to-Weil image.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.IsCanonicalWeilDivisor

open OpenImmersionRational

/-- A genuine Cartier representative of the original second differential
exterior on a smooth surface gives a canonical Weil divisor in the existing
geometric definition. -/
theorem of_cartier
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    [IsSmoothOfRelativeDimension 2 X.structureMorphism]
    (K : CartierDivisor X.toScheme)
    (eK : cartierDivisorModule X.toScheme K ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        X.structureMorphism 2) :
    IsCanonicalWeilDivisor X (X.cartierToWeilHom K) := by
  let U : X.toScheme.Opens := ⊤
  letI : Nonempty U.toScheme := ⟨⟨genericPoint X.toScheme, trivial⟩⟩
  letI : Nonempty U := ⟨Classical.choice inferInstance⟩
  letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  letI : IsSmoothOfRelativeDimension 2 (U.ι ≫ X.structureMorphism) :=
    inferInstanceAs (IsSmoothOfRelativeDimension (0 + 2)
      (U.ι ≫ X.structureMorphism))
  have eU : cartierDivisorModule U.toScheme (cartierRestrictionHom U.ι K) ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ X.structureMorphism) 2 := by
    simpa only [DominantCartierPullback.pullbackHom_eq_cartierRestrictionHom] using
      CanonicalCartierOpenPullback.canonicalModuleIso U.ι X.structureMorphism
        (U.ι ≫ X.structureMorphism) rfl K eK
  have hU : ∀ C : X.PrimeCurve, C.genericPoint ∈ U := fun _ => trivial
  have hcanonical := of_smooth_open X U hU (cartierRestrictionHom U.ι K) eU
  exact (OpenCartierWeil.restrictedWeilHom_restriction U hU K) ▸ hcanonical

end KltDP.Geometry.IsCanonicalWeilDivisor

#check @KltDP.Geometry.IsCanonicalWeilDivisor.of_cartier
#print axioms KltDP.Geometry.IsCanonicalWeilDivisor.of_cartier

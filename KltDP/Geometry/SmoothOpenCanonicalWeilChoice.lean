import KltDP.Geometry.OpenCartierWeilPrincipal
import KltDP.Geometry.SmoothOpenCanonicalWeil

/-!
# Independence of the Cartier representative on a fixed smooth large open

Representatives of the actual exterior square of differentials differ by a
principal Cartier divisor. The original function-field transport proves that
their extensions define the same Weil divisor class on the original surface.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SmoothOpenCanonicalWeil

variable {k : Type u} [Field k] (Y : NormalProjectiveSurface k)
variable (U : Y.toScheme.Opens) [Nonempty U.toScheme]

local instance : Nonempty U := ⟨Classical.choice inferInstance⟩
local instance : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

/-- Cartier representatives of the same intrinsic top-differential sheaf
extend to linearly equivalent Weil divisors on the original surface. -/
theorem exterior_choices_linearlyEquivalent
    (hU : ∀ C : Y.PrimeCurve, C.genericPoint ∈ U)
    (D E : CartierDivisor U.toScheme)
    (eD : cartierDivisorModule U.toScheme D ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ Y.structureMorphism) 2)
    (eE : cartierDivisorModule U.toScheme E ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ Y.structureMorphism) 2) :
    Y.LinearlyEquivalent (OpenCartierWeil.restrictedWeilHom U D)
      (OpenCartierWeil.restrictedWeilHom U E) := by
  obtain ⟨f, hf⟩ := SmoothCanonicalCartierExterior.exterior_choices_principal
    (U.ι ≫ Y.structureMorphism) 2 D E eD eE
  exact OpenCartierWeil.restrictedWeilHom_linearlyEquivalent_of_principal U hU D E f hf

/-- The chosen canonical Weil class equals that from every actual Cartier
representative of the intrinsic exterior square on the same large open. -/
theorem weilRepresentative_class_eq
    [IsSmoothOfRelativeDimension 2 (U.ι ≫ Y.structureMorphism)]
    (hU : ∀ C : Y.PrimeCurve, C.genericPoint ∈ U)
    (D : CartierDivisor U.toScheme)
    (eD : cartierDivisorModule U.toScheme D ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ Y.structureMorphism) 2) :
    Y.weilClassMap (weilRepresentative Y U) =
      Y.weilClassMap (OpenCartierWeil.restrictedWeilHom U D) := by
  apply (Y.linearlyEquivalent_iff_weilClassMap_eq _ _).mp
  exact exterior_choices_linearlyEquivalent Y U hU
    (cartierRepresentative Y U) D (representativeIsoExterior Y U) eD

end KltDP.Geometry.SmoothOpenCanonicalWeil

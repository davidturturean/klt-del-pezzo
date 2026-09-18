import KltDP.Geometry.SmoothCanonicalCartierExterior
import KltDP.Geometry.OpenCartierWeil

/-!
The canonical Cartier representative on an actual smooth surface open
produces a finite Weil divisor on the original normal projective surface.
Its sheaf is the original second exterior power of relative differentials;
its coefficients are orders of the representative's actual transported
local rational equations. No numerical or ample expression defines it.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SmoothOpenCanonicalWeil

variable {k : Type u} [Field k] (Y : NormalProjectiveSurface k)
  (U : Y.toScheme.Opens) [Nonempty U.toScheme]

local instance openNonempty : Nonempty U := ⟨Classical.choice inferInstance⟩
local instance openIntegral : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

variable [IsSmoothOfRelativeDimension 2 (U.ι ≫ Y.structureMorphism)]

/-- The actual Cartier representative on the original smooth open. -/
def cartierRepresentative : CartierDivisor U.toScheme :=
  SmoothCanonicalCartierRepresentative.cartierRepresentative (U.ι ≫ Y.structureMorphism)

/-- The corresponding original finite Weil divisor on the target surface. -/
def weilRepresentative : Y.WeilDivisor :=
  OpenCartierWeil.restrictedWeilHom U (cartierRepresentative Y U)

/-- The original Cartier sheaf represents the intrinsic second exterior
power of relative differentials on the original open. -/
def representativeIsoExterior :
    cartierDivisorModule U.toScheme (cartierRepresentative Y U) ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ Y.structureMorphism) 2 :=
  SmoothCanonicalCartierExterior.representativeIsoExterior (U.ι ≫ Y.structureMorphism)

/-- Every prime generic point in the open sees the order of the actual
transported local equation, using the original target order map. -/
theorem weilRepresentative_apply (C : Y.PrimeCurve) (hC : C.genericPoint ∈ U) :
    weilRepresentative Y U C = C.order
      (OpenCartierWeil.restrictedEquation U (cartierRepresentative Y U)
        ⟨C.genericPoint, hC⟩) :=
  OpenCartierWeil.restrictedCoefficient_of_mem U (cartierRepresentative Y U) C hC

end KltDP.Geometry.SmoothOpenCanonicalWeil

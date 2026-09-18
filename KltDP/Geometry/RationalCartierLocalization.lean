import KltDP.LinearAlgebra.RationalSpanLocalization
import KltDP.Geometry.NormalCartierWeilInjective

/-!
The existing rational Cartier submodule is the localization of the
original signed Cartier divisor group. Normal Cartier-to-Weil injectivity
and injectivity of coefficient rationalization discharge the algebraic
criterion; no alternative rational Cartier group is introduced.
-/

noncomputable section

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

/-- Normal Cartier-to-Weil injectivity survives the original rational
coefficient inclusion. -/
theorem rationalCartierToWeilHom_injective :
    Function.Injective X.rationalCartierToWeilHom := by
  intro A B h
  apply X.cartierToWeilHom_injective
  exact rationalizeWeilDivisor_injective h

/-- The original Cartier map into the already defined rational Cartier
submodule, regarded as an integer-linear map. -/
def rationalCartierMap :
    CartierDivisor X.toScheme →ₗ[ℤ] X.rationalCartierSubmodule :=
  KltDP.LinearAlgebra.RationalSpanLocalization.spanMap X.rationalCartierToWeilHom

@[simp]
theorem rationalCartierMap_coe (A : CartierDivisor X.toScheme) :
    (X.rationalCartierMap A : X.RationalWeilDivisor) = X.rationalCartierToWeilHom A := rfl

/-- The original Cartier numerator map is localization at nonzero integers. -/
instance rationalCartierMap_isLocalizedModule :
    IsLocalizedModule (nonZeroDivisors ℤ) X.rationalCartierMap :=
  KltDP.LinearAlgebra.RationalSpanLocalization.spanMap_isLocalizedModule
    X.rationalCartierToWeilHom X.rationalCartierToWeilHom_injective

end KltDP.Geometry.NormalProjectiveSurface

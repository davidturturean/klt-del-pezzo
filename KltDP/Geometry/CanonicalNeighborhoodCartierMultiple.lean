import KltDP.Geometry.OpenCartierWeilInjective
import KltDP.Geometry.OpenCartierWeilNestedRestriction
import KltDP.Geometry.OpenCartierWeilRestriction

/-!
# The original Cartier numerator on the canonical neighborhood

Agreement with the original canonical reference on its overlap determines
all retained prime coefficients. Normal open Cartier-to-Weil injectivity
then gives the actual Cartier equality for every supplied integral multiple.
No local numerator compatibility or fixed Cartier index is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CanonicalNeighborhoodCartierMultiple

open OpenCartierWeil OpenImmersionRational

variable {k : Type u} [Field k] [IsAlgClosed k] {X : NormalProjectiveSurface k}
    (U W : X.toScheme.Opens) [Nonempty U.toScheme] [Nonempty W.toScheme]

local instance : Nonempty U := ⟨Classical.choice inferInstance⟩
local instance : Nonempty W := ⟨Classical.choice inferInstance⟩
local instance : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
local instance : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι

local instance intersection_nonempty : Nonempty (U ⊓ W).toScheme := by
  exact ⟨⟨genericPoint X.toScheme,
    ⟨genericPoint_mem_nonempty_open X.toScheme U,
      genericPoint_mem_nonempty_open X.toScheme W⟩⟩⟩

local instance : Nonempty (U ⊓ W : X.toScheme.Opens) :=
  ⟨Classical.choice (intersection_nonempty U W)⟩
local instance : IsIntegral (U ⊓ W).toScheme :=
  isIntegral_of_isOpenImmersion (U ⊓ W).ι

/-- Every original global Cartier multiple restricts to the corresponding
multiple of the local canonical representative constructed from the overlap. -/
theorem cartier_multiple_eq_of_overlap
    (hU : ∀ C : X.PrimeCurve, C.genericPoint ∈ U)
    (KU : CartierDivisor U.toScheme) (DW : CartierDivisor W.toScheme)
    (hcompat : cartierRestrictionHom (X.toScheme.homOfLE
        (show U ⊓ W ≤ W from inf_le_right)) DW =
      cartierRestrictionHom (X.toScheme.homOfLE
        (show U ⊓ W ≤ U from inf_le_left)) KU)
    (KX : X.WeilDivisor) (hKX : restrictedWeilHom U KU = KX)
    (n : ℕ) (A : CartierDivisor X.toScheme)
    (hA : X.cartierToWeilHom A = n • KX) :
    n • DW = cartierRestrictionHom W.ι A := by
  apply restrictedWeilHom_injective W
  apply Finsupp.ext
  intro C
  change restrictedCoefficient W (n • DW) C =
    restrictedCoefficient W (cartierRestrictionHom W.ι A) C
  by_cases hCW : C.genericPoint ∈ W
  · have hCV : C.genericPoint ∈ U ⊓ W := ⟨hU C, hCW⟩
    have hC : restrictedCoefficient W DW C = restrictedCoefficient U KU C := by
      calc
        _ = restrictedCoefficient (U ⊓ W)
            (cartierRestrictionHom (X.toScheme.homOfLE
              (show U ⊓ W ≤ W from inf_le_right)) DW) C :=
          (restrictedCoefficient_nestedRestriction W (U ⊓ W) inf_le_right DW C hCV).symm
        _ = restrictedCoefficient (U ⊓ W)
            (cartierRestrictionHom (X.toScheme.homOfLE
              (show U ⊓ W ≤ U from inf_le_left)) KU) C :=
          congrArg (fun D : CartierDivisor (U ⊓ W).toScheme =>
            restrictedCoefficient (U ⊓ W) D C) hcompat
        _ = restrictedCoefficient U KU C :=
          restrictedCoefficient_nestedRestriction U (U ⊓ W) inf_le_left KU C hCV
    have hleft := congrArg (fun D : X.WeilDivisor => D C)
      ((restrictedWeilHom W).map_nsmul DW n)
    change restrictedCoefficient W (n • DW) C = n • restrictedCoefficient W DW C at hleft
    have hAC := congrArg (fun D : X.WeilDivisor => D C)
      (hA.trans (congrArg (fun D : X.WeilDivisor => n • D) hKX.symm))
    change X.cartierToWeilHom A C = n • restrictedCoefficient U KU C at hAC
    exact hleft.trans ((congrArg (fun z : ℤ => n • z) hC).trans
      (hAC.symm.trans (restrictedCoefficient_restriction W A C hCW).symm))
  · rw [restrictedCoefficient_of_not_mem W (n • DW) C hCW,
      restrictedCoefficient_of_not_mem W (cartierRestrictionHom W.ι A) C hCW]

end KltDP.Geometry.CanonicalNeighborhoodCartierMultiple

import KltDP.Geometry.CanonicalPrincipalNeighborhoodExtension
import KltDP.Geometry.CanonicalNeighborhoodCartierMultiple
import KltDP.Geometry.CommonTargetCanonicalRestriction

/-!
# The fixed target canonical divisor on a framed open neighborhood

Compare the native frame with the original canonical reference on the
literal intersection. The actual principal correction gives the same
coordinate there and the original KX coefficient on every retained prime.
Every original Cartier numerator then agrees on the whole neighborhood.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CanonicalOpenNeighborhoodExtension

open CartierRationalCoordinate DominantCartierPullback OpenCartierWeil OpenImmersionRational
open SmoothCanonicalExteriorComparison CommonTargetCanonical

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
    (U W : X.toScheme.Opens) [Nonempty U.toScheme] [Nonempty W.toScheme]

local instance : Nonempty U := ⟨Classical.choice inferInstance⟩
local instance : Nonempty W := ⟨Classical.choice inferInstance⟩
local instance : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
local instance : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
local instance : Nonempty (U ⊓ W).toScheme :=
  CanonicalNeighborhoodCartierMultiple.intersection_nonempty U W
local instance : Nonempty (U ⊓ W : X.toScheme.Opens) := ⟨Classical.choice inferInstance⟩
local instance : IsIntegral (U ⊓ W).toScheme := isIntegral_of_isOpenImmersion (U ⊓ W).ι

local instance openGeneric {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    (g : Y ⟶ Z) [IsOpenImmersion g] : GenericPointPreserving g :=
  ⟨genericPoint_eq_of_isOpenImmersion g⟩

/-- A framed neighborhood acquires the original target canonical Weil
representative, not a independently chosen canonical numerical class. -/
theorem exists_canonical_representative
    (hU : ∀ C : X.PrimeCurve, C.genericPoint ∈ U)
    (KU : CartierDivisor U.toScheme)
    (eU : cartierDivisorModule U.toScheme KU ≅
      relativeDifferentialExterior (U.ι ≫ X.structureMorphism) 2)
    (KX : X.WeilDivisor) (hKX : restrictedWeilHom U KU = KX)
    (eW : cartierDivisorModule W.toScheme 0 ≅
      relativeDifferentialExterior (W.ι ≫ X.structureMorphism) 2) :
    ∃ (DW : CartierDivisor W.toScheme)
      (eDW : cartierDivisorModule W.toScheme DW ≅
        relativeDifferentialExterior (W.ι ≫ X.structureMorphism) 2),
      coordinate (U ⊓ W).toScheme
          (pullbackHom (X.toScheme.homOfLE (show U ⊓ W ≤ W from inf_le_right)) DW)
          (relativeDifferentialExterior ((U ⊓ W).ι ≫ X.structureMorphism) 2)
          (canonicalRestrictionIso X W (U ⊓ W) inf_le_right DW eDW) =
        coordinate (U ⊓ W).toScheme
          (pullbackHom (X.toScheme.homOfLE (show U ⊓ W ≤ U from inf_le_left)) KU)
          (relativeDifferentialExterior ((U ⊓ W).ι ≫ X.structureMorphism) 2)
          (canonicalRestrictionIso X U (U ⊓ W) inf_le_left KU eU) ∧
      (∀ C : X.PrimeCurve, C.genericPoint ∈ W → restrictedCoefficient W DW C = KX C) ∧
      ∀ (n : ℕ) (A : CartierDivisor X.toScheme), X.cartierToWeilHom A = n • KX →
        n • DW = cartierRestrictionHom W.ι A := by
  let i := X.toScheme.homOfLE (show U ⊓ W ≤ W from inf_le_right)
  let j := X.toScheme.homOfLE (show U ⊓ W ≤ U from inf_le_left)
  obtain ⟨q, hq⟩ := CanonicalPrincipalNeighborhoodExtension.exists_principal_normalization
    i j (W.ι ≫ X.structureMorphism) (U.ι ≫ X.structureMorphism)
    ((U ⊓ W).ι ≫ X.structureMorphism)
    (restriction_structure X W (U ⊓ W) inf_le_right)
    (restriction_structure X U (U ⊓ W) inf_le_left) eW KU eU
  let DW := rescaleDivisor W.toScheme 0 q
  let eDW := rescaleIso W.toScheme 0
    (relativeDifferentialExterior (W.ι ≫ X.structureMorphism) 2) eW q
  have hEq : pullbackHom i DW = pullbackHom j KU := hq.2
  have hcompat : cartierRestrictionHom i DW = cartierRestrictionHom j KU := by
    calc
      _ = pullbackHom i DW := (congrArg (fun h => h DW)
        (pullbackHom_eq_cartierRestrictionHom i)).symm
      _ = pullbackHom j KU := hEq
      _ = _ := congrArg (fun h => h KU) (pullbackHom_eq_cartierRestrictionHom j)
  refine ⟨DW, eDW, hq.1, ?_, ?_⟩
  · intro C hCW
    have hCV : C.genericPoint ∈ U ⊓ W := ⟨hU C, hCW⟩
    calc
      _ = restrictedCoefficient (U ⊓ W) (cartierRestrictionHom i DW) C :=
        (restrictedCoefficient_nestedRestriction W (U ⊓ W) inf_le_right DW C hCV).symm
      _ = restrictedCoefficient (U ⊓ W) (cartierRestrictionHom j KU) C :=
        congrArg (fun D => restrictedCoefficient (U ⊓ W) D C) hcompat
      _ = restrictedCoefficient U KU C :=
        restrictedCoefficient_nestedRestriction U (U ⊓ W) inf_le_left KU C hCV
      _ = KX C := congrArg (fun D : X.WeilDivisor => D C) hKX
  · intro n A hA
    exact CanonicalNeighborhoodCartierMultiple.cartier_multiple_eq_of_overlap
      U W hU KU DW hcompat KX hKX n A hA

end KltDP.Geometry.CanonicalOpenNeighborhoodExtension

import KltDP.Geometry.RegularSurfacePointCanonicalFrame
import KltDP.Geometry.CanonicalOpenNeighborhoodExtension
import KltDP.Geometry.CanonicalWeilDivisor

/-!
# The fixed canonical Weil divisor near an original regular target point

The original canonical reference is used only on its overlap with the new
native framed neighborhood. It is never assumed to contain x. The actual
coordinate multiplier supplies the local Cartier representative and every
original Cartier numerator agrees there by normal Cartier-to-Weil injectivity.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open SmoothCanonicalExteriorComparison OpenCartierWeil OpenImmersionRational

variable {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) {S : Scheme.{u}} [IsIntegral S]
    (f : S ⟶ Spec (CommRingCat.of k)) [hSmooth : IsSmoothOfRelativeDimension 2 f]
    (π : S ⟶ X.toScheme) (hπ : π ≫ X.structureMorphism = f)
    (hbir : IsBirationalScheme π)

include hSmooth hπ hbir in
/-- The actual canonical Weil divisor is represented near the original regular
closed point by a genuine canonical Cartier module. No local representative,
normalization, numerator compatibility or target smoothness is assumed. -/
theorem exists_regular_closed_canonical_extension
    (KX : X.WeilDivisor) (hcanonical : IsCanonicalWeilDivisor X KX)
    (x : X.toScheme) (hclosed : IsClosed ({x} : Set X.toScheme))
    (hregular : RegularPoint X.toScheme x) :
    ∃ (W : X.toScheme.Opens) (hxW : x ∈ W), IsAffineOpen W ∧
      letI : Nonempty W := ⟨⟨x, hxW⟩⟩
      letI : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
      ∃ (DW : CartierDivisor W.toScheme)
        (eDW : cartierDivisorModule W.toScheme DW ≅
          relativeDifferentialExterior (W.ι ≫ X.structureMorphism) 2),
        (∀ C : X.PrimeCurve, C.genericPoint ∈ W → restrictedCoefficient W DW C = KX C) ∧
        ∀ (n : ℕ) (A : CartierDivisor X.toScheme), X.cartierToWeilHom A = n • KX →
          n • DW = cartierRestrictionHom W.ι A := by
  obtain ⟨U, hneU, hreference⟩ := hcanonical
  letI : Nonempty U.toScheme := hneU
  letI : Nonempty U := ⟨Classical.choice hneU⟩
  letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  obtain ⟨hsmoothU, hU, KU, ⟨eU⟩, hKX⟩ := hreference
  obtain ⟨W, hxW, hW, eW⟩ :=
    X.exists_regular_closed_native_canonical_frame f π hπ hbir x hclosed hregular
  letI : Nonempty W := ⟨⟨x, hxW⟩⟩
  letI : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  obtain ⟨eW⟩ := eW
  obtain ⟨DW, eDW, _, hcoeff, hmultiple⟩ :=
    CanonicalOpenNeighborhoodExtension.exists_canonical_representative X U W
      hU KU eU KX hKX eW
  exact ⟨W, hxW, hW, DW, eDW, hcoeff, hmultiple⟩

end KltDP.Geometry.NormalProjectiveSurface

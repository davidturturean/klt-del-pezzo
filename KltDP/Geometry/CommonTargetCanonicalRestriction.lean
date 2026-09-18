import KltDP.Geometry.CanonicalRationalCoordinateOpenPullback
import KltDP.Geometry.OpenCartierWeilNestedRestriction

/-!
# Normalized canonical restriction between original target opens

The maps are the original `homOfLE` maps. The signed Cartier pullback and
its canonical identification retain the original exterior differential and
rational-coordinate square. Restriction to a smaller big open preserves
the exact extended Weil divisor.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CommonTargetCanonical

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

local instance integralOpen (U : X.toScheme.Opens) [Nonempty U.toScheme] :
    IsIntegral U.toScheme := by
  letI : Nonempty U := ⟨Classical.choice (inferInstance : Nonempty U.toScheme)⟩
  exact isIntegral_of_isOpenImmersion U.ι

local instance openGeneric {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    (f : Y ⟶ Z) [IsOpenImmersion f] : GenericPointPreserving f :=
  ⟨genericPoint_eq_of_isOpenImmersion f⟩

/-- The same original structure morphism on the smaller open. -/
theorem restriction_structure (U V : X.toScheme.Opens) (hVU : V ≤ U) :
    X.toScheme.homOfLE hVU ≫ (U.ι ≫ X.structureMorphism) =
      V.ι ≫ X.structureMorphism := by
  rw [← Category.assoc, Scheme.homOfLE_ι]

section Restriction

variable (U V : X.toScheme.Opens) [Nonempty U.toScheme] [Nonempty V.toScheme]
    (hVU : V ≤ U)

/-- The normalized canonical identification of the actual signed restriction. -/
def canonicalRestrictionIso (D : CartierDivisor U.toScheme)
    (e : cartierDivisorModule U.toScheme D ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ X.structureMorphism) 2) :
    cartierDivisorModule V.toScheme
        (DominantCartierPullback.pullbackHom (X.toScheme.homOfLE hVU) D) ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (V.ι ≫ X.structureMorphism) 2 :=
  CartierRationalCoordinate.canonicalOpenPullbackIso (X.toScheme.homOfLE hVU)
    (U.ι ≫ X.structureMorphism) (V.ι ≫ X.structureMorphism)
    (restriction_structure X U V hVU) D e

/-- This restriction transports the original rational coordinate through
the original exterior differential, without a supplied comparison scalar. -/
theorem canonicalRestrictionIso_coordinate (D : CartierDivisor U.toScheme)
    (e : cartierDivisorModule U.toScheme D ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ X.structureMorphism) 2) :
    SchemeKaehlerExteriorPullbackTransport.map (U.ι ≫ X.structureMorphism)
        (X.toScheme.homOfLE hVU) (V.ι ≫ X.structureMorphism)
        (restriction_structure X U V hVU) 2 ≫
      CartierRationalCoordinate.coordinate V.toScheme
        (DominantCartierPullback.pullbackHom (X.toScheme.homOfLE hVU) D)
        (SmoothCanonicalExteriorComparison.relativeDifferentialExterior
          (V.ι ≫ X.structureMorphism) 2)
        (canonicalRestrictionIso X U V hVU D e) =
      (schemeModulePullback (X.toScheme.homOfLE hVU)).map
        (CartierRationalCoordinate.coordinate U.toScheme D
          (SmoothCanonicalExteriorComparison.relativeDifferentialExterior
            (U.ι ≫ X.structureMorphism) 2) e) ≫
        (OpenImmersionRational.rationalModulePullbackIso
          (X.toScheme.homOfLE hVU)).hom :=
  CartierRationalCoordinate.map_comp_coordinate_canonicalOpenPullbackIso
    (X.toScheme.homOfLE hVU) (U.ι ≫ X.structureMorphism)
    (V.ι ≫ X.structureMorphism) (restriction_structure X U V hVU) D e

/-- The actual signed restriction has the same extended Weil divisor. -/
theorem restrictedWeilHom_signedRestriction
    (hV : ∀ C : X.PrimeCurve, C.genericPoint ∈ V)
    (D : CartierDivisor U.toScheme) :
    OpenCartierWeil.restrictedWeilHom V
        (DominantCartierPullback.pullbackHom (X.toScheme.homOfLE hVU) D) =
      OpenCartierWeil.restrictedWeilHom U D := by
  rw [DominantCartierPullback.pullbackHom_eq_cartierRestrictionHom]
  exact OpenCartierWeil.restrictedWeilHom_nestedRestriction U V hVU hV D

end Restriction

/-- Every original prime generic point lies in the intersection. -/
theorem prime_genericPoint_mem_inf (U₁ U₂ : X.toScheme.Opens)
    (h₁ : ∀ C : X.PrimeCurve, C.genericPoint ∈ U₁)
    (h₂ : ∀ C : X.PrimeCurve, C.genericPoint ∈ U₂) (C : X.PrimeCurve) :
    C.genericPoint ∈ U₁ ⊓ U₂ :=
  ⟨h₁ C, h₂ C⟩

/-- Coverage derives nonemptiness of the actual intersection. -/
theorem inf_nonempty (U₁ U₂ : X.toScheme.Opens)
    (h₁ : ∀ C : X.PrimeCurve, C.genericPoint ∈ U₁)
    (h₂ : ∀ C : X.PrimeCurve, C.genericPoint ∈ U₂) :
    Nonempty (U₁ ⊓ U₂).toScheme :=
  OpenCartierWeil.nonempty_of_primeGenericPoint_mem (U₁ ⊓ U₂)
    (prime_genericPoint_mem_inf X U₁ U₂ h₁ h₂)

end KltDP.Geometry.CommonTargetCanonical

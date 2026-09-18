import KltDP.Geometry.CommonTargetCanonicalRestriction
import KltDP.Geometry.CanonicalCoordinateNormalization

/-!
# The actual normalization scalar for two original target big opens

Both given canonical identifications are restricted through their original
open maps with coordinate-normalized pullback. Equality of their extended
Weil divisors produces the actual coordinate multiplier on the intersection,
whose order vanishes on every original integral model at every DVR point.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CommonTargetCanonical

attribute [local instance] integralSchemeStalk_isDomain

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

local instance normalizationIntegralOpen (U : X.toScheme.Opens) [Nonempty U.toScheme] :
    IsIntegral U.toScheme := by
  letI : Nonempty U := ⟨Classical.choice (inferInstance : Nonempty U.toScheme)⟩
  exact isIntegral_of_isOpenImmersion U.ι

local instance normalizationOpenGeneric {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    (f : Y ⟶ Z) [IsOpenImmersion f] : GenericPointPreserving f :=
  ⟨genericPoint_eq_of_isOpenImmersion f⟩

variable (U₁ U₂ : X.toScheme.Opens) [Nonempty U₁.toScheme] [Nonempty U₂.toScheme]
    (h₁ : ∀ C : X.PrimeCurve, C.genericPoint ∈ U₁)
    (h₂ : ∀ C : X.PrimeCurve, C.genericPoint ∈ U₂)
    (D₁ : CartierDivisor U₁.toScheme) (D₂ : CartierDivisor U₂.toScheme)

/-- Equality of the original extensions persists under both original
signed restrictions to the intersection. -/
theorem restrictedWeilHom_inf_eq
    (hext : OpenCartierWeil.restrictedWeilHom U₁ D₁ =
      OpenCartierWeil.restrictedWeilHom U₂ D₂) :
    letI : Nonempty (U₁ ⊓ U₂).toScheme := inf_nonempty X U₁ U₂ h₁ h₂
    OpenCartierWeil.restrictedWeilHom (U₁ ⊓ U₂)
        (DominantCartierPullback.pullbackHom
          (X.toScheme.homOfLE (show U₁ ⊓ U₂ ≤ U₁ from inf_le_left)) D₁) =
      OpenCartierWeil.restrictedWeilHom (U₁ ⊓ U₂)
        (DominantCartierPullback.pullbackHom
          (X.toScheme.homOfLE (show U₁ ⊓ U₂ ≤ U₂ from inf_le_right)) D₂) := by
  letI : Nonempty (U₁ ⊓ U₂).toScheme := inf_nonempty X U₁ U₂ h₁ h₂
  have hU := prime_genericPoint_mem_inf X U₁ U₂ h₁ h₂
  exact (restrictedWeilHom_signedRestriction X U₁ (U₁ ⊓ U₂) inf_le_left hU D₁).trans
    (hext.trans (restrictedWeilHom_signedRestriction X U₂ (U₁ ⊓ U₂)
      inf_le_right hU D₂).symm)

section Scalar

-- The canonical identification is already compiled. Its construction need
-- not unfold while elaborating a generic coordinate-normalization theorem.
attribute [local irreducible] canonicalRestrictionIso

/-- The same scalar relates the normalized original canonical coordinates
and has zero order on every original integral model. -/
theorem exists_coordinate_scalar_order_zero_on_models [IsAlgClosed k]
    (e₁ : cartierDivisorModule U₁.toScheme D₁ ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U₁.ι ≫ X.structureMorphism) 2)
    (e₂ : cartierDivisorModule U₂.toScheme D₂ ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U₂.ι ≫ X.structureMorphism) 2)
    (hext : OpenCartierWeil.restrictedWeilHom U₁ D₁ =
      OpenCartierWeil.restrictedWeilHom U₂ D₂) :
    let U := U₁ ⊓ U₂
    letI : Nonempty U.toScheme := inf_nonempty X U₁ U₂ h₁ h₂
    let E₁ : CartierDivisor U.toScheme := DominantCartierPullback.pullbackHom
      (X.toScheme.homOfLE (show U ≤ U₁ from inf_le_left)) D₁
    let E₂ : CartierDivisor U.toScheme := DominantCartierPullback.pullbackHom
      (X.toScheme.homOfLE (show U ≤ U₂ from inf_le_right)) D₂
    let M : U.toScheme.Modules := SmoothCanonicalExteriorComparison.relativeDifferentialExterior
      (U.ι ≫ X.structureMorphism) 2
    let e₁' : cartierDivisorModule U.toScheme E₁ ≅ M :=
      canonicalRestrictionIso X U₁ U inf_le_left D₁ e₁
    let e₂' : cartierDivisorModule U.toScheme E₂ ≅ M :=
      canonicalRestrictionIso X U₂ U inf_le_right D₂ e₂
    ∃ q : U.toScheme.functionFieldˣ,
      E₁ - E₂ = principalCartierDivisorHom U.toScheme (Additive.ofMul q) ∧
      CartierRationalCoordinate.coordinate U.toScheme E₂ M e₂' =
        CartierRationalCoordinate.coordinate U.toScheme E₁ M e₁' ≫
          (rationalFunctionMulIso U.toScheme q).hom ∧
      ∀ (V : Scheme.{u}) [IsIntegral V] (v : V ⟶ X.toScheme)
        [GenericPointPreserving v] (x : V)
        [IsDiscreteValuationRing (V.presheaf.stalk x)],
        stalkDivisorOrder V x
          (Units.map (functionFieldMap v).hom.toMonoidHom
            (OpenCartierWeil.transportUnit U q)) = 0 := by
  let U := U₁ ⊓ U₂
  letI : Nonempty U.toScheme := inf_nonempty X U₁ U₂ h₁ h₂
  let E₁ : CartierDivisor U.toScheme := DominantCartierPullback.pullbackHom
    (X.toScheme.homOfLE (show U ≤ U₁ from inf_le_left)) D₁
  let E₂ : CartierDivisor U.toScheme := DominantCartierPullback.pullbackHom
    (X.toScheme.homOfLE (show U ≤ U₂ from inf_le_right)) D₂
  let M : U.toScheme.Modules := SmoothCanonicalExteriorComparison.relativeDifferentialExterior
    (U.ι ≫ X.structureMorphism) 2
  let e₁' : cartierDivisorModule U.toScheme E₁ ≅ M :=
    canonicalRestrictionIso X U₁ U inf_le_left D₁ e₁
  let e₂' : cartierDivisorModule U.toScheme E₂ ≅ M :=
    canonicalRestrictionIso X U₂ U inf_le_right D₂ e₂
  have hE : OpenCartierWeil.restrictedWeilHom U E₁ =
      OpenCartierWeil.restrictedWeilHom U E₂ :=
    restrictedWeilHom_inf_eq X U₁ U₂ h₁ h₂ D₁ D₂ hext
  exact CanonicalNormalization.exists_coordinate_scalar_order_zero_on_models X U
    (prime_genericPoint_mem_inf X U₁ U₂ h₁ h₂) E₁ E₂ M e₁' e₂' hE

end Scalar

end KltDP.Geometry.CommonTargetCanonical

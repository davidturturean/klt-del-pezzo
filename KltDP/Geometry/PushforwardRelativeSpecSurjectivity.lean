import KltDP.Geometry.PushforwardRelativeSpecConstruction
import KltDP.Geometry.AffineSteinFactor

/-!
Surjectivity of the canonical map to the actual pushforward relative
spectrum. Each target point lies in an original affine section-ring
chart. Properness of the original restricted morphism gives surjectivity
of that chart's original affinization; the compiled chart triangle then
lifts the point through the original global map. No Noetherian,
integrality, normality, field or nonempty hypothesis is required.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PushforwardRelativeSpec

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]

/-- Properness of the original restriction makes its original open
affinization surjective onto the original section-ring spectrum. -/
theorem sourceOpen_toSpecΓ_surjective (U : Y.AffineZariskiSite) :
    Surjective (f ⁻¹ᵁ U.1).toSpecΓ := by
  letI : IsProper (f ∣_ U.1) :=
    IsLocalAtTarget.restrict (P := @IsProper) inferInstance U.1
  let g : (f ⁻¹ᵁ U.1).toScheme ⟶ Spec Γ(Y, U.1) :=
    (f ∣_ U.1) ≫ U.2.isoSpec.hom
  letI : IsProper g := by
    dsimp [g]
    infer_instance
  letI : Surjective (f ⁻¹ᵁ U.1).toScheme.toSpecΓ :=
    ProperAffineSections.toSpecΓ_surjective g
  dsimp only [Scheme.Opens.toSpecΓ]
  infer_instance

/-- Every point of the actual relative spectrum has an original source
preimage. The proof uses the constructed chart cover and exact source triangle. -/
theorem fromSource_surjective : Surjective (fromSource f) := by
  constructor
  intro y
  obtain ⟨U, z, hz⟩ := (datum f).cover.exists_eq y
  change (chart f U).base z = y at hz
  obtain ⟨x, hx⟩ := (sourceOpen_toSpecΓ_surjective f U).surj z
  refine ⟨(f ⁻¹ᵁ U.1).ι.base x, ?_⟩
  calc
    (fromSource f).base ((f ⁻¹ᵁ U.1).ι.base x) =
        (chart f U).base ((f ⁻¹ᵁ U.1).toSpecΓ.base x) :=
      congrArg (fun a : (f ⁻¹ᵁ U.1).toScheme ⟶ relativeSpec f => a.base x)
        (source_ι_fromSource f U)
    _ = (chart f U).base z := congrArg (chart f U).base hx
    _ = y := hz

end KltDP.Geometry.PushforwardRelativeSpec

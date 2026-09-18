import KltDP.Geometry.CanonicalPrincipalShiftOpenCoordinate
import KltDP.Geometry.CartierRationalCoordinateEquality
import KltDP.Geometry.CartierCoordinateMultiplierComparison

/-!
# Extending the original canonical coordinate to a framed neighborhood

On the actual nonempty overlap, the multiplier of the two given module
identifications determines a rational function. Transport that same scalar
to the framed neighborhood and use the original principal-shift map. The
corrected coordinate agrees with the old reference, so the actual Cartier
divisors agree on the overlap. There is no compatibility or smoothness premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CanonicalPrincipalNeighborhoodExtension

open CartierRationalCoordinate DominantCartierPullback OpenImmersionRational
open SmoothCanonicalExteriorComparison

attribute [local irreducible] canonicalOpenPullbackIso

variable {k : Type u} [CommRing k]
    {W U V : Scheme.{u}} [IsIntegral W] [IsIntegral U] [IsIntegral V]
    (i : V ⟶ W) [IsOpenImmersion i] (j : V ⟶ U) [IsOpenImmersion j]
    (σW : W ⟶ Spec (CommRingCat.of k))
    (σU : U ⟶ Spec (CommRingCat.of k))
    (σV : V ⟶ Spec (CommRingCat.of k))
    (hi : i ≫ σW = σV) (hj : j ≫ σU = σV)

local instance : GenericPointPreserving i := ⟨genericPoint_eq_of_isOpenImmersion i⟩
local instance : GenericPointPreserving j := ⟨genericPoint_eq_of_isOpenImmersion j⟩

/-- A genuine frame on W extends the given canonical coordinate from its
actual overlap with U by a determined principal Cartier correction. -/
theorem exists_principal_normalization
    (eW : cartierDivisorModule W 0 ≅ relativeDifferentialExterior σW 2)
    (KU : CartierDivisor U)
    (eU : cartierDivisorModule U KU ≅ relativeDifferentialExterior σU 2) :
    ∃ qW : W.functionFieldˣ,
      let DW := rescaleDivisor W 0 qW
      let eDW := rescaleIso W 0 (relativeDifferentialExterior σW 2) eW qW
      coordinate V (pullbackHom i DW) (relativeDifferentialExterior σV 2)
          (canonicalOpenPullbackIso i σW σV hi DW eDW) =
        coordinate V (pullbackHom j KU) (relativeDifferentialExterior σV 2)
          (canonicalOpenPullbackIso j σU σV hj KU eU) ∧
      pullbackHom i DW = pullbackHom j KU := by
  let D := pullbackHom i (0 : CartierDivisor W)
  let E := pullbackHom j KU
  let M := relativeDifferentialExterior σV 2
  let eD : cartierDivisorModule V D ≅ M := canonicalOpenPullbackIso i σW σV hi 0 eW
  let eE : cartierDivisorModule V E ≅ M := canonicalOpenPullbackIso j σU σV hj KU eU
  obtain ⟨q, _, hinc⟩ := CartierModuleIsoMultiplier.exists_multiplier V D E (eD ≪≫ eE.symm)
  let qW : W.functionFieldˣ := Units.map (functionFieldIso i).inv.hom.toMonoidHom q
  have hqW : Units.map (functionFieldIso i).hom.hom.toMonoidHom qW = q := by
    apply Units.ext
    exact Iso.inv_hom_id_apply (functionFieldIso i) (q : V.functionField)
  let DW := rescaleDivisor W 0 qW
  let eDW := rescaleIso W 0 (relativeDifferentialExterior σW 2) eW qW
  have hcoordinate :
      coordinate V (pullbackHom i DW) M (canonicalOpenPullbackIso i σW σV hi DW eDW) =
        coordinate V E M eE := by
    calc
      _ = coordinate V D M eD ≫
          (rationalFunctionMulIso V
            (Units.map (functionFieldIso i).hom.hom.toMonoidHom qW)).hom :=
        coordinate_rescaleIso_openPullback i σW σV hi 0 eW qW
      _ = coordinate V D M eD ≫ (rationalFunctionMulIso V q).hom := by rw [hqW]
      _ = coordinate V E M eE :=
        (coordinate_eq_mul_of_inclusion V D E M eD eE q hinc).symm
  refine ⟨qW, hcoordinate, ?_⟩
  exact divisor_eq_of_coordinate_eq V (pullbackHom i DW) E M
    (canonicalOpenPullbackIso i σW σV hi DW eDW) eE hcoordinate

end KltDP.Geometry.CanonicalPrincipalNeighborhoodExtension

import KltDP.Geometry.RationalModuleOpenRestrictionFaithful
import KltDP.Geometry.CartierModuleIsoMultiplier
import KltDP.Geometry.CartierCoordinateMultiplierComparison
import KltDP.Geometry.CanonicalRationalCoordinateOpenPullback

/-!
# The original rational coordinate determines the actual Cartier divisor

The scalar of the given two Cartier-module identifications acts on the
original equation frame. Equal coordinates force this same scalar to be
one. Its proved principal divisor is therefore zero. Open restriction can
be used for the coordinate comparison without changing this conclusion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.CartierRationalCoordinate

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X] (D E : CartierDivisor X)
    (M : X.Modules) (eD : cartierDivisorModule X D ≅ M)
    (eE : cartierDivisorModule X E ≅ M)

/-- The actual common rational coordinate determines the actual Cartier
representative, using the multiplier of these same module identifications. -/
theorem divisor_eq_of_coordinate_eq
    (h : coordinate X D M eD = coordinate X E M eE) : D = E := by
  obtain ⟨q, hdiv, hinc⟩ :=
    CartierModuleIsoMultiplier.exists_multiplier X D E (eD ≪≫ eE.symm)
  obtain ⟨f, U, hxU, hf⟩ := exists_cartierOrderEquation X D (genericPoint X)
  letI : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  let c : CartierEquationChart X D := {
    openSet := U
    nonempty := inferInstance
    equation := f
    represents := hf }
  have hvalue := congrArg (fun γ : M ⟶ rationalFunctionModule X =>
    rationalFunctionModuleSectionsEquiv X c.openSet
      (γ.val.app (op c.openSet) (frame X D M eD c))) h
  have hmul : (q : X.functionField) * (↑(c.equation⁻¹) : X.functionField) =
      1 * (↑(c.equation⁻¹) : X.functionField) := by
    calc
      _ = rationalFunctionModuleSectionsEquiv X c.openSet
          ((coordinate X E M eE).val.app (op c.openSet) (frame X D M eD c)) :=
        (coordinate_frame_value_eq_mul_of_inclusion X D E M eD eE q hinc c).symm
      _ = rationalFunctionModuleSectionsEquiv X c.openSet
          ((coordinate X D M eD).val.app (op c.openSet) (frame X D M eD c)) :=
        hvalue.symm
      _ = (↑(c.equation⁻¹) : X.functionField) := coordinate_frame_value X D M eD c
      _ = _ := (one_mul _).symm
  have hq : q = 1 := Units.ext (mul_right_cancel₀ (Units.ne_zero (c.equation⁻¹)) hmul)
  apply sub_eq_zero.mp
  calc
    D - E = principalCartierDivisorHom X (Additive.ofMul q) := hdiv
    _ = 0 := by rw [hq]; exact map_zero _

section OpenCanonical

variable {X} {Y : Scheme.{u}} [IsIntegral Y] (j : Y ⟶ X) [IsOpenImmersion j]
    {k : Type u} [CommRing k]
    (σX : X ⟶ Spec (CommRingCat.of k)) (σY : Y ⟶ Spec (CommRingCat.of k))
    (hσ : j ≫ σX = σY)

local instance : GenericPointPreserving j := ⟨genericPoint_eq_of_isOpenImmersion j⟩

/-- Equal normalized canonical coordinates on an actual nonempty open
already identify the original Cartier divisors on the whole neighborhood. -/
theorem divisor_eq_of_canonicalOpenPullback_coordinate_eq
    (eD : cartierDivisorModule X D ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior σX 2)
    (eE : cartierDivisorModule X E ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior σX 2)
    (h : coordinate Y (DominantCartierPullback.pullbackHom j D)
        (SmoothCanonicalExteriorComparison.relativeDifferentialExterior σY 2)
        (canonicalOpenPullbackIso j σX σY hσ D eD) =
      coordinate Y (DominantCartierPullback.pullbackHom j E)
        (SmoothCanonicalExteriorComparison.relativeDifferentialExterior σY 2)
        (canonicalOpenPullbackIso j σX σY hσ E eE)) : D = E := by
  apply divisor_eq_of_coordinate_eq X D E _ eD eE
  apply OpenImmersionRational.hom_eq_of_openPullback_eq j
  apply (cancel_mono (OpenImmersionRational.rationalModulePullbackIso j).hom).mp
  exact (map_comp_coordinate_canonicalOpenPullbackIso j σX σY hσ D eD).symm.trans
    ((congrArg (fun γ => SchemeKaehlerExteriorPullbackTransport.map
      σX j σY hσ 2 ≫ γ) h).trans
      (map_comp_coordinate_canonicalOpenPullbackIso j σX σY hσ E eE))

end OpenCanonical

end KltDP.Geometry.CartierRationalCoordinate

#check @KltDP.Geometry.CartierRationalCoordinate.divisor_eq_of_coordinate_eq
#check @KltDP.Geometry.CartierRationalCoordinate.divisor_eq_of_canonicalOpenPullback_coordinate_eq
#print axioms KltDP.Geometry.CartierRationalCoordinate.divisor_eq_of_canonicalOpenPullback_coordinate_eq

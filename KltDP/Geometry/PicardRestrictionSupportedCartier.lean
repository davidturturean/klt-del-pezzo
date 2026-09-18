import KltDP.Geometry.PrimeCurveComplementPicardKernel

/-!
# An actual Cartier representative supported outside a nonempty open

This is the representative-producing part of the existing single-prime
restriction-kernel proof. The actual restricted principal function is
transported back through the original open immersion and subtracted.
The resulting Cartier divisor represents the original Picard class and
has zero Weil coefficient at each prime meeting the open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PicardRestrictionSupportedCartier

open KltDP.Geometry.OpenImmersionRational KltDP.Geometry.OpenCartierWeil
open KltDP.Geometry.PrimeCurveComplementKernel

variable {k : Type u} [Field k] [IsAlgClosed k] {X : NormalProjectiveSurface k}
    [∀ y : X.toScheme, UniqueFactorizationMonoid (X.stalk y)]
    (V : X.toScheme.Opens) [Nonempty V.toScheme]

local instance openIntegral : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι

/-- A class trivial on the original open has an actual supported Cartier representative. -/
theorem exists_supported_cartier (c : X.toScheme.Pic)
    (hc : schemePicardPullbackHom V.ι c = 1) :
    ∃ D : CartierDivisor X.toScheme,
      cartierPicardHom X.toScheme D = Additive.ofMul c ∧
      ∀ C : X.PrimeCurve, C.genericPoint ∈ V → X.cartierToWeilHom D C = 0 := by
  obtain ⟨D, rfl⟩ := cartierPicardClass_surjective X.toScheme c
  rw [schemePicardPullbackHom_cartierPicardClass] at hc
  obtain ⟨g', hg'⟩ := (cartierPicardClass_eq_one_iff V.toScheme _).mp hc
  let g : X.toScheme.functionFieldˣ := transportUnit V g'
  let D₀ : CartierDivisor X.toScheme :=
    D - principalCartierDivisorHom X.toScheme (Additive.ofMul g)
  have hrestr : cartierRestrictionHom V.ι D₀ = 0 := by
    dsimp only [D₀, g]
    rw [map_sub, cartierRestrictionHom_principal, transportUnit_hom, hg', sub_self]
  refine ⟨D₀, ?_, ?_⟩
  · change cartierPicardHom X.toScheme D₀ = cartierPicardHom X.toScheme D
    dsimp only [D₀]
    rw [map_sub, cartierPicardHom_principal, sub_zero]
  · intro C hC
    have hcoeff := restrictedCoefficient_cartierRestriction V D₀ C hC
    rw [hrestr, restrictedCoefficient_zero] at hcoeff
    exact hcoeff.symm

end KltDP.Geometry.PicardRestrictionSupportedCartier

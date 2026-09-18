import KltDP.Geometry.NormalModelLocalFrameConstructor
import KltDP.Geometry.CanonicalRationalCoordinateOpenPullback

/-!
# Restricting an actual local canonical frame through its original point

Use the original normalized canonical open pullback and the original local
equation constructor. The actual model point is unchanged and its actual
Cartier order is preserved by the original open-immersion stalk map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalModelCanonical.LocalFrame

open CartierRationalCoordinate DominantCartierPullback OpenImmersionRational

attribute [local instance] integralSchemeStalk_isDomain

local instance openGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : A ⟶ B) [IsOpenImmersion i] : GenericPointPreserving i :=
  ⟨genericPoint_eq_of_isOpenImmersion i⟩

variable {k : Type u} [Field k] {V : Scheme.{u}} [IsIntegral V]
    {σ : V ⟶ Spec (CommRingCat.of k)} {x : V} (F : LocalFrame σ x)
    (Z : F.neighborhood.Opens) (hZ : F.point ∈ Z)

/-- Restriction uses the same original model map, the same original point,
and the actual differential-normalized Cartier pullback. -/
def restrict : LocalFrame σ x := by
  letI : Nonempty Z.toScheme := ⟨⟨F.point, hZ⟩⟩
  letI : IsIntegral Z.toScheme := isIntegral_of_isOpenImmersion Z.ι
  letI : IsSmoothOfRelativeDimension 2 ((Z.ι ≫ F.toModel) ≫ σ) := by
    rw [Category.assoc]
    exact IsLocalAtSource.comp (P := @IsSmoothOfRelativeDimension 2) F.smooth Z.ι
  exact ofCanonicalDivisor σ (Z.ι ≫ F.toModel) ⟨F.point, hZ⟩ x
    (by simpa only [Scheme.comp_base_apply] using F.point_eq)
    (pullbackHom Z.ι F.divisor)
    (canonicalOpenPullbackIso Z.ι (F.toModel ≫ σ) ((Z.ι ≫ F.toModel) ≫ σ)
      (Category.assoc Z.ι F.toModel σ).symm F.divisor F.canonicalIso)

/-- The restricted frame retains the original integer order at the original
model point, through the original open-immersion order comparison. -/
theorem restrict_order [IsDiscreteValuationRing (V.presheaf.stalk x)] :
    (F.restrict Z hZ).order = F.order := by
  letI : Nonempty Z.toScheme := ⟨⟨F.point, hZ⟩⟩
  letI : IsIntegral Z.toScheme := isIntegral_of_isOpenImmersion Z.ι
  letI : IsDiscreteValuationRing (Z.toScheme.presheaf.stalk ⟨F.point, hZ⟩) :=
    stalk_isDiscreteValuationRing_of_isOpenImmersion Z.ι ⟨F.point, hZ⟩ F.point rfl
  calc
    _ = cartierOrderAt Z.toScheme (pullbackHom Z.ι F.divisor) ⟨F.point, hZ⟩ :=
      order_eq_cartierOrderAt (F.restrict Z hZ)
    _ = cartierOrderAt F.neighborhood F.divisor F.point := by
      rw [pullbackHom_eq_cartierRestrictionHom]
      exact cartierOrderAt_cartierRestrictionHom Z.ι F.divisor ⟨F.point, hZ⟩ F.point rfl
    _ = F.order := (order_eq_cartierOrderAt F).symm

end KltDP.Geometry.NormalModelCanonical.LocalFrame

#check @KltDP.Geometry.NormalModelCanonical.LocalFrame.restrict
#check @KltDP.Geometry.NormalModelCanonical.LocalFrame.restrict_order
#print axioms KltDP.Geometry.NormalModelCanonical.LocalFrame.restrict_order

import KltDP.Geometry.NormalModelCanonicalFrameOrder

/-!
# Actual local canonical frames from a given canonical Cartier identification

An actual smooth open immersion and a Cartier identification with its
original top differential sheaf produce a local frame through the given
point. The Cartier equation and chart are obtained from the proved local
equation theorem. The resulting frame order is the original Cartier order;
no chart or order-comparison witness is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalModelCanonical.LocalFrame

attribute [local instance] integralSchemeStalk_isDomain

variable {k : Type u} [Field k] {V W : Scheme.{u}}
    [IsIntegral V] [IsIntegral W]
    (σ : V ⟶ Spec (CommRingCat.of k)) (i : W ⟶ V) [IsOpenImmersion i]
    [IsSmoothOfRelativeDimension 2 (i ≫ σ)]
    (w : W) (x : V) (hw : i.base w = x)
    (D : CartierDivisor W)
    (eD : cartierDivisorModule W D ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior (i ≫ σ) 2)

/-- The original local equation theorem supplies the equation chart. -/
def ofCanonicalDivisor : LocalFrame σ x := by
  let hs := cartierOrderEquation_spec W D w
  let U := hs.choose
  let hwU : w ∈ U := hs.choose_spec.choose
  letI : Nonempty U := ⟨⟨w, hwU⟩⟩
  exact {
    neighborhood := W
    toModel := i
    isOpenImmersion := inferInstance
    point := w
    point_eq := hw
    smooth := inferInstance
    divisor := D
    canonicalIso := eD
    equationChart := {
      openSet := U
      nonempty := inferInstance
      equation := cartierOrderEquation W D w
      represents := hs.choose_spec.choose_spec }
    point_mem_equation := hwU }

/-- The constructed frame retains the given divisor's original local order. -/
theorem ofCanonicalDivisor_order
    [IsDiscreteValuationRing (V.presheaf.stalk x)] :
    letI := OpenImmersionRational.stalk_isDiscreteValuationRing_of_isOpenImmersion i w x hw
    (ofCanonicalDivisor σ i w x hw D eD).order = cartierOrderAt W D w := by
  letI := OpenImmersionRational.stalk_isDiscreteValuationRing_of_isOpenImmersion i w x hw
  exact order_eq_cartierOrderAt (ofCanonicalDivisor σ i w x hw D eD)

end KltDP.Geometry.NormalModelCanonical.LocalFrame

#check @KltDP.Geometry.NormalModelCanonical.LocalFrame.ofCanonicalDivisor
#print axioms KltDP.Geometry.NormalModelCanonical.LocalFrame.ofCanonicalDivisor_order

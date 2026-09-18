import KltDP.Geometry.PointBlowupCartierBranchCoefficient
import KltDP.Geometry.DominantCartierPullbackOffSupport

/-!
# Actual exceptional coefficient at a two-branch crossing

The original Cartier germ is a unit times the two genuine original
parameters. Their images under the original projection are the already
proved exceptional uniformizers. The actual rational equation is their
product times the mapped stalk unit, so its actual Weil coefficient is two.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

private theorem cartier_pullback_coefficient_of_two_irreducible_germs
    {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [GenericPointPreserving π]
    (D : CartierDivisor X.toScheme) (c : RegularCartierEquationChart X.toScheme D)
    (C : S.PrimeCurve) (hx : π.base C.genericPoint ∈ c.chart.openSet)
    (g h : X.stalk (π.base C.genericPoint))
    (u : (X.stalk (π.base C.genericPoint))ˣ)
    (hc : X.toScheme.presheaf.germ c.chart.openSet
      (π.base C.genericPoint) hx c.coefficient = (u : X.stalk (π.base C.genericPoint)) * (g * h))
    (hg : Irreducible (π.stalkMap C.genericPoint g))
    (hh : Irreducible (π.stalkMap C.genericPoint h)) :
    S.cartierToWeilHom (DominantCartierPullback.pullbackHom π D) C = 2 := by
  let v : (S.stalk C.genericPoint)ˣ :=
    Units.map (π.stalkMap C.genericPoint).hom.toMonoidHom u
  let fg := RingTheory.fractionFieldUnit (S.stalk C.genericPoint) S.toScheme.functionField
    (π.stalkMap C.genericPoint g) hg.ne_zero
  let fh := RingTheory.fractionFieldUnit (S.stalk C.genericPoint) S.toScheme.functionField
    (π.stalkMap C.genericPoint h) hh.ne_zero
  have hregular : algebraMap (X.stalk (π.base C.genericPoint)) X.toScheme.functionField
      (X.toScheme.presheaf.germ c.chart.openSet (π.base C.genericPoint) hx c.coefficient) =
      (c.chart.equation : X.toScheme.functionField) := by
    change X.toScheme.presheaf.stalkSpecializes
        ((genericPoint_spec X.toScheme).specializes trivial)
        (X.toScheme.presheaf.germ c.chart.openSet (π.base C.genericPoint) hx c.coefficient) = _
    exact (ConcreteCategory.congr_hom
      (X.toScheme.presheaf.germ_stalkSpecializes hx
        ((genericPoint_spec X.toScheme).specializes trivial)) c.coefficient).trans c.germ_eq
  have hmap : Units.map (functionFieldMap π).hom.toMonoidHom c.chart.equation =
      Units.map (algebraMap (S.stalk C.genericPoint) S.toScheme.functionField) v * (fg * fh) := by
    apply Units.ext
    change functionFieldMap π (c.chart.equation : X.toScheme.functionField) =
      algebraMap (S.stalk C.genericPoint) S.toScheme.functionField
          (π.stalkMap C.genericPoint (u : X.stalk (π.base C.genericPoint))) *
        (algebraMap (S.stalk C.genericPoint) S.toScheme.functionField
            (π.stalkMap C.genericPoint g) *
          algebraMap (S.stalk C.genericPoint) S.toScheme.functionField
            (π.stalkMap C.genericPoint h))
    calc
      _ = functionFieldMap π (algebraMap (X.stalk (π.base C.genericPoint))
          X.toScheme.functionField (X.toScheme.presheaf.germ c.chart.openSet
            (π.base C.genericPoint) hx c.coefficient)) :=
        congrArg (functionFieldMap π) hregular.symm
      _ = algebraMap (S.stalk C.genericPoint) S.toScheme.functionField
          (π.stalkMap C.genericPoint (X.toScheme.presheaf.germ c.chart.openSet
            (π.base C.genericPoint) hx c.coefficient)) :=
        functionFieldMap_stalk_algebraMap π C.genericPoint _
      _ = algebraMap (S.stalk C.genericPoint) S.toScheme.functionField
          (π.stalkMap C.genericPoint ((u : X.stalk (π.base C.genericPoint)) * (g * h))) :=
        congrArg (fun z : X.stalk (π.base C.genericPoint) =>
          algebraMap (S.stalk C.genericPoint) S.toScheme.functionField
            (π.stalkMap C.genericPoint z)) hc
      _ = _ := by simp only [map_mul]
  letI : IsDiscreteValuationRing (S.stalk C.genericPoint) := C.genericPoint_isDiscreteValuationRing
  have hgorder : C.order fg = 1 := by
    rw [C.order_eq_stalkDivisorOrder]
    exact stalkDivisorOrder_uniformizer S.toScheme C.genericPoint (π.stalkMap C.genericPoint g) hg
  have hhorder : C.order fh = 1 := by
    rw [C.order_eq_stalkDivisorOrder]
    exact stalkDivisorOrder_uniformizer S.toScheme C.genericPoint (π.stalkMap C.genericPoint h) hh
  letI : Nonempty (π ⁻¹ᵁ c.chart.openSet) := ⟨⟨C.genericPoint, hx⟩⟩
  calc
    S.cartierToWeilHom (DominantCartierPullback.pullbackHom π D) C =
        C.order (Units.map (functionFieldMap π).hom.toMonoidHom c.chart.equation) :=
      S.cartierToWeilHom_apply_of_equation (DominantCartierPullback.pullbackHom π D) C
        (π ⁻¹ᵁ c.chart.openSet) hx _
        (DominantCartierPullback.pullbackHom_globalEquation_preimage π D c.chart.openSet
          c.chart.equation c.chart.represents)
    _ = 2 := by
      rw [hmap, C.order_mul, C.order_mul, C.order_map_local_unit, hgorder, hhorder]
      norm_num

namespace PointBlowupExceptionalPrimeStalk

open AffineBlowup AffineBlowupRegularPairChart PointBlowupGluing PointBlowupChartStalk

variable {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))
    (C : (sourceSurface X j q hclosed).PrimeCurve)
    (a b : q.asIdeal) (P : PrimeSpectrum (chartRing q.asIdeal a))
    (hC : (chartInclusion j q hclosed a).base P = C.genericPoint)
    (hcenter : (projection j q hclosed).base C.genericPoint = j.base q)
    (ha : (centerParameter q a : Localization.AtPrime q.asIdeal) ∈
      nonZeroDivisors (Localization.AtPrime q.asIdeal))
    (hb : Ideal.Quotient.mk
      (Ideal.span {(centerParameter q a : Localization.AtPrime q.asIdeal)})
      (centerParameter q b : Localization.AtPrime q.asIdeal) ∈ nonZeroDivisors
        (Localization.AtPrime q.asIdeal ⧸
          Ideal.span {(centerParameter q a : Localization.AtPrime q.asIdeal)}))
    (hI : centerIdeal q = Ideal.span
      {(centerParameter q a : Localization.AtPrime q.asIdeal),
        (centerParameter q b : Localization.AtPrime q.asIdeal)})

include hcenter ha hb hI in
/-- The original Cartier crossing has actual exceptional coefficient two;
both original parameter images are proved irreducible from the Rees maps. -/
theorem cartier_pullback_coefficient_of_crossing
    (D : CartierDivisor X.toScheme) (c : RegularCartierEquationChart X.toScheme D)
    (hx : (projection j q hclosed).base C.genericPoint ∈ c.chart.openSet)
    (u : (X.stalk ((projection j q hclosed).base C.genericPoint))ˣ)
    (hc : X.toScheme.presheaf.germ c.chart.openSet
      ((projection j q hclosed).base C.genericPoint) hx c.coefficient =
        (u : X.stalk ((projection j q hclosed).base C.genericPoint)) *
          (baseCoefficientGerm X j q hclosed C a P hC (a : R) *
            baseCoefficientGerm X j q hclosed C a P hC (b : R))) :
    let π : (sourceSurface X j q hclosed).toScheme ⟶ X.toScheme := projection j q hclosed
    letI : GenericPointPreserving π := projection_genericPointPreserving X j q hclosed
    (sourceSurface X j q hclosed).cartierToWeilHom
      (DominantCartierPullback.pullbackHom π D) C = 2 := by
  let π : (sourceSurface X j q hclosed).toScheme ⟶ X.toScheme := projection j q hclosed
  letI : GenericPointPreserving π := projection_genericPointPreserving X j q hclosed
  apply cartier_pullback_coefficient_of_two_irreducible_germs π D c C hx
    (baseCoefficientGerm X j q hclosed C a P hC (a : R))
    (baseCoefficientGerm X j q hclosed C a P hC (b : R)) u hc
  · exact pullback_firstParameter_irreducible X j q hclosed C a P hC hcenter
      (centerParameter q b) ha hb hI
  · letI : IsDomain (Localization.AtPrime q.asIdeal) := X.affineLocalization_isDomain j q
    letI : (centerIdeal q).IsPrime := by
      dsimp only [centerIdeal]
      rw [Localization.AtPrime.map_eq_maximalIdeal]
      infer_instance
    let e := exceptionalStalkEquiv X j q hclosed C a P hC hcenter (centerParameter q b) ha hb hI
    apply (MulEquiv.irreducible_iff e.toMulEquiv).mp
    have h := exceptionalStalkEquiv_pullback_baseCoefficientGerm
      X j q hclosed C a P hC hcenter (centerParameter q b) ha hb hI (b : R)
    exact Eq.mpr (congrArg Irreducible h)
      (exceptionalGeneric_second_irreducible (centerIdeal q) (centerParameter q a)
        (centerParameter q b) ha hb hI)

end PointBlowupExceptionalPrimeStalk
end KltDP.Geometry

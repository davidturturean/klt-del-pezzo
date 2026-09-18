import KltDP.Geometry.PointBlowupExceptionalPullbackParameter
import KltDP.Geometry.DominantCartierPullbackEquations
import KltDP.Geometry.FunctionFieldStalkMap
import KltDP.Geometry.CartierWeilMap

/-!
# Actual exceptional coefficient of the original pulled Cartier branch

For either genuine parameter of the original centre stalk, an original
Cartier equation equal to a unit times that parameter pulls back with
coefficient one at the original contracted prime. The source stalk
irreducibility is proved from the original Rees maps. The original
function-field square and Cartier equation map then compute the actual
Weil coefficient. No multiplicity or coefficient conclusion is supplied.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

private theorem cartier_pullback_coefficient_of_irreducible_germ
    {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [GenericPointPreserving π]
    (D : CartierDivisor X.toScheme) (c : RegularCartierEquationChart X.toScheme D)
    (C : S.PrimeCurve) (hx : π.base C.genericPoint ∈ c.chart.openSet)
    (hr : Irreducible (π.stalkMap C.genericPoint
      (X.toScheme.presheaf.germ c.chart.openSet (π.base C.genericPoint) hx c.coefficient))) :
    S.cartierToWeilHom (DominantCartierPullback.pullbackHom π D) C = 1 := by
  let g := X.toScheme.presheaf.germ c.chart.openSet (π.base C.genericPoint) hx c.coefficient
  have hregular : algebraMap (X.stalk (π.base C.genericPoint)) X.toScheme.functionField g =
      (c.chart.equation : X.toScheme.functionField) := by
    change X.toScheme.presheaf.stalkSpecializes
        ((genericPoint_spec X.toScheme).specializes trivial)
        (X.toScheme.presheaf.germ c.chart.openSet (π.base C.genericPoint) hx c.coefficient) = _
    exact (ConcreteCategory.congr_hom
      (X.toScheme.presheaf.germ_stalkSpecializes hx
        ((genericPoint_spec X.toScheme).specializes trivial)) c.coefficient).trans c.germ_eq
  have hmap : Units.map (functionFieldMap π).hom.toMonoidHom c.chart.equation =
      RingTheory.fractionFieldUnit (S.stalk C.genericPoint) S.toScheme.functionField
        (π.stalkMap C.genericPoint g) hr.ne_zero := by
    apply Units.ext
    change functionFieldMap π (c.chart.equation : X.toScheme.functionField) =
      algebraMap (S.stalk C.genericPoint) S.toScheme.functionField (π.stalkMap C.genericPoint g)
    rw [← functionFieldMap_stalk_algebraMap π C.genericPoint]
    exact congrArg (functionFieldMap π) hregular.symm
  letI : Nonempty (π ⁻¹ᵁ c.chart.openSet) := ⟨⟨C.genericPoint, hx⟩⟩
  letI : IsDiscreteValuationRing (S.stalk C.genericPoint) := C.genericPoint_isDiscreteValuationRing
  calc
    S.cartierToWeilHom (DominantCartierPullback.pullbackHom π D) C =
        C.order (Units.map (functionFieldMap π).hom.toMonoidHom c.chart.equation) :=
      S.cartierToWeilHom_apply_of_equation (DominantCartierPullback.pullbackHom π D) C
        (π ⁻¹ᵁ c.chart.openSet) hx _
        (DominantCartierPullback.pullbackHom_globalEquation_preimage π D c.chart.openSet
          c.chart.equation c.chart.represents)
    _ = 1 := by
      rw [hmap, C.order_eq_stalkDivisorOrder]
      exact stalkDivisorOrder_uniformizer S.toScheme C.genericPoint
        (π.stalkMap C.genericPoint g) hr

namespace PointBlowupExceptionalPrimeStalk

open AffineBlowup AffineBlowupRegularPairChart PointBlowupGluing PointBlowupChartStalk

variable {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))

/-- Generic-point preservation belongs to the original projection and
is derived from the already proved actual surface blowup geometry. -/
theorem projection_genericPointPreserving :
    GenericPointPreserving
      (show (sourceSurface X j q hclosed).toScheme ⟶ X.toScheme from projection j q hclosed) :=
  ⟨surface_projection_genericPoint X j q hclosed⟩

variable (C : (sourceSurface X j q hclosed).PrimeCurve)
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
/-- A unit times either original centre parameter has actual pulled
Weil coefficient one. Both parameters are genuine generators in the
original centre localization; the source irreducibility is derived. -/
theorem cartier_pullback_coefficient_of_branch
    (D : CartierDivisor X.toScheme) (c : RegularCartierEquationChart X.toScheme D)
    (hx : (projection j q hclosed).base C.genericPoint ∈ c.chart.openSet)
    (r : q.asIdeal) (hr : r = a ∨ r = b)
    (u : (X.stalk ((projection j q hclosed).base C.genericPoint))ˣ)
    (hc : X.toScheme.presheaf.germ c.chart.openSet
      ((projection j q hclosed).base C.genericPoint) hx c.coefficient =
        (u : X.stalk ((projection j q hclosed).base C.genericPoint)) *
          baseCoefficientGerm X j q hclosed C a P hC (r : R)) :
    let π : (sourceSurface X j q hclosed).toScheme ⟶ X.toScheme := projection j q hclosed
    letI : GenericPointPreserving π := projection_genericPointPreserving X j q hclosed
    (sourceSurface X j q hclosed).cartierToWeilHom
      (DominantCartierPullback.pullbackHom π D) C = 1 := by
  let π : (sourceSurface X j q hclosed).toScheme ⟶ X.toScheme := projection j q hclosed
  letI : GenericPointPreserving π := projection_genericPointPreserving X j q hclosed
  have hparam : Irreducible (π.stalkMap C.genericPoint
      (baseCoefficientGerm X j q hclosed C a P hC (r : R))) := by
    rcases hr with hra | hrb
    · have hpa := pullback_firstParameter_irreducible X j q hclosed C a P hC hcenter
        (centerParameter q b) ha hb hI
      exact Eq.mpr (congrArg (fun z : q.asIdeal => Irreducible
        (π.stalkMap C.genericPoint (baseCoefficientGerm X j q hclosed C a P hC (z : R))))
          hra) hpa
    · have hpb : Irreducible (π.stalkMap C.genericPoint
          (baseCoefficientGerm X j q hclosed C a P hC (b : R))) := by
        letI : IsDomain (Localization.AtPrime q.asIdeal) := X.affineLocalization_isDomain j q
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
      exact Eq.mpr (congrArg (fun z : q.asIdeal => Irreducible
        (π.stalkMap C.genericPoint (baseCoefficientGerm X j q hclosed C a P hC (z : R))))
          hrb) hpb
  apply cartier_pullback_coefficient_of_irreducible_germ π D c C hx
  have hceq := congrArg
    (fun z : X.stalk ((projection j q hclosed).base C.genericPoint) =>
      π.stalkMap C.genericPoint z) hc
  have hceq' : π.stalkMap C.genericPoint
      (X.toScheme.presheaf.germ c.chart.openSet
        ((projection j q hclosed).base C.genericPoint) hx c.coefficient) =
      π.stalkMap C.genericPoint
          (u : X.stalk ((projection j q hclosed).base C.genericPoint)) *
        π.stalkMap C.genericPoint (baseCoefficientGerm X j q hclosed C a P hC (r : R)) :=
    hceq.trans ((π.stalkMap C.genericPoint).hom.map_mul _ _)
  exact Eq.mpr (congrArg Irreducible hceq')
    ((irreducible_isUnit_mul (u.isUnit.map (π.stalkMap C.genericPoint).hom)).mpr hparam)

end PointBlowupExceptionalPrimeStalk

end KltDP.Geometry

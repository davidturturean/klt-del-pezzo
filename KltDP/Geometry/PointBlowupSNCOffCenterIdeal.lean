import KltDP.Geometry.PointBlowupTotalBoundaryStalkIdeal
import KltDP.Geometry.PointBlowupCanonicalDivisor
import KltDP.Geometry.RationalTreePicardRestrictStalk
import KltDP.Geometry.StrictNormalCrossingsReducedEquation
import KltDP.Geometry.StrictNormalCrossingsCartierIdealData
import KltDP.Geometry.AffineIdealGermRadical

/-!
# The actual reduced total boundary off the blowup centre

The original projection is an isomorphism over the original puncture.
Its literal stalk map therefore transports the source SNC equation.
The actual centre-fibre ideal is the unit ideal on an affine neighborhood,
and reduction preserves the transported SNC principal ideal.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PointBlowupSNCBoundary

open PointBlowupGluing PointBlowupChartStalk
open PointBlowupExceptionalPrimeStalk (sourceSurface)

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
variable (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
variable (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
variable (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
variable (hclosed : IsClosed ({j.base q} : Set X.toScheme))

local instance : IsLocallyNoetherian X.toScheme := X.isLocallyNoetherian
local instance : IsIntegral (PointBlowupGluing.scheme j q hclosed) :=
  (sourceSurface X j q hclosed).integral
local instance : GenericPointPreserving (projection j q hclosed) :=
  ⟨(PointBlowupCanonicalCartier.isBirational_projection X j q hclosed).map_genericPoint⟩

/-- Every point off the original centre has an SNC generator for the
original reduced total-boundary ideal on an actual affine neighborhood. -/
theorem reduced_total_ideal_snc_off_center (D : CartierDivisor X.toScheme)
    (hD : IsStrictNormalCrossingsCartier X.toScheme D)
    (y : PointBlowupGluing.scheme j q hclosed)
    (hy : (projection j q hclosed).base y ≠ j.base q) :
    ∃ (U : (PointBlowupGluing.scheme j q hclosed).affineOpens) (hyU : y ∈ U.1)
      (t : (PointBlowupGluing.scheme j q hclosed).presheaf.stalk y),
      Ideal.map ((PointBlowupGluing.scheme j q hclosed).presheaf.germ U.1 y hyU).hom
        ((regularTotalBoundaryIdeal j q hclosed D hD.1).radical.ideal U) = Ideal.span {t} ∧
      IsStrictNormalCrossingsEquation _ t := by
  let π := projection j q hclosed
  have hyopen : y ∈ exceptionalComplementOpen j q hclosed := hy
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWle⟩ :=
    (isBasis_affine_open (scheme j q hclosed)).exists_subset_of_mem_open hyopen
      (exceptionalComplementOpen j q hclosed).2
  let U : (scheme j q hclosed).affineOpens := ⟨W, hW⟩
  have hdisj : ∀ z, (globalCenterFiberι j q hclosed).base z ∉ W := by
    intro z hz
    have hne : π.base ((globalCenterFiberι j q hclosed).base z) ≠ j.base q := hWle hz
    apply hne
    have hr : (globalCenterFiberι j q hclosed).base z ∈
        Set.range (globalCenterFiberι j q hclosed).base := ⟨z, rfl⟩
    rw [range_globalCenterFiberι] at hr
    exact hr
  have hkernel : (globalCenterFiberι j q hclosed).ker.ideal U = ⊤ :=
    ker_ideal_eq_top_of_disjoint _ U hdisj
  letI : IsIso (π ∣_ puncture j q hclosed) :=
    projection_restrict_puncture_isIso j q hclosed
  letI : IsIso (π.stalkMap y) :=
    RationalTreePicard.isIso_stalkMap_of_isIso_restrict π (puncture j q hclosed) y hy
  let e := (asIso (π.stalkMap y)).commRingCatIsoToRingEquiv
  obtain ⟨c, hc⟩ := hD.1 (π.base y)
  let t : (scheme j q hclosed).presheaf.stalk y :=
    π.stalkMap y (X.toScheme.presheaf.germ c.chart.openSet (π.base y) hc c.coefficient)
  have hsnc : IsStrictNormalCrossingsEquation _ t :=
    (hD.2 c (π.base y) hc).map_equiv e
  have hideal : Ideal.map ((scheme j q hclosed).presheaf.germ U.1 y hyW).hom
      ((regularTotalBoundaryIdeal j q hclosed D hD.1).ideal U) = Ideal.span {t} := by
    rw [regularTotalBoundaryIdeal_ideal, hkernel, Ideal.mul_top]
    have h := regularCartierIdealData_map_germ_eq_span (scheme j q hclosed)
      (pullbackDivisor π D hD.1) (pullbackDivisor_hasRegularEquations π D hD.1)
      (pullbackDivisor_regularChart π D hD.1 c) U y hyW hc
    exact h.trans (congrArg (fun z : (scheme j q hclosed).presheaf.stalk y =>
      Ideal.span ({z} : Set _)) (Scheme.stalkMap_germ_apply π c.chart.openSet y hc c.coefficient).symm)
  refine ⟨U, hyW, t, ?_, hsnc⟩
  rw [Scheme.IdealSheafData.radical_ideal, affineIdeal_map_germ_radical, hideal]
  exact ((sourceSurface X j q hclosed).snc_equation_span_isRadical y hsnc).radical

end KltDP.Geometry.PointBlowupSNCBoundary

import KltDP.Examples.FrobeniusGlobalExceptionalSuccessor
import KltDP.Examples.ProjectiveProductOriginStalkRegular
import KltDP.Geometry.GluedSubschemeStalkKernel
import KltDP.Geometry.AffineBlowupCover
import KltDP.Geometry.AffineBlowupExceptionalIntersection
import KltDP.Geometry.PointBlowupExceptionalIdeal

/-!
# The crossing of the older exceptional curve with the newest one in the second Rees chart

BRIEF20 (lane F), for an arbitrary charted plane `A : PlaneChartedScheme k`. The second Rees chart
`secondChart A : Spec (reesVChartRing k) ⟶ A.next.carrier` of the blowup `A.next → A` (coordinates
`u/v = oldRatio`, `v = vEquation`) has the affine chart open `secondOpen A` with section ring
`secondSections A : Γ ≃+* reesVChartRing k`. On it

* the newest exceptional curve `P = previousFiberι A` has the principal kernel ideal `(v)`
  (`fiber_ideal_secondOpen`, the accepted pullback-square computation for an arbitrary `A`), and every
  chart point on `P` has `v` in its prime (`vEquation_mem_of_mem_fiber`); `P` lies in the affine
  blowup piece (`fiber_mem_range_affineBlowup`);
* for `A = B.next`, the strict transform `C = previousStrictι B` of the previous exceptional curve has the
  principal kernel ideal `(u/v)` (`strict_ideal_secondOpen`), and every chart point on `C` has `u/v` in
  its prime (`oldRatio_mem_of_mem_strict`);
* every point of `C ∩ P` lies in the chart (`mem_range_secondChart_of_mem`: `P` is in the affine blowup
  piece and `C` avoids the first Rees chart), hence is the origin `(u/v, v) = 0`
  (`eq_crossingPoint_of_mem`): **`C ∩ P` is the single point `(previousStrictι B).base (adjacentPoint B)`**
  (`strict_inter_fiber_subsingleton`, `adjacentPoint_eq`);
* the centre of the next blowup (the origin of the first Rees chart) is not in the second chart
  (`center_not_mem_range_secondChart`).

The local ring of the chart at its origin is `reesVChartRing k` localised at `(u/v, v)`, isomorphic to
`k[u][v]_{(u,v)}` (`originLocalEquiv`, through `vChartPolynomialEquiv`), hence regular of dimension two
(lane A1's `ProjectiveProductOriginStalkRegular`); the stalk of `A.next` at the crossing point inherits
this (`crossingStalk_regularLocal`, `crossingStalk_ringKrullDim`), and the germs `crossingU`, `crossingV`
of `u/v`, `v` generate its maximal ideal (`span_crossingU_crossingV`); they are the germs of the chart
sections `(secondSections A).symm oldRatio`, `(secondSections A).symm vEquation` (`crossingU_eq_germ`,
`crossingV_eq_germ`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing

universe u

namespace KltDP.Examples.FrobeniusSecondChartCrossing

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupChartIteration
open FrobeniusGlobalBlowupStages FrobeniusExceptionalSuccessorChart
  FrobeniusGlobalExceptionalSuccessor ProjectiveProductOriginStalkRegular
  FrobeniusExceptionalCharts

variable {k : Type u} [Field k]

local instance secondChartOriginPoint_isMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

local instance secondChartCenterIdeal_isMaximal : (centerIdeal (k := k)).IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-! ## The origin `(u/v, v) = 0` of the second chart and its local ring -/

/-- The ideal of the origin of the second Rees chart. -/
def originIdeal : Ideal (reesVChartRing k) := Ideal.span {oldRatio, vEquation}

theorem map_originIdeal :
    Ideal.map (vChartPolynomialEquiv (k := k)).toRingHom (originIdeal (k := k)) = centerIdeal := by
  rw [originIdeal, Ideal.map_span, Set.image_pair]
  change Ideal.span {vChartPolynomialEquiv (chartFraction centerIdeal (centerV (k := k)) centerU),
    vChartPolynomialEquiv (chartBaseMap centerIdeal centerV (centerV (k := k) : planeRing k))} = _
  rw [vChartPolynomialEquiv_coordinate, vChart_selected_equation]
  exact Ideal.span_pair_comm

theorem originIdeal_eq_comap :
    originIdeal (k := k) = Ideal.comap (vChartPolynomialEquiv (k := k)).toRingHom centerIdeal :=
  (Ideal.comap_map_of_bijective _ (vChartPolynomialEquiv (k := k)).bijective
    (I := originIdeal (k := k))).symm.trans
      (congrArg (Ideal.comap (vChartPolynomialEquiv (k := k)).toRingHom) map_originIdeal)

theorem originIdeal_isMaximal : (originIdeal (k := k)).IsMaximal := by
  rw [originIdeal_eq_comap]
  exact Ideal.comap_isMaximal_of_surjective (f := (vChartPolynomialEquiv (k := k)).toRingHom)
    (vChartPolynomialEquiv (k := k)).surjective

theorem originIdeal_isPrime : (originIdeal (k := k)).IsPrime := originIdeal_isMaximal.isPrime

local instance secondChartOriginIdeal_isPrime : (originIdeal (k := k)).IsPrime := originIdeal_isPrime

/-- The origin of the second Rees chart as a point of `Spec (reesVChartRing k)`. -/
def secondOrigin : Spec (CommRingCat.of (reesVChartRing k)) := ⟨originIdeal, originIdeal_isPrime⟩

theorem eq_secondOrigin_of_le (p : PrimeSpectrum (reesVChartRing k))
    (h : originIdeal (k := k) ≤ p.asIdeal) : p = secondOrigin :=
  PrimeSpectrum.ext (originIdeal_isMaximal.eq_of_le p.2.ne_top h).symm

/-- The local ring of the second chart at its origin. -/
abbrev originLocal : Type u := Localization.AtPrime (originIdeal (k := k))

theorem primeCompl_map_eq :
    (originIdeal (k := k)).primeCompl.map (vChartPolynomialEquiv (k := k)).toMonoidHom =
      (centerIdeal (k := k)).primeCompl := by
  ext x
  rw [Submonoid.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∉ originIdeal (k := k) := hy
    intro h
    apply hy'
    rw [originIdeal_eq_comap]
    exact h
  · intro hx
    have hx' : x ∉ centerIdeal (k := k) := hx
    refine ⟨(vChartPolynomialEquiv (k := k)).symm x, ?_,
      (vChartPolynomialEquiv (k := k)).apply_symm_apply x⟩
    intro h
    apply hx'
    have h' : (vChartPolynomialEquiv (k := k)).toRingHom ((vChartPolynomialEquiv (k := k)).symm x) ∈
        centerIdeal (k := k) := by
      rw [originIdeal_eq_comap] at h
      exact h
    have he : (vChartPolynomialEquiv (k := k)).toRingHom ((vChartPolynomialEquiv (k := k)).symm x) =
        x := (vChartPolynomialEquiv (k := k)).apply_symm_apply x
    rw [he] at h'
    exact h'

/-- `R_{(u/v, v)} ≃+* k[u][v]_{(u, v)}`. -/
def originLocalEquiv : originLocal (k := k) ≃+* originLocalRing (k := k) :=
  IsLocalization.ringEquivOfRingEquiv (originLocal (k := k)) (originLocalRing (k := k))
    (vChartPolynomialEquiv (k := k)) primeCompl_map_eq

theorem originLocalEquiv_algebraMap (r : reesVChartRing k) :
    originLocalEquiv (algebraMap (reesVChartRing k) (originLocal (k := k)) r) =
      algebraMap (planeRing k) (originLocalRing (k := k)) (vChartPolynomialEquiv r) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ _

theorem originLocal_regularLocal : RegularLocal (originLocal (k := k)) :=
  regularLocal_of_ringEquiv (originLocalEquiv (k := k)).symm originLocalRing_regularLocal

theorem ringKrullDim_originLocal : ringKrullDim (originLocal (k := k)) = 2 :=
  (ringKrullDim_eq_of_ringEquiv (originLocalEquiv (k := k))).trans ringKrullDim_originLocalRing

theorem span_eq_maximalIdeal_originLocal :
    Ideal.span {algebraMap (reesVChartRing k) (originLocal (k := k)) oldRatio,
      algebraMap (reesVChartRing k) (originLocal (k := k)) vEquation} =
      maximalIdeal (originLocal (k := k)) := by
  have h : Ideal.map (algebraMap (reesVChartRing k) (originLocal (k := k)))
      (Ideal.span {oldRatio, vEquation}) = maximalIdeal (originLocal (k := k)) :=
    Localization.AtPrime.map_eq_maximalIdeal (I := originIdeal (k := k))
  rw [Ideal.map_span, Set.image_pair] at h
  exact h

/-! ## The second Rees chart of the blowup `A.next → A` -/

variable (A : PlaneChartedScheme k)

/-- The second Rees chart of the blowup `A.next → A`. -/
def secondChart : Spec (CommRingCat.of (reesVChartRing k)) ⟶ A.next.carrier :=
  chartι centerIdeal centerV ≫ A.nextAffineBlowup

instance secondChart_isOpenImmersion : IsOpenImmersion (secondChart A) := by
  unfold secondChart
  infer_instance

@[reassoc] theorem secondChart_projection :
    secondChart A ≫ A.nextProjection =
      Spec.map (CommRingCat.ofHom (chartBaseMap (centerIdeal (k := k)) centerV)) ≫ A.chart := by
  rw [secondChart, Category.assoc, PlaneChartedScheme.nextAffineBlowup_projection,
    ← Category.assoc, chartι_toSpec]
  rfl

/-- The chart open of the second Rees chart. -/
def secondOpen : A.next.carrier.affineOpens :=
  ⟨secondChart A ''ᵁ ⊤, chart_image_top_isAffineOpen _⟩

/-- The section ring of the chart open, identified with the chart ring. -/
abbrev secondSections : Γ(A.next.carrier, (secondOpen A).1) ≃+* reesVChartRing k :=
  chartSectionsEquiv (secondChart A)

theorem mem_secondOpen (p : PrimeSpectrum (reesVChartRing k)) :
    (secondChart A).base p ∈ (secondOpen A).1 :=
  mem_chart_image_top _ p

/-! ## The newest exceptional curve `P` on the chart -/

theorem fiber_projection_eq (x : A.next.carrier) (hx : x ∈ Set.range (previousFiberι A).base) :
    A.nextProjection.base x = A.chart.base (originPoint (k := k)) := by
  have hx' : x ∈ Set.range (PointBlowupGluing.globalCenterFiberι A.chart (originPoint (k := k))
      A.center_closed).base := hx
  rw [PointBlowupGluing.range_globalCenterFiberι] at hx'
  exact hx'

/-- Every chart point of `P` has `v` in its prime. -/
theorem vEquation_mem_of_mem_fiber (p : PrimeSpectrum (reesVChartRing k))
    (hp : (secondChart A).base p ∈ Set.range (previousFiberι A).base) :
    vEquation (k := k) ∈ p.asIdeal := by
  have h : (secondChart A ≫ A.nextProjection).base p = A.chart.base (originPoint (k := k)) :=
    fiber_projection_eq A _ hp
  rw [secondChart_projection] at h
  have h' : (Spec.map (CommRingCat.ofHom (chartBaseMap (centerIdeal (k := k)) centerV))).base p =
      originPoint (k := k) :=
    A.chart.isOpenEmbedding.injective h
  have h2 : Ideal.comap (chartBaseMap (centerIdeal (k := k)) centerV) p.asIdeal = centerIdeal :=
    congrArg PrimeSpectrum.asIdeal h'
  have hv : vCoord (k := k) ∈ Ideal.comap (chartBaseMap (centerIdeal (k := k)) centerV) p.asIdeal := by
    rw [h2]
    exact centerV.property
  exact hv

/-- `P` lies in the affine blowup piece. -/
theorem fiber_mem_range_affineBlowup (x : A.next.carrier)
    (hx : x ∈ Set.range (previousFiberι A).base) : x ∈ Set.range A.nextAffineBlowup.base := by
  rcases PointBlowupGluing.pieces_cover A.chart (originPoint (k := k)) A.center_closed x with
    ⟨a, rfl⟩ | ⟨b, rfl⟩
  · exact ⟨a, rfl⟩
  · exfalso
    have h := fiber_projection_eq A _ hx
    have hb : (PointBlowupGluing.complementι A.chart (originPoint (k := k)) A.center_closed ≫
        A.nextProjection).base b = A.chart.base (originPoint (k := k)) := h
    rw [PlaneChartedScheme.nextProjection, PointBlowupGluing.complementι_projection] at hb
    exact b.2 hb

private theorem affineCenterFiber_global_isPullback :
    IsPullback (centerFiberι (centerIdeal (k := k)))
      (PointBlowupGluing.affineCenterFiberIso A.chart (originPoint (k := k)) A.center_closed).hom
      A.nextAffineBlowup (previousFiberι A) := by
  refine (PointBlowupGluing.exceptionalGlobalFiber_isPullback A.chart (originPoint (k := k))
    A.center_closed).of_iso (exceptionalFiberIso (centerIdeal (k := k))) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, exceptionalFiberIso_hom_ι]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id,
      PointBlowupGluing.exceptionalGlobalFiberIso, Iso.trans_hom]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- The quotient chart of the exceptional curve in the second chart, mapped to the whole fibre. -/
def secondFiberChartToGlobal : exceptionalChart (centerIdeal (k := k)) centerV ⟶ previousFiber A :=
  exceptionalChartToFiber (centerIdeal (k := k)) centerV ≫
    (PointBlowupGluing.affineCenterFiberIso A.chart (originPoint (k := k)) A.center_closed).hom

theorem secondFiberChart_isPullback :
    IsPullback (exceptionalChartInclusion (centerIdeal (k := k)) centerV)
      (secondFiberChartToGlobal A) (secondChart A) (previousFiberι A) := by
  simpa only [secondFiberChartToGlobal, secondChart] using
    (exceptionalChartToFiber_isPullback (centerIdeal (k := k)) centerV).paste_vert
      (affineCenterFiber_global_isPullback A)

private theorem secondFiber_coordinateKernel :
    RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (reesVChartRing k))).inv ≫
      (exceptionalChartInclusion (centerIdeal (k := k)) centerV).appTop).hom) =
        chartCenterIdeal (centerIdeal (k := k)) centerV := by
  have hΓ : Function.Injective
      ((Scheme.ΓSpecIso (CommRingCat.of
        (exceptionalChartRing (centerIdeal (k := k)) centerV))).inv.hom) :=
    (Scheme.ΓSpecIso (CommRingCat.of
      (exceptionalChartRing (centerIdeal (k := k)) centerV))).symm.commRingCatIsoToRingEquiv.injective
  rw [exceptionalChartInclusion, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.hom_comp, RingHom.ker_comp_of_injective _ hΓ,
    CommRingCat.hom_ofHom, Ideal.mk_ker]

/-- **On the second chart, `P` is the axis `v = 0`.** -/
theorem fiber_ideal_secondOpen :
    ((previousFiberι A).ker.ideal (secondOpen A)).map (secondSections A) =
      Ideal.span {vEquation} := by
  show ((previousFiberι A).ker.ideal (secondOpen A)).map (chartSectionsEquiv (secondChart A)) = _
  rw [← comap_inv_comap_inv_eq_map]
  unfold secondOpen
  rw [← Scheme.ker_ideal_of_isPullback_of_isOpenImmersion (previousFiberι A)
    (exceptionalChartInclusion (centerIdeal (k := k)) centerV) (secondFiberChartToGlobal A)
    (secondChart A) (secondFiberChart_isPullback A)
    ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of (reesVChartRing k)))⟩, Scheme.Hom.ker_apply]
  change RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (reesVChartRing k))).inv ≫
    (exceptionalChartInclusion (centerIdeal (k := k)) centerV).appTop).hom) = _
  rw [secondFiber_coordinateKernel]
  exact map_chartBaseMap_ideal (centerIdeal (k := k)) centerV

/-- Points of the first Rees chart lie in the selected chart of the next stage. -/
theorem uChart_range_subset_nextChart (a : AffineBlowup.scheme (centerIdeal (k := k)))
    (ha : a ∈ Set.range (chartι (centerIdeal (k := k)) centerU).base) :
    A.nextAffineBlowup.base a ∈ Set.range A.nextChart.base := by
  obtain ⟨c, rfl⟩ := ha
  refine ⟨(coordinateChartIso (k := k)).inv.base c, ?_⟩
  have e : (coordinateChartIso (k := k)).inv ≫ A.nextChart =
      chartι (centerIdeal (k := k)) centerU ≫ A.nextAffineBlowup := by
    rw [PlaneChartedScheme.nextChart, coordinateChart, Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun f => f.base c) e

/-- The centre of the next blowup (the origin of the first Rees chart) is not in the second chart. -/
theorem center_not_mem_range_secondChart (p : PrimeSpectrum (reesVChartRing k)) :
    (secondChart A).base p ≠ A.next.chart.base (originPoint (k := k)) := by
  intro h
  have h' : A.nextAffineBlowup.base ((chartι (centerIdeal (k := k)) centerV).base p) =
      A.nextAffineBlowup.base ((chartι (centerIdeal (k := k)) centerU).base
        ((coordinateChartIso (k := k)).hom.base (originPoint (k := k)))) := h
  have h'' := A.nextAffineBlowup.isOpenEmbedding.injective h'
  have hmem : (coordinateChartIso (k := k)).hom.base (originPoint (k := k)) ∈
      (chartι (centerIdeal (k := k)) centerU).base ⁻¹'
        Set.range (chartι (centerIdeal (k := k)) centerV).base := ⟨p, h''⟩
  rw [chart_preimage_chart_range] at hmem
  apply hmem
  change (FrobeniusBlowupContact.chartPolynomialEquiv (k := k)) (chartW (k := k)) ∈
    centerIdeal (k := k)
  rw [chartPolynomialEquiv_w]
  exact centerV.property

/-! ## The strict transform `C` of the previous exceptional curve on the chart of `B.next.next` -/

variable (B : PlaneChartedScheme k)

theorem successorCurve_eq :
    successorCurve B = oldCurveChartMorphism ≫ secondChart B.next := by
  unfold successorCurve oldCurveMorphism secondChart
  rw [Category.assoc]

theorem successorCurve_secondChart_isPullback :
    IsPullback (oldCurveChartMorphism (k := k)) (𝟙 _) (secondChart B.next) (successorCurve B) := by
  have hr : Set.range (successorCurve B).base ⊆ Set.range (secondChart B.next).base := by
    rintro _ ⟨t, rfl⟩
    exact ⟨(oldCurveChartMorphism (k := k)).base t,
      congrArg (fun f => f.base t) (successorCurve_eq B).symm⟩
  have hLift : IsOpenImmersion.lift (secondChart B.next) (successorCurve B) hr =
      oldCurveChartMorphism :=
    (IsOpenImmersion.lift_uniq (secondChart B.next) (successorCurve B) hr
      oldCurveChartMorphism (successorCurve_eq B).symm).symm
  simpa only [hLift] using
    IsOpenImmersion.isPullback_lift_id (successorCurve B) (secondChart B.next) hr

theorem previousStrictι_ker : (previousStrictι B).ker = (successorCurve B).ker :=
  (Scheme.IdealSheafData.ker_gluedTo (previousStrictIdeal B)).trans (previousStrictIdeal_eq B)

private theorem oldCurveChart_coordinateKernel :
    RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (reesVChartRing k))).inv ≫
        (oldCurveChartMorphism (k := k)).appTop).hom) =
      Ideal.span {oldRatio} := by
  have hΓ : Function.Injective
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom) :=
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).symm.commRingCatIsoToRingEquiv.injective
  rw [oldCurveChartMorphism, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.hom_comp,
    RingHom.ker_comp_of_injective _ hΓ, CommRingCat.hom_ofHom, oldCurveMap_ker]

/-- **On the second chart of `B.next.next`, the strict transform `C` is the axis `u/v = 0`.** -/
theorem strict_ideal_secondOpen :
    ((previousStrictι B).ker.ideal (secondOpen B.next)).map (secondSections B.next) =
      Ideal.span {oldRatio} := by
  show ((previousStrictι B).ker.ideal (secondOpen B.next)).map
    (chartSectionsEquiv (secondChart B.next)) = _
  rw [← comap_inv_comap_inv_eq_map, previousStrictι_ker]
  unfold secondOpen
  rw [← Scheme.ker_ideal_of_isPullback_of_isOpenImmersion (successorCurve B) oldCurveChartMorphism
    (𝟙 _) (secondChart B.next) (successorCurve_secondChart_isPullback B)
    ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of (reesVChartRing k)))⟩, Scheme.Hom.ker_apply]
  change RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (reesVChartRing k))).inv ≫
    (oldCurveChartMorphism (k := k)).appTop).hom) = _
  exact oldCurveChart_coordinateKernel

/-- Every chart point of `C` has `u/v` in its prime. -/
theorem oldRatio_mem_of_mem_strict (p : PrimeSpectrum (reesVChartRing k))
    (hp : (secondChart B.next).base p ∈ Set.range (previousStrictι B).base) :
    oldRatio (k := k) ∈ p.asIdeal := by
  rw [range_previousStrictι, successorCurve_eq] at hp
  have e : Set.range (oldCurveChartMorphism ≫ secondChart B.next).base =
      (secondChart B.next).base '' Set.range (oldCurveChartMorphism (k := k)).base := by
    rw [← Set.range_comp]
    rfl
  rw [e] at hp
  have h1 : p ∈ (secondChart B.next).base ⁻¹' closure ((secondChart B.next).base ''
      Set.range (oldCurveChartMorphism (k := k)).base) := hp
  rw [(secondChart B.next).isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    (secondChart B.next).base.hom.continuous,
    Set.preimage_image_eq _ (secondChart B.next).isOpenEmbedding.injective,
    (oldCurveChartMorphism (k := k)).isClosedEmbedding.isClosed_range.closure_eq] at h1
  obtain ⟨t, rfl⟩ := h1
  exact oldRatio_mem_image_prime t

theorem range_generators_eq :
    Set.range (fun i : Fin 2 => ((![centerU, centerV] i : centerIdeal (k := k)) : planeRing k)) =
      {uCoord, vCoord} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem span_range_generators :
    Ideal.span (Set.range (fun i : Fin 2 =>
      ((![centerU, centerV] i : centerIdeal (k := k)) : planeRing k))) = centerIdeal := by
  rw [range_generators_eq]
  rfl

/-- Every point of `C ∩ P` lies in the second chart. -/
theorem mem_range_secondChart_of_mem (x : B.next.next.carrier)
    (hC : x ∈ Set.range (previousStrictι B).base)
    (hP : x ∈ Set.range (previousFiberι B.next).base) :
    x ∈ Set.range (secondChart B.next).base := by
  obtain ⟨a, rfl⟩ := fiber_mem_range_affineBlowup B.next x hP
  have hcov : a ∈ (⨆ i, chartOpen (centerIdeal (k := k)) (![centerU, centerV] i)) := by
    rw [iSup_chartOpen_generators _ _ span_range_generators]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hcov
  rw [← chartι_opensRange] at hi
  fin_cases i
  · exfalso
    have hi' : a ∈ Set.range (chartι (centerIdeal (k := k)) centerU).base := hi
    obtain ⟨z, hz⟩ := hC
    have hx := uChart_range_subset_nextChart B.next a hi'
    rw [← hz] at hx
    exact previousStrict_avoids_nextChart B z hx
  · have hi' : a ∈ Set.range (chartι (centerIdeal (k := k)) centerV).base := hi
    obtain ⟨p, hp⟩ := hi'
    refine ⟨p, ?_⟩
    rw [← hp]
    rfl

/-- **Every point of `C ∩ P` is the origin of the second chart.** -/
theorem eq_crossingPoint_of_mem (x : B.next.next.carrier)
    (hC : x ∈ Set.range (previousStrictι B).base)
    (hP : x ∈ Set.range (previousFiberι B.next).base) :
    x = (secondChart B.next).base secondOrigin := by
  obtain ⟨p, rfl⟩ := mem_range_secondChart_of_mem B x hC hP
  have h1 := oldRatio_mem_of_mem_strict B p hC
  have h2 := vEquation_mem_of_mem_fiber B.next p hP
  have hle : originIdeal (k := k) ≤ p.asIdeal := by
    rw [originIdeal, Ideal.span_le]
    rintro y (rfl | rfl)
    · exact h1
    · exact h2
  rw [eq_secondOrigin_of_le p hle]

/-- **`C ∩ P` has at most one point.** -/
theorem strict_inter_fiber_subsingleton :
    (Set.range (previousStrictι B).base ∩ Set.range (previousFiberι B.next).base).Subsingleton :=
  fun x hx y hy =>
    (eq_crossingPoint_of_mem B x hx.1 hx.2).trans (eq_crossingPoint_of_mem B y hy.1 hy.2).symm

/-- The accepted adjacent point is the origin of the second chart. -/
theorem adjacentPoint_eq :
    (previousStrictι B).base (adjacentPoint B) = (secondChart B.next).base secondOrigin :=
  eq_crossingPoint_of_mem B _ ⟨_, rfl⟩ (adjacentPoint_mem_newFiber B)

/-! ## The stalk at the crossing point -/

/-- The origin of the second chart as a point of `A.next`. -/
def crossingPoint : A.next.carrier := (secondChart A).base secondOrigin

theorem crossingPoint_mem_secondOpen : crossingPoint A ∈ (secondOpen A).1 :=
  mem_secondOpen A secondOrigin

/-- The stalk at the crossing point is the local ring of the chart at its origin. -/
def crossingStalkEquiv :
    A.next.carrier.presheaf.stalk (crossingPoint A) ≃+* originLocal (k := k) :=
  openImmersionStalkLocalizationEquiv (secondChart A) secondOrigin

/-- **The stalk at the crossing point is regular.** -/
theorem crossingStalk_regularLocal :
    RegularLocal (A.next.carrier.presheaf.stalk (crossingPoint A)) :=
  regularLocal_of_ringEquiv (crossingStalkEquiv A).symm originLocal_regularLocal

/-- **The stalk at the crossing point has Krull dimension two.** -/
theorem crossingStalk_ringKrullDim :
    ringKrullDim (A.next.carrier.presheaf.stalk (crossingPoint A)) = 2 :=
  (ringKrullDim_eq_of_ringEquiv (crossingStalkEquiv A)).trans ringKrullDim_originLocal

/-- The germ of `u/v` (the equation of the older curve) at the crossing point. -/
def crossingU : A.next.carrier.presheaf.stalk (crossingPoint A) :=
  (crossingStalkEquiv A).symm (algebraMap (reesVChartRing k) (originLocal (k := k)) oldRatio)

/-- The germ of `v` (the equation of the newest curve) at the crossing point. -/
def crossingV : A.next.carrier.presheaf.stalk (crossingPoint A) :=
  (crossingStalkEquiv A).symm (algebraMap (reesVChartRing k) (originLocal (k := k)) vEquation)

theorem map_symm_maximalIdeal :
    Ideal.map (crossingStalkEquiv A).symm (maximalIdeal (originLocal (k := k))) =
      maximalIdeal (A.next.carrier.presheaf.stalk (crossingPoint A)) := by
  apply IsLocalRing.eq_maximalIdeal
  rw [← Ideal.comap_symm, RingEquiv.symm_symm]
  exact Ideal.comap_isMaximal_of_surjective (f := crossingStalkEquiv A)
    (crossingStalkEquiv A).surjective

/-- **The germs of `u/v` and `v` generate the maximal ideal of the stalk at the crossing point.** -/
theorem span_crossingU_crossingV :
    Ideal.span {crossingU A, crossingV A} =
      maximalIdeal (A.next.carrier.presheaf.stalk (crossingPoint A)) := by
  rw [← map_symm_maximalIdeal, ← span_eq_maximalIdeal_originLocal, Ideal.map_span,
    Set.image_insert_eq, Set.image_singleton]
  rfl

/-- The germ of `u/v` is the germ of the chart section `u/v`. -/
theorem crossingU_eq_germ :
    crossingU A = A.next.carrier.presheaf.germ (secondOpen A).1 (crossingPoint A)
      (crossingPoint_mem_secondOpen A) ((secondSections A).symm oldRatio) :=
  openImmersionStalkLocalizationEquiv_symm_algebraMap (secondChart A) secondOrigin oldRatio

/-- The germ of `v` is the germ of the chart section `v`. -/
theorem crossingV_eq_germ :
    crossingV A = A.next.carrier.presheaf.germ (secondOpen A).1 (crossingPoint A)
      (crossingPoint_mem_secondOpen A) ((secondSections A).symm vEquation) :=
  openImmersionStalkLocalizationEquiv_symm_algebraMap (secondChart A) secondOrigin vEquation

/-- The product of the two germs is the germ of the chart section `(u/v)·v`. -/
theorem crossingU_mul_crossingV_eq_germ :
    crossingU A * crossingV A = A.next.carrier.presheaf.germ (secondOpen A).1 (crossingPoint A)
      (crossingPoint_mem_secondOpen A) ((secondSections A).symm (oldRatio * vEquation)) := by
  rw [crossingU_eq_germ, crossingV_eq_germ, ← map_mul, ← map_mul]

/-! ## Primality of the two axes -/

theorem span_uCoord_isPrime : (Ideal.span {uCoord (k := k)}).IsPrime :=
  (Ideal.span_singleton_prime uCoord_ne_zero).mpr (Polynomial.prime_C_iff.mpr Polynomial.prime_X)

theorem span_vCoord_isPrime : (Ideal.span {vCoord (k := k)}).IsPrime :=
  (Ideal.span_singleton_prime vCoord_ne_zero).mpr vCoord_prime

theorem vCoord_not_mem_span_uCoord : vCoord (k := k) ∉ Ideal.span {uCoord (k := k)} := by
  rw [Ideal.mem_span_singleton]
  show ¬ (Polynomial.C Polynomial.X ∣ Polynomial.X)
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro h
  have h1 := h 1
  rw [Polynomial.coeff_X_one, Polynomial.X_dvd_iff, Polynomial.coeff_one_zero] at h1
  exact one_ne_zero h1

theorem map_span_vEquation :
    Ideal.map (vChartPolynomialEquiv (k := k)).toRingHom (Ideal.span {vEquation}) =
      Ideal.span {uCoord} := by
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {vChartPolynomialEquiv
    (chartBaseMap centerIdeal centerV (centerV (k := k) : planeRing k))} = _
  rw [vChart_selected_equation]

theorem map_span_oldRatio :
    Ideal.map (vChartPolynomialEquiv (k := k)).toRingHom (Ideal.span {oldRatio}) =
      Ideal.span {vCoord} := by
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {vChartPolynomialEquiv (chartFraction centerIdeal (centerV (k := k)) centerU)} = _
  rw [vChartPolynomialEquiv_coordinate]

theorem span_vEquation_isPrime : (Ideal.span {vEquation (k := k)}).IsPrime := by
  rw [← Ideal.comap_map_of_bijective (vChartPolynomialEquiv (k := k)).toRingHom
    (vChartPolynomialEquiv (k := k)).bijective (I := Ideal.span {vEquation}), map_span_vEquation]
  haveI hp : (Ideal.span {uCoord (k := k)}).IsPrime := span_uCoord_isPrime
  exact Ideal.IsPrime.comap (vChartPolynomialEquiv (k := k)).toRingHom

theorem span_oldRatio_isPrime : (Ideal.span {oldRatio (k := k)}).IsPrime := by
  rw [← Ideal.comap_map_of_bijective (vChartPolynomialEquiv (k := k)).toRingHom
    (vChartPolynomialEquiv (k := k)).bijective (I := Ideal.span {oldRatio}), map_span_oldRatio]
  haveI hp : (Ideal.span {vCoord (k := k)}).IsPrime := span_vCoord_isPrime
  exact Ideal.IsPrime.comap (vChartPolynomialEquiv (k := k)).toRingHom

theorem oldRatio_not_mem_span_vEquation : oldRatio (k := k) ∉ Ideal.span {vEquation} := by
  intro h
  have h' := Ideal.mem_map_of_mem (vChartPolynomialEquiv (k := k)).toRingHom h
  rw [map_span_vEquation] at h'
  change vChartPolynomialEquiv (chartFraction centerIdeal (centerV (k := k)) centerU) ∈ _ at h'
  rw [vChartPolynomialEquiv_coordinate] at h'
  exact vCoord_not_mem_span_uCoord h'

/-- The axis `v = 0` is prime in the section ring of the chart open. -/
theorem span_symm_vEquation_isPrime :
    (Ideal.span {(secondSections A).symm vEquation}).IsPrime := by
  rw [show ({(secondSections A).symm vEquation} : Set Γ(A.next.carrier, (secondOpen A).1)) =
      (secondSections A).symm '' {vEquation} from Set.image_singleton.symm,
    ← Ideal.map_span, Ideal.map_symm]
  haveI hp : (Ideal.span {vEquation (k := k)}).IsPrime := span_vEquation_isPrime
  exact Ideal.IsPrime.comap (secondSections A)

/-- The axis `u/v = 0` is prime in the section ring of the chart open. -/
theorem span_symm_oldRatio_isPrime :
    (Ideal.span {(secondSections A).symm oldRatio}).IsPrime := by
  rw [show ({(secondSections A).symm oldRatio} : Set Γ(A.next.carrier, (secondOpen A).1)) =
      (secondSections A).symm '' {oldRatio} from Set.image_singleton.symm,
    ← Ideal.map_span, Ideal.map_symm]
  haveI hp : (Ideal.span {oldRatio (k := k)}).IsPrime := span_oldRatio_isPrime
  exact Ideal.IsPrime.comap (secondSections A)

theorem symm_oldRatio_not_mem :
    (secondSections A).symm oldRatio ∉ Ideal.span {(secondSections A).symm vEquation} := by
  intro h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp h
  apply oldRatio_not_mem_span_vEquation (k := k)
  rw [Ideal.mem_span_singleton]
  refine ⟨secondSections A c, ?_⟩
  have h' := congrArg (secondSections A) hc
  rwa [RingEquiv.apply_symm_apply, map_mul, RingEquiv.apply_symm_apply] at h'

/-- The two axes meet in the ideal `(u/v · v)`. -/
theorem span_symm_inf :
    Ideal.span {(secondSections A).symm oldRatio} ⊓ Ideal.span {(secondSections A).symm vEquation} =
      Ideal.span {(secondSections A).symm (oldRatio * vEquation)} := by
  rw [span_singleton_inf_span_singleton_of_prime (span_symm_vEquation_isPrime A)
    (symm_oldRatio_not_mem A), map_mul]

/-! ## Statements at a point equal to the crossing point -/

theorem mem_secondOpen_of_eq (y : A.next.carrier) (hy : y = crossingPoint A) :
    y ∈ (secondOpen A).1 := by
  subst hy
  exact crossingPoint_mem_secondOpen A

theorem regularLocal_of_eq (y : A.next.carrier) (hy : y = crossingPoint A) :
    RegularLocal (A.next.carrier.presheaf.stalk y) := by
  subst hy
  exact crossingStalk_regularLocal A

theorem ringKrullDim_of_eq (y : A.next.carrier) (hy : y = crossingPoint A) :
    ringKrullDim (A.next.carrier.presheaf.stalk y) = 2 := by
  subst hy
  exact crossingStalk_ringKrullDim A

theorem span_germs_of_eq (y : A.next.carrier) (hy : y = crossingPoint A) :
    Ideal.span {A.next.carrier.presheaf.germ (secondOpen A).1 y (mem_secondOpen_of_eq A y hy)
        ((secondSections A).symm oldRatio),
      A.next.carrier.presheaf.germ (secondOpen A).1 y (mem_secondOpen_of_eq A y hy)
        ((secondSections A).symm vEquation)} =
      maximalIdeal (A.next.carrier.presheaf.stalk y) := by
  subst hy
  rw [← crossingU_eq_germ, ← crossingV_eq_germ]
  exact span_crossingU_crossingV A

end KltDP.Examples.FrobeniusSecondChartCrossing

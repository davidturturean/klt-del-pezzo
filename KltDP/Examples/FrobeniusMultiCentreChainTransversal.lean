import KltDP.Examples.FrobeniusExceptionalChainTransversalLater
import KltDP.Examples.FrobeniusMultiCentreChainPicard
import KltDP.Geometry.KernelIdealIsoTransport

/-!
# Single points and transversal crossings of the exceptional chains of `S_{p,n}`

BRIEF21, task 2 (lane F). Write `p = q + 1`, `A_i = translatedInitial (q+1) (a i)` the `i`-th tower,
`T_i = selectedStage (q+1) (a i) (q+1)` its stage `q+1`, `π_i = towerProjection (q+1) n a i : S_{p,n} ⟶ T_i`,
an isomorphism over the open `V_i = selectedProjection ⁻¹ᵁ otherComplement q n a i` (accepted
`towerProjection_restrict_isIso`), and `E_{i,idx} = exceptionalCurveι q n a i idx`, the base change of the
tower component `finalComponentι A_i q idx` along `π_i` (accepted `FrobeniusMultiCentreExceptional`), with
support `π_i⁻¹(finalSupport A_i q idx)` (`exceptionalSupport_eq`).

* **`singlePoints q n a ha : SinglePoints q n a`** (lane A1's first hypothesis for `S_{p,n}`): the
  intersection of two adjacent `E_{i,·}` is the preimage of the tower intersection, a single point
  (`chainSinglePoints`), and `π_i` is injective over `V_i` (`eq_of_restrict_isIso`), where all tower
  components lie (`finalComponent_mem_otherComplement`).
* `IsCrossingChart C D τ p rU rV` packages the chart data of a transversal crossing of two closed
  immersions `C`, `D` into a scheme `S`: an open immersion `τ : Spec R ⟶ S`, a point `p`, elements
  `rU, rV` generating the kernel ideals of `C`, `D` on the chart, `(rV)` prime with `rU ∉ (rV)`, and the
  local ring `R_p` regular of dimension two with maximal ideal `(rU, rV)`. `IsChainCrossingChart` adds
  the chain conditions: the crossing point is `τ p`, and the other components miss the chart.
  The tower charts of BRIEF20/21 give `IsChainCrossingChart` for every adjacent pair of every tower
  (`chainCrossingChart_last`, `chainCrossingChart_later`).
* `IsCrossingChart.restrict`: a crossing chart restricted to the basic open `D(r) ∋ p` is a crossing chart
  (localisation of the ideals; `R_r` localised at `p R_r` is `R_p`).
* `IsCrossingChart.lift`: a crossing chart whose image lies in the isomorphism locus `V` of `π : S' ⟶ S`
  lifts to a crossing chart of the base-changed curves on `S'` (the `liftedChart` construction of
  `FrobeniusExceptionalChainTransversalLater` and the generic `ker_ideal_map_eq_of_isPullback`).
* `curveChain_transversalCrossing_of_chart`: the crossing assembly of BRIEF20 for lane A1's generic
  `CurveChain` (the chains of `S_{p,n}`).
* **`towerTransversal q n a ha : TowerTransversal q n a ha (singlePoints q n a ha)`**: for each tower `i`
  and adjacent pair, shrink the tower chart to a basic open over `V_i` (`isBasis_basicOpen`), lift it to
  `S_{p,n}`, and assemble; hence lane A1's `towerChainPicardEquiv i` is unconditional
  (`towerChainPicardEquiv_unconditional`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing

universe u

namespace KltDP.Examples.FrobeniusMultiCentreChainTransversal

open KltDP.Geometry KltDP.Geometry.RationalTreePicard
open FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
  FrobeniusGlobalExceptionalSuccessor FrobeniusExceptionalChainPicard FrobeniusSecondChartCrossing
  FrobeniusExceptionalSuccessorChart FrobeniusBlowupChartIteration FrobeniusBlowupSmooth
  FrobeniusExceptionalChainTransversal FrobeniusExceptionalChainTransversalLater
  FrobeniusStageComplement.PlaneChartedScheme FrobeniusContactTowerSelectedPoint
  FrobeniusTranslatedCharts FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptional
  FrobeniusMultiCentreChainPicard

variable {k : Type u} [Field k]

local instance multiChainOriginPoint_isMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-! ## Generic lemmas -/

/-- Precomposition with an isomorphism does not change the kernel ideal sheaf. -/
theorem ker_comp_of_isIso {X Y Z : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (f : Y ⟶ Z) :
    (e ≫ f).ker = f.ker := by
  apply le_antisymm
  · have h := Scheme.Hom.le_ker_comp (inv e) (e ≫ f)
    rwa [IsIso.inv_hom_id_assoc] at h
  · exact Scheme.Hom.le_ker_comp e f

section CurveChainGeneric

variable (S : Scheme.{u}) (m : ℕ) (c : Fin (m + 1) → (projectiveSpace k 1 ⟶ S))
  [∀ i, IsClosedImmersion (c i)]

/-- The vanishing ideal sheaf of a chain of curves is the infimum of the radicals of the kernels. -/
theorem curveChain_ideal_eq_iInf :
    CurveChain.ideal S m c = ⨅ i : Fin (m + 1), (c i).ker.radical :=
  Scheme.IdealSheafData.vanishingIdeal_eq_iInf_ker_radical c
    ⟨CurveChain.locus S m c, CurveChain.locus_isClosed S m c⟩ rfl

theorem curveChain_ideal_ideal_eq (U : S.affineOpens) :
    (CurveChain.ideal S m c).ideal U = ⨅ i : Fin (m + 1), ((c i).ker.ideal U).radical := by
  rw [curveChain_ideal_eq_iInf, Scheme.IdealSheafData.ideal_iInf, iInf_apply]
  simp only [Scheme.IdealSheafData.radical_ideal]

variable [NoetherianSpace S] [IsLocallyNoetherian S]

omit [IsLocallyNoetherian S] in
/-- A germ of a section vanishing on the `i`-th curve lies in the stalk ideal of the `i`-th component
of the chain. -/
theorem curveChain_stalkMap_germ_mem_chartIdeal (hd : CurveChain.ChainData S m c) (i : Fin (m + 1))
    (x : CurveChain.scheme S m c) (U : S.affineOpens)
    (hxU : (CurveChain.inclusion S m c).base x ∈ U.1) (s : Γ(S, U.1))
    (hs : s ∈ (c i).ker.ideal U) :
    (CurveChain.inclusion S m c).stalkMap x (S.presheaf.germ U.1 _ hxU s) ∈
      (componentChartIdeal (CurveChain.scheme S m c) {CurveChain.component S m c hd i}
        ⟨CurveChain.inclusion S m c ⁻¹ᵁ U.1, U.2.preimage (CurveChain.inclusion S m c)⟩).map
          ((CurveChain.scheme S m c).presheaf.germ (CurveChain.inclusion S m c ⁻¹ᵁ U.1) x hxU).hom := by
  rw [Scheme.stalkMap_germ_apply]
  apply Ideal.mem_map_of_mem
  have hle : (CurveChain.curve S m c (ULift.up i)).ker ≤
      componentUnionIdeal (CurveChain.scheme S m c) {CurveChain.component S m c hd i} := by
    rw [componentUnionIdeal, ← Scheme.IdealSheafData.subset_support_iff_le_vanishingIdeal,
      coe_componentClosedUnion_singleton, CurveChain.component_val]
    exact (CurveChain.curve S m c (ULift.up i)).range_subset_ker_support
  show (CurveChain.inclusion S m c).app U.1 s ∈
    (componentUnionIdeal (CurveChain.scheme S m c) {CurveChain.component S m c hd i}).ideal
      ⟨CurveChain.inclusion S m c ⁻¹ᵁ U.1, U.2.preimage (CurveChain.inclusion S m c)⟩
  refine (Scheme.IdealSheafData.le_def.mp hle)
    ⟨CurveChain.inclusion S m c ⁻¹ᵁ U.1, U.2.preimage (CurveChain.inclusion S m c)⟩ ?_
  have hmem : s ∈ (CurveChain.curve S m c (ULift.up i) ≫ CurveChain.inclusion S m c).ker.ideal U := by
    rw [CurveChain.curve_comp]
    exact hs
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker] at hmem
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  have e1 := ConcreteCategory.congr_hom
    (Scheme.comp_app (CurveChain.curve S m c (ULift.up i)) (CurveChain.inclusion S m c) U.1) s
  exact e1.symm.trans hmem

omit [IsLocallyNoetherian S] in
/-- The crossing assembly for a chain of curves: chart data at a common point of two curves give the
transversal crossing of the corresponding components. -/
theorem curveChain_transversalCrossing_of_chart (hd : CurveChain.ChainData S m c) (i i' : Fin (m + 1))
    (x : CurveChain.scheme S m c) (U : S.affineOpens)
    (hxU : (CurveChain.inclusion S m c).base x ∈ U.1)
    (hreg : RegularLocal (S.presheaf.stalk ((CurveChain.inclusion S m c).base x)))
    (hdim : ringKrullDim (S.presheaf.stalk ((CurveChain.inclusion S m c).base x)) = 2)
    (sU sV : Γ(S, U.1))
    (hspan : Ideal.span {S.presheaf.germ U.1 _ hxU sU, S.presheaf.germ U.1 _ hxU sV} =
      maximalIdeal (S.presheaf.stalk ((CurveChain.inclusion S m c).base x)))
    (hker : (CurveChain.ideal S m c).ideal U = Ideal.span {sU * sV})
    (hsU : sU ∈ (c i).ker.ideal U) (hsV : sV ∈ (c i').ker.ideal U) :
    TransversalCrossing (CurveChain.inclusion S m c) (CurveChain.component S m c hd i)
      (CurveChain.component S m c hd i') x := by
  refine TransversalCrossing.ofChart (CurveChain.inclusion S m c) _ _ x hreg hdim
    (S.presheaf.germ U.1 _ hxU sU) (S.presheaf.germ U.1 _ hxU sV) hspan ?_
    ⟨CurveChain.inclusion S m c ⁻¹ᵁ U.1, U.2.preimage (CurveChain.inclusion S m c)⟩ hxU
    (curveChain_stalkMap_germ_mem_chartIdeal S m c hd i x U hxU sU hsU)
    (curveChain_stalkMap_germ_mem_chartIdeal S m c hd i' x U hxU sV hsV)
  change RingHom.ker ((CurveChain.ideal S m c).gluedTo.stalkMap x).hom = _
  rw [Scheme.IdealSheafData.stalkMap_gluedTo_ker_eq_map (CurveChain.ideal S m c) U hxU, hker,
    Ideal.map_span, Set.image_singleton, map_mul]
  rfl

end CurveChainGeneric

/-! ## Single points on `S_{p,n}` -/

section SinglePoints

variable (q n : ℕ) (a : Fin n → k)

/-- The `i`-th tower. -/
abbrev tower (i : Fin n) : PlaneChartedScheme k := translatedInitial (q + 1) (a i)

/-- The isomorphism locus of the `i`-th tower projection: the points over the complement of the other
centres. -/
abbrev isoOpen (i : Fin n) : (selectedStage (q + 1) (a i) (q + 1)).Opens :=
  selectedProjection (q + 1) (a i) (q + 1) ⁻¹ᵁ otherComplement q n a i

instance towerProjection_isoOpen_isIso (i : Fin n) :
    IsIso (towerProjection (q + 1) n a i ∣_ isoOpen q n a i) :=
  towerProjection_restrict_isIso q n a i (otherComplement q n a i)
    (fun j hj => center_not_mem_otherComplement q n a i j hj)

variable [IsAlgClosed k] (ha : Function.Injective a)
include ha

/-- The intersection of two exceptional curves of one tower is the preimage of the tower intersection;
if the latter is a single point, so is the former. -/
theorem exceptionalSupport_inter_subsingleton (i : Fin n) (idx idx' : FinalIndex.{0} q)
    (h : (finalSupport (tower q n a i) q idx ∩ finalSupport (tower q n a i) q idx').Subsingleton) :
    (exceptionalSupport q n a i idx ∩ exceptionalSupport q n a i idx').Subsingleton := by
  intro x hx y hy
  rw [exceptionalSupport_eq, exceptionalSupport_eq] at hx hy
  have hπ : (towerProjection (q + 1) n a i).base x = (towerProjection (q + 1) n a i).base y :=
    h ⟨hx.1, hx.2⟩ ⟨hy.1, hy.2⟩
  refine eq_of_restrict_isIso (towerProjection (q + 1) n a i) (isoOpen q n a i) x y ?_ ?_ hπ
  · obtain ⟨z, hz⟩ := hx.1
    rw [← hz]
    exact finalComponent_mem_otherComplement q n a ha i idx z
  · obtain ⟨z, hz⟩ := hy.1
    rw [← hz]
    exact finalComponent_mem_otherComplement q n a ha i idx z

/-- **Lane A1's hypothesis `SinglePoints` for `S_{p,n}`.** -/
theorem singlePoints : SinglePoints q n a where
  old i j hj :=
    exceptionalSupport_inter_subsingleton q n a ha i _ _ ((chainSinglePoints (tower q n a i) q).old j hj)
  newest i m hq :=
    exceptionalSupport_inter_subsingleton q n a ha i _ _
      ((chainSinglePoints (tower q n a i) q).newest m hq)

end SinglePoints

/-! ## Crossing charts -/

section CrossingChart

variable {S : Scheme.{u}}

/-- Chart data for a transversal crossing of the closed immersions `C`, `D` into `S`: an open immersion
`τ : Spec R ⟶ S`, a point `p`, elements `rU`, `rV` of `R` generating the kernel ideals of `C`, `D` on
the chart, `(rV)` prime with `rU ∉ (rV)`, and `R_p` regular of dimension two with maximal ideal
`(rU, rV)`. -/
structure IsCrossingChart {Z Z' : Scheme.{u}} (C : Z ⟶ S) (D : Z' ⟶ S) {R : Type u} [CommRing R]
    (τ : Spec (CommRingCat.of R) ⟶ S) [IsOpenImmersion τ] (p : PrimeSpectrum R) (rU rV : R) : Prop where
  ideal_C : ((C.ker.ideal ⟨τ ''ᵁ ⊤, chart_image_top_isAffineOpen τ⟩).map (chartSectionsEquiv τ)) =
    Ideal.span {rU}
  ideal_D : ((D.ker.ideal ⟨τ ''ᵁ ⊤, chart_image_top_isAffineOpen τ⟩).map (chartSectionsEquiv τ)) =
    Ideal.span {rV}
  prime_U : (Ideal.span {rU}).IsPrime
  prime_V : (Ideal.span {rV}).IsPrime
  not_mem : rU ∉ Ideal.span {rV}
  regular : RegularLocal (Localization.AtPrime p.asIdeal)
  dim : ringKrullDim (Localization.AtPrime p.asIdeal) = 2
  span_eq : Ideal.span {algebraMap R (Localization.AtPrime p.asIdeal) rU,
    algebraMap R (Localization.AtPrime p.asIdeal) rV} = maximalIdeal (Localization.AtPrime p.asIdeal)

/-- The generator `rV` vanishes at the point `p`. -/
theorem IsCrossingChart.rV_mem {Z Z' : Scheme.{u}} {C : Z ⟶ S} {D : Z' ⟶ S} {R : Type u} [CommRing R]
    {τ : Spec (CommRingCat.of R) ⟶ S} [IsOpenImmersion τ] {p : PrimeSpectrum R} {rU rV : R}
    (H : IsCrossingChart C D τ p rU rV) : rV ∈ p.asIdeal := by
  have h : algebraMap R (Localization.AtPrime p.asIdeal) rV ∈
      maximalIdeal (Localization.AtPrime p.asIdeal) := by
    rw [← H.span_eq]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p.asIdeal)
    p.asIdeal rV).mp h

/-- The generator `rU` vanishes at the point `p`. -/
theorem IsCrossingChart.rU_mem {Z Z' : Scheme.{u}} {C : Z ⟶ S} {D : Z' ⟶ S} {R : Type u} [CommRing R]
    {τ : Spec (CommRingCat.of R) ⟶ S} [IsOpenImmersion τ] {p : PrimeSpectrum R} {rU rV : R}
    (H : IsCrossingChart C D τ p rU rV) : rU ∈ p.asIdeal := by
  have h : algebraMap R (Localization.AtPrime p.asIdeal) rU ∈
      maximalIdeal (Localization.AtPrime p.asIdeal) := by
    rw [← H.span_eq]
    exact Ideal.subset_span (Set.mem_insert _ _)
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p.asIdeal)
    p.asIdeal rU).mp h

/-- **Lift of a crossing chart along a morphism that is an isomorphism over an open containing the
chart.** If `C'`, `D'` are the base changes of `C`, `D` along `π : S' ⟶ S`, and `τ` lands in an open `V`
over which `π` is an isomorphism, then the lifted chart is a crossing chart for `C'`, `D'`. -/
theorem IsCrossingChart.lift {S' Z Z' W W' : Scheme.{u}} {C : Z ⟶ S} {D : Z' ⟶ S}
    [QuasiCompact C] [QuasiCompact D] {R : Type u} [CommRing R]
    {τ : Spec (CommRingCat.of R) ⟶ S} [IsOpenImmersion τ] {p : PrimeSpectrum R} {rU rV : R}
    (H : IsCrossingChart C D τ p rU rV) (π : S' ⟶ S) (V : S.Opens) [IsIso (π ∣_ V)]
    (C' : W ⟶ S') (D' : W' ⟶ S') [QuasiCompact C'] [QuasiCompact D']
    (eC : W ⟶ Z) (eD : W' ⟶ Z') (HC : IsPullback C' eC π C) (HD : IsPullback D' eD π D)
    (τ' : Spec (CommRingCat.of R) ⟶ S') [IsOpenImmersion τ'] (hτ' : τ' ≫ π = τ) :
    IsCrossingChart C' D' τ' p rU rV where
  ideal_C := by
    rw [ker_ideal_map_eq_of_isPullback π C C' eC HC τ τ' hτ']
    exact H.ideal_C
  ideal_D := by
    rw [ker_ideal_map_eq_of_isPullback π D D' eD HD τ τ' hτ']
    exact H.ideal_D
  prime_U := H.prime_U
  prime_V := H.prime_V
  not_mem := H.not_mem
  regular := H.regular
  dim := H.dim
  span_eq := H.span_eq

/-- The lifted chart itself: the chart factored through `V`, followed by the inverse of the restricted
isomorphism and the inclusion of `π ⁻¹ᵁ V`. -/
def liftChart {S' : Scheme.{u}} {R : Type u} [CommRing R] (τ : Spec (CommRingCat.of R) ⟶ S)
    [IsOpenImmersion τ] (π : S' ⟶ S) (V : S.Opens) [IsIso (π ∣_ V)] (hτ : ∀ x, τ.base x ∈ V) :
    Spec (CommRingCat.of R) ⟶ S' :=
  IsOpenImmersion.lift V.ι τ (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hτ x) ≫ inv (π ∣_ V) ≫ (π ⁻¹ᵁ V).ι

instance liftChart_isOpenImmersion {S' : Scheme.{u}} {R : Type u} [CommRing R]
    (τ : Spec (CommRingCat.of R) ⟶ S) [IsOpenImmersion τ] (π : S' ⟶ S) (V : S.Opens) [IsIso (π ∣_ V)]
    (hτ : ∀ x, τ.base x ∈ V) : IsOpenImmersion (liftChart τ π V hτ) := by
  haveI hl : IsOpenImmersion (IsOpenImmersion.lift V.ι τ (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact hτ x)) := by
    haveI hcomp : IsOpenImmersion (IsOpenImmersion.lift V.ι τ (by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨x, rfl⟩
        exact hτ x) ≫ V.ι) := by
      rw [IsOpenImmersion.lift_fac]
      infer_instance
    exact IsOpenImmersion.of_comp _ V.ι
  unfold liftChart
  infer_instance

theorem liftChart_comp {S' : Scheme.{u}} {R : Type u} [CommRing R] (τ : Spec (CommRingCat.of R) ⟶ S)
    [IsOpenImmersion τ] (π : S' ⟶ S) (V : S.Opens) [IsIso (π ∣_ V)] (hτ : ∀ x, τ.base x ∈ V) :
    liftChart τ π V hτ ≫ π = τ := by
  rw [liftChart, Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
    IsOpenImmersion.lift_fac]

theorem liftChart_base_mem {S' : Scheme.{u}} {R : Type u} [CommRing R]
    (τ : Spec (CommRingCat.of R) ⟶ S) [IsOpenImmersion τ] (π : S' ⟶ S) (V : S.Opens) [IsIso (π ∣_ V)]
    (hτ : ∀ x, τ.base x ∈ V) (x : PrimeSpectrum R) : π.base ((liftChart τ π V hτ).base x) = τ.base x :=
  congrArg (fun f => f.base x) (liftChart_comp τ π V hτ)

end CrossingChart

/-! ## Restriction of a crossing chart to a basic open -/

section Restrict

theorem disjoint_powers_of_not_mem {R : Type u} [CommRing R] {I : Ideal R} (hI : I.IsPrime) {r : R}
    (hr : r ∉ I) : Disjoint (↑(Submonoid.powers r) : Set R) ↑I := by
  rw [Set.disjoint_left]
  intro x hx hxI
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff x r).mp hx
  exact hr (hI.mem_of_pow_mem n hxI)

variable {S : Scheme.{u}} {R : Type u} [CommRing R] (τ : Spec (CommRingCat.of R) ⟶ S)
  [IsOpenImmersion τ]

/-- The chart restricted to the basic open `D(r)`: `Spec R_r ⟶ Spec R ⟶ S`. -/
abbrev awayChart (r : R) : Spec (CommRingCat.of (Localization.Away r)) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ τ

theorem awayChart_image_le (r : R) : awayChart τ r ''ᵁ ⊤ ≤ τ ''ᵁ ⊤ := by
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.image_top_eq_opensRange]
  rintro x ⟨y, rfl⟩
  exact ⟨(Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))).base y, rfl⟩

/-- Restricting a chart section to the basic open is the localisation map in chart coordinates. -/
theorem awayChart_res (r : R) (x : R) :
    (S.presheaf.map (homOfLE (awayChart_image_le τ r)).op).hom ((chartSectionsEquiv τ).symm x) =
      (chartSectionsEquiv (awayChart τ r)).symm (algebraMap R (Localization.Away r) x) := by
  have h := appLE_of_chart_square (awayChart τ r) τ (𝟙 S)
    (CommRingCat.ofHom (algebraMap R (Localization.Away r))) (by rw [Category.comp_id])
    (fun y hy => awayChart_image_le τ r hy) x
  rw [chartSectionsEquiv_symm_apply, chartSectionsEquiv_symm_apply]
  refine Eq.trans ?_ h
  change _ = (S.presheaf.map (homOfLE (awayChart_image_le τ r)).op)
    (Scheme.Hom.app (𝟙 S) (τ ''ᵁ ⊤) ((τ.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of R)).inv x)))
  rw [Scheme.id_app]
  rfl

/-- The kernel ideal of a closed immersion on the restricted chart. -/
theorem ideal_awayChart (I : S.IdealSheafData) (x : R)
    (hI : (I.ideal ⟨τ ''ᵁ ⊤, chart_image_top_isAffineOpen τ⟩).map (chartSectionsEquiv τ) =
      Ideal.span {x}) (r : R) :
    (I.ideal ⟨awayChart τ r ''ᵁ ⊤, chart_image_top_isAffineOpen _⟩).map
        (chartSectionsEquiv (awayChart τ r)) =
      Ideal.span {algebraMap R (Localization.Away r) x} := by
  have h1 : I.ideal ⟨τ ''ᵁ ⊤, chart_image_top_isAffineOpen τ⟩ =
      Ideal.span {(chartSectionsEquiv τ).symm x} := eq_span_symm_of_map_eq _ hI
  have h2 : I.ideal ⟨awayChart τ r ''ᵁ ⊤, chart_image_top_isAffineOpen _⟩ =
      (I.ideal ⟨τ ''ᵁ ⊤, chart_image_top_isAffineOpen τ⟩).map
        (S.presheaf.map (homOfLE (awayChart_image_le τ r)).op).hom :=
    (I.map_ideal (awayChart_image_le τ r)).symm
  rw [h2, h1, Ideal.map_span, Set.image_singleton, awayChart_res, Ideal.map_span,
    Set.image_singleton, RingEquiv.apply_symm_apply]

/-- The restricted point `p R_r` of `Spec R_r` over `p ∈ D(r)`. -/
def awayPoint (p : PrimeSpectrum R) (r : R) (hr : r ∉ p.asIdeal) :
    PrimeSpectrum (Localization.Away r) :=
  ⟨p.asIdeal.map (algebraMap R (Localization.Away r)),
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers r) _ p.asIdeal p.2
      (disjoint_powers_of_not_mem p.2 hr)⟩

theorem awayPoint_comap (p : PrimeSpectrum R) (r : R) (hr : r ∉ p.asIdeal) :
    (awayPoint p r hr).asIdeal.comap (algebraMap R (Localization.Away r)) = p.asIdeal :=
  IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers r) _ p.asIdeal p.2
    (disjoint_powers_of_not_mem p.2 hr)

omit [IsOpenImmersion τ] in
theorem awayChart_awayPoint (p : PrimeSpectrum R) (r : R) (hr : r ∉ p.asIdeal) :
    (awayChart τ r).base (awayPoint p r hr) = τ.base p := by
  show τ.base ((Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))).base
    (awayPoint p r hr)) = τ.base p
  congr 1
  apply PrimeSpectrum.ext
  rw [Spec.map_base_apply]
  exact awayPoint_comap p r hr

/-- `R_p` is the localisation of `R` at `p` also through `R_r`. -/
instance awayPoint_isLocalization (p : PrimeSpectrum R) (r : R) (hr : r ∉ p.asIdeal) :
    IsLocalization p.asIdeal.primeCompl (Localization.AtPrime (awayPoint p r hr).asIdeal) := by
  have hsub : p.asIdeal.primeCompl =
      ((awayPoint p r hr).asIdeal.comap (algebraMap R (Localization.Away r))).primeCompl :=
    Submonoid.ext fun x => show x ∉ p.asIdeal ↔ x ∉ _ by
      rw [awayPoint_comap]
      exact Iff.rfl
  rw [hsub]
  exact IsLocalization.isLocalization_atPrime_localization_atPrime (M := Submonoid.powers r)
    (awayPoint p r hr).asIdeal

/-- `(R_r)_{p R_r} ≃ R_p`. -/
def awayLocalEquiv (p : PrimeSpectrum R) (r : R) (hr : r ∉ p.asIdeal) :
    Localization.AtPrime p.asIdeal ≃+* Localization.AtPrime (awayPoint p r hr).asIdeal :=
  (IsLocalization.algEquiv p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
    (Localization.AtPrime (awayPoint p r hr).asIdeal)).toRingEquiv

theorem awayLocalEquiv_algebraMap (p : PrimeSpectrum R) (r : R) (hr : r ∉ p.asIdeal) (x : R) :
    awayLocalEquiv p r hr (algebraMap R (Localization.AtPrime p.asIdeal) x) =
      algebraMap (Localization.Away r) (Localization.AtPrime (awayPoint p r hr).asIdeal)
        (algebraMap R (Localization.Away r) x) :=
  (IsLocalization.algEquiv p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
    (Localization.AtPrime (awayPoint p r hr).asIdeal)).commutes x

theorem awayLocalEquiv_map_maximalIdeal (p : PrimeSpectrum R) (r : R) (hr : r ∉ p.asIdeal) :
    Ideal.map (awayLocalEquiv p r hr) (maximalIdeal (Localization.AtPrime p.asIdeal)) =
      maximalIdeal (Localization.AtPrime (awayPoint p r hr).asIdeal) := by
  apply IsLocalRing.eq_maximalIdeal
  rw [← Ideal.comap_symm]
  exact Ideal.comap_isMaximal_of_surjective (f := (awayLocalEquiv p r hr).symm)
    (awayLocalEquiv p r hr).symm.surjective

variable {Z Z' : Scheme.{u}} {C : Z ⟶ S} {D : Z' ⟶ S}

/-- **A crossing chart restricted to a basic open containing the point is a crossing chart.** -/
theorem IsCrossingChart.restrict {p : PrimeSpectrum R} {rU rV : R} (H : IsCrossingChart C D τ p rU rV)
    (r : R) (hr : r ∉ p.asIdeal) :
    IsCrossingChart C D (awayChart τ r) (awayPoint p r hr) (algebraMap R (Localization.Away r) rU)
      (algebraMap R (Localization.Away r) rV) := by
  have hV : Ideal.span {rV} ≤ p.asIdeal :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr H.rV_mem)
  have hrV : r ∉ Ideal.span {rV} := fun h => hr (hV h)
  have hd := disjoint_powers_of_not_mem H.prime_V hrV
  have hU : Ideal.span {rU} ≤ p.asIdeal :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr H.rU_mem)
  have hrU : r ∉ Ideal.span {rU} := fun h => hr (hU h)
  have hdU := disjoint_powers_of_not_mem H.prime_U hrU
  have hmap : Ideal.span {algebraMap R (Localization.Away r) rV} =
      (Ideal.span {rV}).map (algebraMap R (Localization.Away r)) := by
    rw [Ideal.map_span, Set.image_singleton]
  have hmapU : Ideal.span {algebraMap R (Localization.Away r) rU} =
      (Ideal.span {rU}).map (algebraMap R (Localization.Away r)) := by
    rw [Ideal.map_span, Set.image_singleton]
  refine
    { ideal_C := ideal_awayChart τ C.ker rU H.ideal_C r
      ideal_D := ideal_awayChart τ D.ker rV H.ideal_D r
      prime_U := by
        rw [hmapU]
        exact IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers r) _ _ H.prime_U hdU
      prime_V := by
        rw [hmap]
        exact IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers r) _ _ H.prime_V hd
      not_mem := by
        intro h
        rw [hmap] at h
        have h' : rU ∈ Ideal.comap (algebraMap R (Localization.Away r))
            ((Ideal.span {rV}).map (algebraMap R (Localization.Away r))) := h
        rw [IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers r) _ _ H.prime_V hd] at h'
        exact H.not_mem h'
      regular := regularLocal_of_ringEquiv (awayLocalEquiv p r hr) H.regular
      dim := (ringKrullDim_eq_of_ringEquiv (awayLocalEquiv p r hr)).symm.trans H.dim
      span_eq := ?_ }
  rw [← awayLocalEquiv_map_maximalIdeal p r hr, ← H.span_eq, Ideal.map_span, Set.image_insert_eq,
    Set.image_singleton, awayLocalEquiv_algebraMap, awayLocalEquiv_algebraMap]

end Restrict

/-! ## Stalk statements at a chart point (arbitrary chart ring) -/

section ChartPoint

variable {Y : Scheme.{u}} {R : Type u} [CommRing R] (jc : Spec (CommRingCat.of R) ⟶ Y)
  [IsOpenImmersion jc] (p : PrimeSpectrum R)

theorem stalk_regularLocal_of_eq (hreg : RegularLocal (Localization.AtPrime p.asIdeal)) (y : Y)
    (hy : y = jc.base p) : RegularLocal (Y.presheaf.stalk y) := by
  subst hy
  exact regularLocal_of_ringEquiv (openImmersionStalkLocalizationEquiv jc p).symm hreg

theorem stalk_ringKrullDim_of_eq (hdim : ringKrullDim (Localization.AtPrime p.asIdeal) = 2) (y : Y)
    (hy : y = jc.base p) : ringKrullDim (Y.presheaf.stalk y) = 2 := by
  subst hy
  exact (ringKrullDim_eq_of_ringEquiv (openImmersionStalkLocalizationEquiv jc p)).trans hdim

theorem stalk_mem_of_eq (y : Y) (hy : y = jc.base p) : y ∈ jc ''ᵁ ⊤ := by
  subst hy
  exact mem_chart_image_top jc p

theorem stalk_span_germs_of_eq (rU rV : R)
    (hspan : Ideal.span {algebraMap R (Localization.AtPrime p.asIdeal) rU,
      algebraMap R (Localization.AtPrime p.asIdeal) rV} = maximalIdeal (Localization.AtPrime p.asIdeal))
    (y : Y) (hy : y = jc.base p) :
    Ideal.span {Y.presheaf.germ (jc ''ᵁ ⊤) y (stalk_mem_of_eq jc p y hy) ((chartSectionsEquiv jc).symm rU),
      Y.presheaf.germ (jc ''ᵁ ⊤) y (stalk_mem_of_eq jc p y hy) ((chartSectionsEquiv jc).symm rV)} =
      maximalIdeal (Y.presheaf.stalk y) := by
  subst hy
  have hmax : Ideal.map (openImmersionStalkLocalizationEquiv jc p).symm
      (maximalIdeal (Localization.AtPrime p.asIdeal)) = maximalIdeal (Y.presheaf.stalk (jc.base p)) := by
    apply IsLocalRing.eq_maximalIdeal
    rw [← Ideal.comap_symm, RingEquiv.symm_symm]
    exact Ideal.comap_isMaximal_of_surjective (f := openImmersionStalkLocalizationEquiv jc p)
      (openImmersionStalkLocalizationEquiv jc p).surjective
  have key : Ideal.span {(openImmersionStalkLocalizationEquiv jc p).symm
      (algebraMap R (Localization.AtPrime p.asIdeal) rU),
      (openImmersionStalkLocalizationEquiv jc p).symm
      (algebraMap R (Localization.AtPrime p.asIdeal) rV)} =
      maximalIdeal (Y.presheaf.stalk (jc.base p)) := by
    rw [← hmax, ← hspan, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  rw [openImmersionStalkLocalizationEquiv_symm_algebraMap,
    openImmersionStalkLocalizationEquiv_symm_algebraMap] at key
  exact key

/-- Primality of the preimage of a principal prime under a ring isomorphism of section rings. -/
theorem span_symm_isPrime {Γ : Type u} [CommRing Γ] (θ : Γ ≃+* R) {r : R}
    (h : (Ideal.span {r}).IsPrime) : (Ideal.span {θ.symm r}).IsPrime := by
  rw [show ({θ.symm r} : Set Γ) = θ.symm '' {r} from Set.image_singleton.symm, ← Ideal.map_span,
    Ideal.map_symm]
  haveI hp : (Ideal.span {r}).IsPrime := h
  exact Ideal.IsPrime.comap θ

theorem symm_not_mem_span_symm {Γ : Type u} [CommRing Γ] (θ : Γ ≃+* R) {rU rV : R}
    (h : rU ∉ Ideal.span {rV}) : θ.symm rU ∉ Ideal.span {θ.symm rV} := by
  intro hmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmem
  apply h
  rw [Ideal.mem_span_singleton]
  refine ⟨θ c, ?_⟩
  have h' := congrArg θ hc
  rwa [RingEquiv.apply_symm_apply, map_mul, RingEquiv.apply_symm_apply] at h'

theorem span_symm_inf_span_symm {Γ : Type u} [CommRing Γ] (θ : Γ ≃+* R) {rU rV : R}
    (hV : (Ideal.span {rV}).IsPrime) (h : rU ∉ Ideal.span {rV}) :
    Ideal.span {θ.symm rU} ⊓ Ideal.span {θ.symm rV} = Ideal.span {θ.symm rU * θ.symm rV} :=
  span_singleton_inf_span_singleton_of_prime (span_symm_isPrime θ hV) (symm_not_mem_span_symm θ h)

end ChartPoint

/-! ## Chain crossing charts of the towers -/

/-- Chart data for the crossing of two components `idx`, `idx'` of the final exceptional chain of
`A.stage (q+1)`: a crossing chart whose point is the common point, and which the other components
miss. -/
structure IsChainCrossingChart (A : PlaneChartedScheme k) (q : ℕ) (idx idx' : FinalIndex.{0} q)
    {R : Type u} [CommRing R] (τ : Spec (CommRingCat.of R) ⟶ chainStage q A) [IsOpenImmersion τ]
    (p : PrimeSpectrum R) (rU rV : R) : Prop extends
    IsCrossingChart (finalComponentι A q idx) (finalComponentι A q idx') τ p rU rV where
  eq_of_mem : ∀ x, x ∈ finalSupport A q idx → x ∈ finalSupport A q idx' → x = τ.base p
  other_not_mem : ∀ idx'' : FinalIndex.{0} q, idx'' ≠ idx → idx'' ≠ idx' →
    ∀ z, (finalComponentι A q idx'').base z ∉ τ ''ᵁ ⊤

section TowerCharts

variable (A : PlaneChartedScheme k)

/-- The birth-stage crossing chart of the last pair `C_{m+1}, P` of stage `m+2`. -/
theorem chainCrossingChart_last (m : ℕ) :
    IsChainCrossingChart A (m + 1) (Sum.inl ⟨m, by omega⟩) (Sum.inr PUnit.unit)
      (secondChart (A.stage (m + 1))) secondOrigin oldRatio vEquation where
  ideal_C := by
    rw [finalComponentι_last]
    exact strict_ideal_secondOpen (A.stage m)
  ideal_D := fiber_ideal_secondOpen (A.stage (m + 1))
  prime_U := span_oldRatio_isPrime
  prime_V := span_vEquation_isPrime
  not_mem := oldRatio_not_mem_span_vEquation
  regular := originLocal_regularLocal
  dim := ringKrullDim_originLocal
  span_eq := span_eq_maximalIdeal_originLocal
  eq_of_mem x hC hP := by
    have hC' : x ∈ Set.range (finalOldMap A (m + 2) m (le_refl _)).base := hC
    rw [finalOldMap_birth] at hC'
    exact eq_crossingPoint_of_mem (A.stage m) x hC' hP
  other_not_mem idx hne hne' z := by
    rcases idx with ⟨i, hi⟩ | ⟨⟩
    · have him : i + 2 ≤ m + 1 := by
        rcases Nat.lt_or_ge i m with h | h
        · omega
        · exfalso
          apply hne
          congr 1
          exact Fin.ext (show i = m by omega)
      exact old_not_mem_secondOpen A m i him z
    · exact absurd rfl hne'

/-- The lifted crossing chart of an older pair `C_{j+1}, C_{j+2}` (`j + 1 < q`) of stage `q+1`. -/
theorem chainCrossingChart_later (q j : ℕ) (hj : j + 1 < q) :
    IsChainCrossingChart A q (Sum.inl ⟨j, by omega⟩) (Sum.inl ⟨j + 1, hj⟩)
      (liftedChart A j (q + 1) (laterLe j hj)) secondOrigin oldRatio vEquation where
  ideal_C := old_ideal_lifted A j (q + 1) (laterLe j hj)
  ideal_D := newer_ideal_lifted A j (q + 1) (laterLe j hj)
  prime_U := span_oldRatio_isPrime
  prime_V := span_vEquation_isPrime
  not_mem := oldRatio_not_mem_span_vEquation
  regular := originLocal_regularLocal
  dim := ringKrullDim_originLocal
  span_eq := span_eq_maximalIdeal_originLocal
  eq_of_mem x hC hD :=
    (old_pair_subsingleton A (q + 1) j (laterLe j hj) ⟨hC, hD⟩
      ⟨crossingPointN_mem_left A j (q + 1) (laterLe j hj),
        crossingPointN_mem_right A j (q + 1) (laterLe j hj)⟩).trans
      (crossingPointN_eq A j (q + 1) (laterLe j hj))
  other_not_mem idx hne hne' z := by
    rcases idx with ⟨i, hi⟩ | ⟨⟩
    · have hij : i ≠ j := fun e => hne (by congr 1; exact Fin.ext e)
      have hij' : i ≠ j + 1 := fun e => hne' (by congr 1; exact Fin.ext e)
      rcases Nat.lt_or_ge i j with hlt | hge
      · exact old_component_not_mem A j (q + 1) (laterLe j hj) i (by omega) z
      · exact later_component_not_mem A j (q + 1) (laterLe j hj) i (by omega) (by omega) z
    · exact newest_component_not_mem A j q hj z

end TowerCharts

/-! ## Transversality on `S_{p,n}` -/

section Assembly

variable (q n : ℕ) (a : Fin n → k) [IsAlgClosed k] (ha : Function.Injective a)
include ha

/-- **The crossing of the pair `j` of the `i`-th chain of `S_{p,n}` is transversal**, given a chain
crossing chart of the tower: shrink it to a basic open over the isomorphism locus, lift it to `S_{p,n}`
and assemble. -/
theorem transversalCrossing_of_chainCrossingChart (i : Fin n) (j : Fin q) {R : Type u} [CommRing R]
    (τ : Spec (CommRingCat.of R) ⟶ selectedStage (q + 1) (a i) (q + 1)) [IsOpenImmersion τ]
    (p : PrimeSpectrum R) (rU rV : R)
    (H : IsChainCrossingChart (tower q n a i) q (chainMember.{0} q j.castSucc)
      (chainMember.{0} q j.succ) τ p rU rV)
    (x : CurveChain.scheme (multiSurface (q + 1) n a) q (chainCurve q n a ha i))
    (hC : x ∈ (CurveChain.component (multiSurface (q + 1) n a) q (chainCurve q n a ha i)
      (chainData q n a ha (singlePoints q n a ha) i) j.castSucc).1)
    (hD : x ∈ (CurveChain.component (multiSurface (q + 1) n a) q (chainCurve q n a ha i)
      (chainData q n a ha (singlePoints q n a ha) i) j.succ).1) :
    TransversalCrossing (CurveChain.inclusion (multiSurface (q + 1) n a) q (chainCurve q n a ha i))
      (CurveChain.component (multiSurface (q + 1) n a) q (chainCurve q n a ha i)
        (chainData q n a ha (singlePoints q n a ha) i) j.castSucc)
      (CurveChain.component (multiSurface (q + 1) n a) q (chainCurve q n a ha i)
        (chainData q n a ha (singlePoints q n a ha) i) j.succ) x := by
  set ι := CurveChain.inclusion (multiSurface (q + 1) n a) q (chainCurve q n a ha i)
  set π := towerProjection (q + 1) n a i
  -- the point lies on both curves of `S_{p,n}`, hence over the tower crossing point
  have hyC : ι.base x ∈ exceptionalSupport q n a i (chainMember.{0} q j.castSucc) := by
    have h := hC
    rw [CurveChain.component_val, CurveChain.range_curve_eq] at h
    rw [← range_chainCurve q n a ha i j.castSucc]
    exact h
  have hyD : ι.base x ∈ exceptionalSupport q n a i (chainMember.{0} q j.succ) := by
    have h := hD
    rw [CurveChain.component_val, CurveChain.range_curve_eq] at h
    rw [← range_chainCurve q n a ha i j.succ]
    exact h
  rw [exceptionalSupport_eq] at hyC hyD
  have hπ : π.base (ι.base x) = τ.base p := H.eq_of_mem _ hyC hyD
  have hpV : τ.base p ∈ isoOpen q n a i := by
    obtain ⟨z, hz⟩ := hyC
    rw [← hπ, ← hz]
    exact finalComponent_mem_otherComplement q n a ha i _ z
  -- shrink the chart to a basic open over the isomorphism locus
  have hpV' : p ∈ ((τ ⁻¹ᵁ isoOpen q n a i : (Spec (CommRingCat.of R)).Opens) :
      Set (Spec (CommRingCat.of R))) := hpV
  obtain ⟨v, hvB, hpv, hvu⟩ :=
    (isBasis_basicOpen (Spec (CommRingCat.of R))).exists_subset_of_mem_open hpV'
      (τ ⁻¹ᵁ isoOpen q n a i).isOpen
  obtain ⟨U, ⟨f, hfU⟩, hUv⟩ := hvB
  have hpf : p ∈ (Spec (CommRingCat.of R)).basicOpen f := by
    rw [hfU]
    show p ∈ (U : Set (Spec (CommRingCat.of R)))
    rw [hUv]
    exact hpv
  have hfle : ((Spec (CommRingCat.of R)).basicOpen f : Set (Spec (CommRingCat.of R))) ⊆
      ((τ ⁻¹ᵁ isoOpen q n a i : (Spec (CommRingCat.of R)).Opens) : Set (Spec (CommRingCat.of R))) := by
    rw [hfU, hUv]
    exact hvu
  set r := (Scheme.ΓSpecIso (CommRingCat.of R)).hom f
  have hpr : r ∉ p.asIdeal := by
    have h := hpf
    rw [basicOpen_eq_of_affine'] at h
    exact h
  have hτr : ∀ x', (awayChart τ r).base x' ∈ isoOpen q n a i := by
    intro x'
    have hx' : (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))).base x' ∈
        PrimeSpectrum.basicOpen r := by
      rw [Spec.map_base_apply]
      exact (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r).le ⟨x', rfl⟩
    have hx'' : (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))).base x' ∈
        (Spec (CommRingCat.of R)).basicOpen f := by
      rw [basicOpen_eq_of_affine']
      exact hx'
    exact hfle hx''
  -- the restricted and lifted charts
  set τr := awayChart τ r
  set pr := awayPoint p r hpr
  have Hr : IsCrossingChart (finalComponentι (tower q n a i) q (chainMember.{0} q j.castSucc))
      (finalComponentι (tower q n a i) q (chainMember.{0} q j.succ)) τr pr
      (algebraMap R (Localization.Away r) rU) (algebraMap R (Localization.Away r) rV) :=
    IsCrossingChart.restrict τ H.toIsCrossingChart r hpr
  let τ' := liftChart τr π (isoOpen q n a i) hτr
  have Hlift : IsCrossingChart (exceptionalCurveι q n a i (chainMember.{0} q j.castSucc))
      (exceptionalCurveι q n a i (chainMember.{0} q j.succ)) τ' pr
      (algebraMap R (Localization.Away r) rU) (algebraMap R (Localization.Away r) rV) :=
    Hr.lift π (isoOpen q n a i) _ _ (exceptionalCurveToComponent q n a i _)
      (exceptionalCurveToComponent q n a i _) (IsPullback.of_hasPullback _ _)
      (IsPullback.of_hasPullback _ _) τ' (liftChart_comp τr π (isoOpen q n a i) hτr)
  have hy : ι.base x = τ'.base pr := by
    apply eq_of_restrict_isIso π (isoOpen q n a i)
    · rw [hπ]
      exact hpV
    · rw [liftChart_base_mem]
      exact hτr pr
    · rw [hπ, liftChart_base_mem, awayChart_awayPoint]
  -- points of the lifted chart lie over the tower chart
  have hover : ∀ y, y ∈ τ' ''ᵁ ⊤ → π.base y ∈ τ ''ᵁ ⊤ := by
    intro y hy'
    have hy'' : y ∈ τ'.opensRange := by
      rw [← Scheme.Hom.image_top_eq_opensRange]
      exact hy'
    obtain ⟨x', rfl⟩ := hy''
    rw [liftChart_base_mem]
    exact awayChart_image_le τ r (mem_chart_image_top τr x')
  -- the other curves of the chain miss the lifted chart
  have hother : ∀ j' : Fin (q + 1), j' ≠ j.castSucc → j' ≠ j.succ →
      ∀ z, (chainCurve q n a ha i j').base z ∉ τ' ''ᵁ ⊤ := by
    intro j' h1 h2 z hz
    have hne1 : chainMember.{0} q j' ≠ chainMember.{0} q j.castSucc :=
      fun e => h1 ((chainEquiv q).injective e)
    have hne2 : chainMember.{0} q j' ≠ chainMember.{0} q j.succ :=
      fun e => h2 ((chainEquiv q).injective e)
    have hmem : (chainCurve q n a ha i j').base z ∈ exceptionalSupport q n a i (chainMember.{0} q j') := by
      rw [← range_chainCurve q n a ha i j']
      exact ⟨z, rfl⟩
    rw [exceptionalSupport_eq] at hmem
    obtain ⟨w, hw⟩ := hmem
    apply H.other_not_mem (chainMember.{0} q j') hne1 hne2 w
    rw [hw]
    exact hover _ hz
  -- the vanishing ideal of the chain on the lifted chart
  set U' : (multiSurface (q + 1) n a).affineOpens := ⟨τ' ''ᵁ ⊤, chart_image_top_isAffineOpen τ'⟩
  set θ' := chartSectionsEquiv τ'
  have hkC : (chainCurve q n a ha i j.castSucc).ker.ideal U' =
      Ideal.span {θ'.symm (algebraMap R (Localization.Away r) rU)} := by
    show ((curveIso q n a ha i (chainMember.{0} q j.castSucc)).inv ≫
      exceptionalCurveι q n a i (chainMember.{0} q j.castSucc)).ker.ideal U' = _
    rw [ker_comp_of_isIso]
    exact eq_span_symm_of_map_eq _ Hlift.ideal_C
  have hkD : (chainCurve q n a ha i j.succ).ker.ideal U' =
      Ideal.span {θ'.symm (algebraMap R (Localization.Away r) rV)} := by
    show ((curveIso q n a ha i (chainMember.{0} q j.succ)).inv ≫
      exceptionalCurveι q n a i (chainMember.{0} q j.succ)).ker.ideal U' = _
    rw [ker_comp_of_isIso]
    exact eq_span_symm_of_map_eq _ Hlift.ideal_D
  have hker : (CurveChain.ideal (multiSurface (q + 1) n a) q (chainCurve q n a ha i)).ideal U' =
      Ideal.span {θ'.symm (algebraMap R (Localization.Away r) rU) *
        θ'.symm (algebraMap R (Localization.Away r) rV)} := by
    rw [curveChain_ideal_ideal_eq, iInf_eq_inf_of_top _ j.castSucc j.succ]
    · rw [hkC, hkD, (span_symm_isPrime θ' Hlift.prime_U).radical,
        (span_symm_isPrime θ' Hlift.prime_V).radical]
      exact span_symm_inf_span_symm θ' Hlift.prime_V Hlift.not_mem
    · intro j' h1 h2
      have h0 : (chainCurve q n a ha i j').ker.ideal U' = ⊤ :=
        ker_ideal_eq_top_of_disjoint _ _ (hother j' h1 h2)
      rw [h0, Ideal.radical_top]
  refine curveChain_transversalCrossing_of_chart (multiSurface (q + 1) n a) q (chainCurve q n a ha i)
    (chainData q n a ha (singlePoints q n a ha) i) j.castSucc j.succ x U'
    (stalk_mem_of_eq τ' pr _ hy) (stalk_regularLocal_of_eq τ' pr Hlift.regular _ hy)
    (stalk_ringKrullDim_of_eq τ' pr Hlift.dim _ hy) _ _
    (stalk_span_germs_of_eq τ' pr _ _ Hlift.span_eq _ hy) hker ?_ ?_
  · rw [hkC]
    exact Ideal.mem_span_singleton_self _
  · rw [hkD]
    exact Ideal.mem_span_singleton_self _

/-- **Lane A1's hypothesis `TowerTransversal` for `S_{p,n}`.** -/
theorem towerTransversal : TowerTransversal q n a ha (singlePoints q n a ha) := by
  intro i j x hC hD
  by_cases hj : j.val + 1 < q
  · have hmC : chainMember.{0} q j.castSucc = Sum.inl ⟨j.val, by omega⟩ :=
      chainMember_of_lt q j.castSucc (by rw [Fin.coe_castSucc]; omega)
    have hmD : chainMember.{0} q j.succ = Sum.inl ⟨j.val + 1, hj⟩ :=
      chainMember_of_lt q j.succ (by rw [Fin.val_succ]; exact hj)
    have H := chainCrossingChart_later (tower q n a i) q j.val hj
    rw [← hmC, ← hmD] at H
    exact transversalCrossing_of_chainCrossingChart q n a ha i j _ _ _ _ H x hC hD
  · obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨j.val, by have := j.isLt; omega⟩
    have hjm : j.val = m := by have := j.isLt; omega
    have hmC : chainMember.{0} (m + 1) j.castSucc = Sum.inl ⟨m, by omega⟩ := by
      rw [chainMember_of_lt (m + 1) j.castSucc (by rw [Fin.coe_castSucc]; omega)]
      congr 1
      exact Fin.ext (by rw [Fin.coe_castSucc]; exact hjm)
    have hmD : chainMember.{0} (m + 1) j.succ = Sum.inr PUnit.unit :=
      chainMember_of_not_lt (m + 1) j.succ (by rw [Fin.val_succ]; omega)
    have H := chainCrossingChart_last (tower (m + 1) n a i) m
    rw [← hmC, ← hmD] at H
    exact transversalCrossing_of_chainCrossingChart (m + 1) n a ha i j _ _ _ _ H x hC hD

/-- **`Pic(C_{i1} ∪ ⋯ ∪ C_{iq} ∪ P_i) ≃* ℤ^{q+1}` on `S_{p,n}`, unconditionally.** -/
def towerChainPicardEquiv_unconditional (i : Fin n) :
    (towerChain q n a ha i).Pic ≃* (Fin (q + 1) → Multiplicative ℤ) :=
  towerChainPicardEquiv q n a ha (singlePoints q n a ha) (towerTransversal q n a ha) i

end Assembly

end KltDP.Examples.FrobeniusMultiCentreChainTransversal

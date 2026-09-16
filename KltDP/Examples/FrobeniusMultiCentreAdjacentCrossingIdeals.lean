import KltDP.Examples.FrobeniusMultiCentreChainTransversal

/-!
# Actual adjacent exceptional stalk ideals generate the ambient maximal ideal

This extracts the original embedded-curve crossing information from the accepted
translated chain charts. A chart is restricted to the existing cluster isomorphism
open and lifted by the actual tower projection. Its two original kernel ideals
therefore generate the ambient maximal ideal at every point common to the two
adjacent global exceptional curves. No projectivity, DVR, coefficient, or numerical
intersection premise is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing

universe u

namespace KltDP.Examples.FrobeniusMultiCentreAdjacentCrossingIdeals

open KltDP.Geometry
open FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
  FrobeniusExceptionalChainPicard FrobeniusExceptionalChainTransversal
  FrobeniusExceptionalChainTransversalLater FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint
  FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptional FrobeniusMultiCentreChainPicard
  FrobeniusMultiCentreChainTransversal

/-- The two original embedded kernel ideals of an actual crossing chart generate the stalk maximal ideal. -/
theorem kernel_stalk_sum_of_crossingChart {S Z Z' : Scheme.{u}}
    (C : Z ⟶ S) (D : Z' ⟶ S) {R : Type u} [CommRing R]
    (τ : Spec (CommRingCat.of R) ⟶ S) [IsOpenImmersion τ]
    (p : PrimeSpectrum R) (rU rV : R) (H : IsCrossingChart C D τ p rU rV)
    (x : S) (hx : x = τ.base p) :
    (C.ker.ideal ⟨τ ''ᵁ ⊤, chart_image_top_isAffineOpen τ⟩).map
        (S.presheaf.germ (τ ''ᵁ ⊤) x (stalk_mem_of_eq τ p x hx)).hom ⊔
      (D.ker.ideal ⟨τ ''ᵁ ⊤, chart_image_top_isAffineOpen τ⟩).map
        (S.presheaf.germ (τ ''ᵁ ⊤) x (stalk_mem_of_eq τ p x hx)).hom =
      maximalIdeal (S.presheaf.stalk x) := by
  rw [eq_span_symm_of_map_eq _ H.ideal_C, eq_span_symm_of_map_eq _ H.ideal_D]
  simp only [Ideal.map_span, Set.image_singleton]
  rw [← Ideal.span_union, Set.singleton_union]
  exact stalk_span_germs_of_eq τ p rU rV H.span_eq x hx

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)

include ha in
/-- Restrict and lift an accepted actual translated chart, retaining both original global kernels. -/
theorem exists_kernel_stalk_sum_of_chainCrossingChart (i : Fin n) (j : Fin q)
    {R : Type u} [CommRing R]
    (τ : Spec (CommRingCat.of R) ⟶ selectedStage (q + 1) (a i) (q + 1)) [IsOpenImmersion τ]
    (p : PrimeSpectrum R) (rU rV : R)
    (H : IsChainCrossingChart (tower q n a i) q (chainMember.{0} q j.castSucc)
      (chainMember.{0} q j.succ) τ p rU rV)
    (x : multiSurface (q + 1) n a)
    (hyC : x ∈ exceptionalSupport q n a i (chainMember.{0} q j.castSucc))
    (hyD : x ∈ exceptionalSupport q n a i (chainMember.{0} q j.succ)) :
    ∃ (U : (multiSurface (q + 1) n a).affineOpens) (hxU : x ∈ U.1),
      ((exceptionalCurveι q n a i (chainMember.{0} q j.castSucc)).ker.ideal U).map
          ((multiSurface (q + 1) n a).presheaf.germ U.1 x hxU).hom ⊔
        ((exceptionalCurveι q n a i (chainMember.{0} q j.succ)).ker.ideal U).map
          ((multiSurface (q + 1) n a).presheaf.germ U.1 x hxU).hom =
        maximalIdeal ((multiSurface (q + 1) n a).presheaf.stalk x) := by
  set π := towerProjection (q + 1) n a i
  rw [exceptionalSupport_eq] at hyC hyD
  have hπ : π.base x = τ.base p := H.eq_of_mem _ hyC hyD
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
  have hy : x = τ'.base pr := by
    apply eq_of_restrict_isIso π (isoOpen q n a i)
    · rw [hπ]
      exact hpV
    · rw [liftChart_base_mem]
      exact hτr pr
    · rw [hπ, liftChart_base_mem, awayChart_awayPoint]
  exact ⟨⟨τ' ''ᵁ ⊤, chart_image_top_isAffineOpen τ'⟩, stalk_mem_of_eq τ' pr x hy,
    kernel_stalk_sum_of_crossingChart _ _ τ' pr _ _ Hlift x hy⟩

include ha in
/-- Adjacent original global exceptional kernels generate the ambient maximal ideal at every common point. -/
theorem exists_adjacent_kernel_stalk_sum (i : Fin n) (j : Fin q)
    (x : multiSurface (q + 1) n a)
    (hyC : x ∈ exceptionalSupport q n a i (chainMember.{0} q j.castSucc))
    (hyD : x ∈ exceptionalSupport q n a i (chainMember.{0} q j.succ)) :
    ∃ (U : (multiSurface (q + 1) n a).affineOpens) (hxU : x ∈ U.1),
      ((exceptionalCurveι q n a i (chainMember.{0} q j.castSucc)).ker.ideal U).map
          ((multiSurface (q + 1) n a).presheaf.germ U.1 x hxU).hom ⊔
        ((exceptionalCurveι q n a i (chainMember.{0} q j.succ)).ker.ideal U).map
          ((multiSurface (q + 1) n a).presheaf.germ U.1 x hxU).hom =
        maximalIdeal ((multiSurface (q + 1) n a).presheaf.stalk x) := by
  by_cases hj : j.val + 1 < q
  · have hmC : chainMember.{0} q j.castSucc = Sum.inl ⟨j.val, by omega⟩ :=
      chainMember_of_lt q j.castSucc (by rw [Fin.coe_castSucc]; omega)
    have hmD : chainMember.{0} q j.succ = Sum.inl ⟨j.val + 1, hj⟩ :=
      chainMember_of_lt q j.succ (by rw [Fin.val_succ]; exact hj)
    have H := chainCrossingChart_later (tower q n a i) q j.val hj
    rw [← hmC, ← hmD] at H
    exact exists_kernel_stalk_sum_of_chainCrossingChart q n a ha i j _ _ _ _ H x hyC hyD
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
    exact exists_kernel_stalk_sum_of_chainCrossingChart (m + 1) n a ha i j _ _ _ _ H x hyC hyD

end KltDP.Examples.FrobeniusMultiCentreAdjacentCrossingIdeals

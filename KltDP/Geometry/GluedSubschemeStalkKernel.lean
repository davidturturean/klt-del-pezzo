import KltDP.Geometry.GluedIdealSheafKernel
import KltDP.Geometry.SurfaceRegularCharts

/-!
# Stalk kernels of glued closed subschemes, vanishing ideals of unions, chart germs

Generic lemmas for BRIEF20 (lane F), all independent of the contact tower.

* `stalkMap_gluedTo_ker_eq_map`: for an ideal sheaf `I` on `Y` with glued closed subscheme
  `ι : Z → Y`, the kernel of the stalk map `O_{Y, ι z} → O_{Z, z}` is the extension `I(U)·O_{Y, ι z}`
  of the ideal of `I` on any affine open `U ∋ ι z` (the accepted `stalkMap_gluedTo_ker_eq_span` without
  the principal-generator hypothesis, using the locality `map_ideal` of ideal-sheaf data).
* `vanishingIdeal_eq_iInf_ker_radical`: the vanishing ideal sheaf of a finite union of the ranges of
  closed immersions `f i : X i → Y` is `⨅ i, (f i).ker.radical` (Galois connection `support ⊣ vanishingIdeal`).
* `ker_ideal_eq_top_of_disjoint`: a quasi-compact morphism whose range misses an affine open has the unit
  kernel ideal there.
* `span_singleton_inf_span_singleton_of_prime`: `(a) ⊓ (b) = (ab)` when `(b)` is prime and `a ∉ (b)`.
* `chartSectionsEquiv j : Γ(Y, j ''ᵁ ⊤) ≃+* R` for an open immersion `j : Spec R ⟶ Y`, and the germ
  compatibility `openImmersionStalkLocalizationEquiv_germ`: the accepted stalk equivalence
  `O_{Y, j p} ≃+* R_p` sends the germ of a section `s` of the chart open to the image of the
  corresponding element of `R`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {Y : Scheme.{u}} (I : Y.IdealSheafData)

/-- The kernel of the stalk map of the glued closed subscheme at `z` is the extension of the ideal of
`I` on any affine open containing `ι z`. -/
theorem stalkMap_gluedTo_ker_eq_map {z : I.glueData.glued} (U : Y.affineOpens)
    (hy : I.gluedTo.base z ∈ U.1) :
    RingHom.ker (I.gluedTo.stalkMap z).hom =
      (I.ideal U).map (Y.presheaf.germ U.1 (I.gluedTo.base z) hy).hom := by
  apply le_antisymm
  · intro a ha
    obtain ⟨W, hzW, s, rfl⟩ := Y.presheaf.germ_exist (I.gluedTo.base z) a
    have ha' : I.gluedTo.stalkMap z (Y.presheaf.germ W (I.gluedTo.base z) hzW s) = 0 := ha
    rw [Scheme.stalkMap_germ_apply] at ha'
    have h0 : I.glueData.glued.presheaf.germ (I.gluedTo ⁻¹ᵁ W) z hzW (I.gluedTo.app W s) =
        I.glueData.glued.presheaf.germ ⊤ z trivial 0 := by
      rw [ha', map_zero]
    obtain ⟨W', hzW', iU, iV, hW'⟩ :=
      TopCat.Presheaf.germ_eq (V := ⊤) I.glueData.glued.presheaf z hzW trivial _ _ h0
    obtain ⟨V', hV'open, hV'⟩ :=
      (IsClosedImmersion.base_closed (f := I.gluedTo)).toIsEmbedding.toIsInducing.isOpen_iff.mp
        W'.isOpen
    let V'op : Y.Opens := ⟨V', hV'open⟩
    have hyV' : I.gluedTo.base z ∈ V'op := by
      have : z ∈ I.gluedTo.base ⁻¹' V' := by rw [hV']; exact hzW'
      exact this
    have hyU' : I.gluedTo.base z ∈ ((U.1 ⊓ W ⊓ V'op : Y.Opens) : Set Y) := ⟨⟨hy, hzW⟩, hyV'⟩
    obtain ⟨_, ⟨V, hVaff, rfl⟩, hyV, hVle⟩ :=
      (isBasis_affine_open Y).exists_subset_of_mem_open hyU' (U.1 ⊓ W ⊓ V'op).2
    have hVU : V ≤ U.1 := fun x hx => (hVle hx).1.1
    have hVW : V ≤ W := fun x hx => (hVle hx).1.2
    have hVV' : V ≤ V'op := fun x hx => (hVle hx).2
    have hj₁ : I.gluedTo ⁻¹ᵁ V ≤ W' := by
      intro w hw
      have : w ∈ I.gluedTo.base ⁻¹' V' := hVV' hw
      show w ∈ (W' : Set I.glueData.glued)
      rw [← hV']
      exact this
    have hmem : Y.presheaf.map (homOfLE hVW).op s ∈ RingHom.ker (I.gluedTo.app V).hom := by
      rw [RingHom.mem_ker]
      have hnat : I.gluedTo.app V (Y.presheaf.map (homOfLE hVW).op s) =
          I.glueData.glued.presheaf.map ((Opens.map I.gluedTo.base).map (homOfLE hVW)).op
            (I.gluedTo.app W s) :=
        ConcreteCategory.congr_hom (I.gluedTo.naturality ((homOfLE hVW).op : op W ⟶ op V)) s
      have hfac : (Opens.map I.gluedTo.base).map (homOfLE hVW) =
          (homOfLE hj₁ : I.gluedTo ⁻¹ᵁ V ⟶ W') ≫ iU := Subsingleton.elim _ _
      change I.gluedTo.app V (Y.presheaf.map (homOfLE hVW).op s) = 0
      rw [hnat, hfac, op_comp, Functor.map_comp]
      erw [CommRingCat.comp_apply]
      rw [hW', map_zero, map_zero]
    have hker := I.ker_gluedTo_app ⟨V, hVaff⟩
    change RingHom.ker (I.gluedTo.app V).hom = I.ideal ⟨V, hVaff⟩ at hker
    rw [hker, ← I.map_ideal (U := ⟨V, hVaff⟩) (V := U) hVU] at hmem
    have hgerm := Ideal.mem_map_of_mem (Y.presheaf.germ V (I.gluedTo.base z) hyV).hom hmem
    rw [Ideal.map_map] at hgerm
    have hcomp : (Y.presheaf.germ V (I.gluedTo.base z) hyV).hom.comp
        (Y.presheaf.map (homOfLE hVU).op).hom =
        (Y.presheaf.germ U.1 (I.gluedTo.base z) hy).hom := by
      rw [← CommRingCat.hom_comp]
      exact congrArg CommRingCat.Hom.hom
        (TopCat.Presheaf.germ_res Y.presheaf (homOfLE hVU) (I.gluedTo.base z) hyV)
    have hs : Y.presheaf.germ V (I.gluedTo.base z) hyV (Y.presheaf.map (homOfLE hVW).op s) =
        Y.presheaf.germ W (I.gluedTo.base z) hzW s :=
      Y.presheaf.germ_res_apply (homOfLE hVW) (I.gluedTo.base z) hyV s
    rw [← hcomp, ← hs]
    exact hgerm
  · refine Ideal.map_le_iff_le_comap.mpr fun d hd => ?_
    have happ : I.gluedTo.app U.1 d = 0 := by
      have h := I.ker_gluedTo_app U
      have : d ∈ RingHom.ker (I.gluedTo.app U.1).hom := by rw [h]; exact hd
      exact this
    show I.gluedTo.stalkMap z (Y.presheaf.germ U.1 (I.gluedTo.base z) hy d) = 0
    rw [Scheme.stalkMap_germ_apply, happ, map_zero]

/-- The vanishing ideal sheaf of a finite union of ranges of closed immersions is the infimum of the
radicals of their kernels. -/
theorem vanishingIdeal_eq_iInf_ker_radical {ι : Type*} [Finite ι] {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ Y) [∀ i, IsClosedImmersion (f i)] (Z : Closeds Y)
    (hZ : (Z : Set Y) = ⋃ i, Set.range (f i).base) :
    vanishingIdeal Z = ⨅ i, (f i).ker.radical := by
  apply le_antisymm
  · refine le_iInf fun i => ?_
    rw [← vanishingIdeal_support]
    apply vanishingIdeal_antimono
    rw [← SetLike.coe_subset_coe, Scheme.Hom.support_ker, hZ,
      (f i).isClosedEmbedding.isClosed_range.closure_eq]
    exact Set.subset_iUnion (fun i => Set.range (f i).base) i
  · rw [← subset_support_iff_le_vanishingIdeal, hZ]
    refine Set.iUnion_subset fun i => ?_
    refine (f i).range_subset_ker_support.trans ?_
    have h1 : ((f i).ker.support : Set Y) = (f i).ker.radical.support := by
      rw [support_radical]
    rw [h1]
    exact SetLike.coe_subset_coe.mpr (support_antitone (iInf_le (fun i => (f i).ker.radical) i))

end AlgebraicGeometry.Scheme.IdealSheafData

namespace KltDP.Geometry

/-- A quasi-compact morphism whose range misses an affine open `U` has the unit kernel ideal on `U`. -/
theorem ker_ideal_eq_top_of_disjoint {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (U : Y.affineOpens) (h : ∀ x, f.base x ∉ U.1) : f.ker.ideal U = ⊤ := by
  rw [Scheme.Hom.ker_apply, Ideal.eq_top_iff_one, RingHom.mem_ker]
  have hb : f ⁻¹ᵁ U.1 = ⊥ := by
    apply Opens.ext
    rw [Opens.coe_bot]
    exact Set.eq_empty_iff_forall_not_mem.mpr fun y hy => h y hy
  haveI : Subsingleton Γ(X, f ⁻¹ᵁ U.1) :=
    CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hb)
  exact Subsingleton.elim _ _

/-- `(a) ⊓ (b) = (a b)` when `(b)` is prime and `a ∉ (b)`. -/
theorem span_singleton_inf_span_singleton_of_prime {R : Type*} [CommRing R] {a b : R}
    (hb : (Ideal.span {b}).IsPrime) (hab : a ∉ Ideal.span {b}) :
    Ideal.span {a} ⊓ Ideal.span {b} = Ideal.span {a * b} := by
  apply le_antisymm
  · rintro x ⟨hxa, hxb⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hxa
    have hc : c ∈ Ideal.span {b} := (hb.mem_or_mem hxb).resolve_left hab
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hc
    exact Ideal.mem_span_singleton.mpr ⟨d, by ring⟩
  · exact le_inf (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right a b))
      (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left b a))

section Chart

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (j : Spec (CommRingCat.of R) ⟶ Y)
  [IsOpenImmersion j]

/-- Every point of the chart lies in the chart open `j ''ᵁ ⊤`. -/
theorem mem_chart_image_top (p : PrimeSpectrum R) : j.base p ∈ j ''ᵁ ⊤ := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact ⟨p, rfl⟩

/-- The chart open is affine. -/
theorem chart_image_top_isAffineOpen : IsAffineOpen (j ''ᵁ ⊤) :=
  (isAffineOpen_top (Spec (CommRingCat.of R))).image_of_isOpenImmersion j

/-- The sections of the chart open, identified with the chart ring through the open immersion and
`Γ(Spec R, ⊤) ≅ R`. -/
def chartSectionsEquiv : Γ(Y, j ''ᵁ ⊤) ≃+* R :=
  (j.appIso ⊤).commRingCatIsoToRingEquiv.trans
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv

theorem chartSectionsEquiv_apply (s : Γ(Y, j ''ᵁ ⊤)) :
    chartSectionsEquiv j s = (Scheme.ΓSpecIso (CommRingCat.of R)).hom ((j.appIso ⊤).hom s) := rfl

theorem chartSectionsEquiv_symm_apply (r : R) :
    (chartSectionsEquiv j).symm r = (j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) :=
  rfl

/-- The ideal computed in the chart ring through the two inverse isomorphisms (the accepted pattern
`comap (ΓSpecIso).inv (comap (appIso ⊤).inv J)`) is the preimage of `J` under the inverse of
`chartSectionsEquiv`. -/
theorem comap_inv_comap_inv_eq_comap_symm (J : Ideal Γ(Y, j ''ᵁ ⊤)) :
    Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
        (Ideal.comap (j.appIso ⊤).inv.hom J) = J.comap (chartSectionsEquiv j).symm :=
  Ideal.ext fun _ => Iff.rfl

/-- The same ideal is the image of `J` under `chartSectionsEquiv`. -/
theorem comap_inv_comap_inv_eq_map (J : Ideal Γ(Y, j ''ᵁ ⊤)) :
    Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
        (Ideal.comap (j.appIso ⊤).inv.hom J) = J.map (chartSectionsEquiv j) := by
  rw [comap_inv_comap_inv_eq_comap_symm, Ideal.comap_symm]

/-- The germ of a section of the chart open at a chart point, under the accepted stalk equivalence,
is the image of the corresponding element of the chart ring in the localisation. -/
theorem openImmersionStalkLocalizationEquiv_germ (p : PrimeSpectrum R) (s : Γ(Y, j ''ᵁ ⊤)) :
    openImmersionStalkLocalizationEquiv j p
        (Y.presheaf.germ (j ''ᵁ ⊤) (j.base p) (mem_chart_image_top j p) s) =
      algebraMap R (Localization.AtPrime p.asIdeal) (chartSectionsEquiv j s) := by
  change specStalkLocalizationEquiv R p
    (j.stalkMap p (Y.presheaf.germ (j ''ᵁ ⊤) (j.base p) (mem_chart_image_top j p) s)) = _
  rw [Scheme.stalkMap_germ_apply]
  have h1' : (j.appIso ⊤).hom s = (Spec (CommRingCat.of R)).presheaf.map
      (eqToHom (Scheme.Hom.preimage_image_eq j ⊤).symm).op (j.app (j ''ᵁ ⊤) s) := by
    rw [Scheme.Hom.appIso_hom]
    rfl
  have h1 : (Spec (CommRingCat.of R)).presheaf.germ (j ⁻¹ᵁ j ''ᵁ ⊤) p (mem_chart_image_top j p)
        (j.app (j ''ᵁ ⊤) s) =
      (Spec (CommRingCat.of R)).presheaf.germ ⊤ p trivial ((j.appIso ⊤).hom s) := by
    rw [h1', TopCat.Presheaf.germ_res_apply]
  have h2 : (j.appIso ⊤).hom s = StructureSheaf.toOpen R ⊤ (chartSectionsEquiv j s) := by
    change _ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ((j.appIso ⊤).hom s))
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
    rfl
  have h3 : (Spec (CommRingCat.of R)).presheaf.germ (j ⁻¹ᵁ j ''ᵁ ⊤) p (mem_chart_image_top j p)
        (j.app (j ''ᵁ ⊤) s) = StructureSheaf.toStalk R p (chartSectionsEquiv j s) := by
    rw [h1, h2]
    exact StructureSheaf.germ_toOpen R ⊤ p trivial _
  rw [h3]
  exact StructureSheaf.stalkToFiberRingHom_toStalk R p _

/-- Inverse form of the germ compatibility. -/
theorem openImmersionStalkLocalizationEquiv_symm_algebraMap (p : PrimeSpectrum R) (r : R) :
    (openImmersionStalkLocalizationEquiv j p).symm (algebraMap R (Localization.AtPrime p.asIdeal) r) =
      Y.presheaf.germ (j ''ᵁ ⊤) (j.base p) (mem_chart_image_top j p)
        ((chartSectionsEquiv j).symm r) := by
  apply (openImmersionStalkLocalizationEquiv j p).injective
  rw [RingEquiv.apply_symm_apply, openImmersionStalkLocalizationEquiv_germ,
    RingEquiv.apply_symm_apply]

/-- **Transport of kernel ideals along a pullback square and compatible charts.** If `g' : Z' ⟶ S'` is the
base change of `g : Z ⟶ S` along `π : S' ⟶ S`, and the chart `τ : Spec R ⟶ S'` lies over the chart
`σ : Spec R ⟶ S` (`τ ≫ π = σ`), then the kernel ideals of `g'` and `g` on the two chart opens agree in the
chart ring `R`. -/
theorem ker_ideal_map_eq_of_isPullback {S S' Z Z' : Scheme.{u}} {R : Type u} [CommRing R]
    (π : S' ⟶ S) (g : Z ⟶ S) (g' : Z' ⟶ S') (e : Z' ⟶ Z) [QuasiCompact g] [QuasiCompact g']
    (H : IsPullback g' e π g) (σ : Spec (CommRingCat.of R) ⟶ S) (τ : Spec (CommRingCat.of R) ⟶ S')
    [IsOpenImmersion σ] [IsOpenImmersion τ] (hτ : τ ≫ π = σ) :
    (g'.ker.ideal ⟨τ ''ᵁ ⊤, chart_image_top_isAffineOpen τ⟩).map (chartSectionsEquiv τ) =
      (g.ker.ideal ⟨σ ''ᵁ ⊤, chart_image_top_isAffineOpen σ⟩).map (chartSectionsEquiv σ) := by
  have H₁ : IsPullback (pullback.fst τ g') (pullback.snd τ g') τ g' := IsPullback.of_hasPullback τ g'
  have H₂ : IsPullback (pullback.fst τ g') (pullback.snd τ g' ≫ e) σ g := by
    have h := H₁.paste_vert H
    rwa [hτ] at h
  have e1 := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion g' (pullback.fst τ g')
    (pullback.snd τ g') τ H₁ ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩
  have e2 := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion g (pullback.fst τ g')
    (pullback.snd τ g' ≫ e) σ H₂ ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩
  rw [← comap_inv_comap_inv_eq_map, ← comap_inv_comap_inv_eq_map, ← e1, ← e2]

/-- An ideal whose image under a ring isomorphism is principal is principal, generated by the preimage
of the generator. -/
theorem eq_span_symm_of_map_eq {Γ R : Type*} [CommRing Γ] [CommRing R] (θ : Γ ≃+* R) {J : Ideal Γ}
    {r : R} (h : J.map θ = Ideal.span {r}) : J = Ideal.span {θ.symm r} := by
  rw [← Ideal.comap_map_of_bijective θ θ.bijective (I := J), h, ← Ideal.map_symm, Ideal.map_span,
    Set.image_singleton]

/-- An infimum in which all but two terms are `⊤`. -/
theorem iInf_eq_inf_of_top {ι : Type*} {L : Type*} [CompleteLattice L] (J : ι → L) (a b : ι)
    (h : ∀ i, i ≠ a → i ≠ b → J i = ⊤) : ⨅ i, J i = J a ⊓ J b := by
  apply le_antisymm
  · exact le_inf (iInf_le J a) (iInf_le J b)
  · refine le_iInf fun i => ?_
    by_cases ha : i = a
    · subst ha
      exact inf_le_left
    by_cases hb : i = b
    · subst hb
      exact inf_le_right
    · rw [h i ha hb]
      exact le_top

end Chart

end KltDP.Geometry

import KltDP.Geometry.SchematicImageToImageIso

/-!
# A morphism of curves that is an isomorphism over a puncture and has a common affine chart

Let `f : X' ⟶ X` be a morphism over a blowdown `π : S' ⟶ S` of the ambient schemes
(`f ≫ ι = ι' ≫ π` for closed immersions `ι' : X' ⟶ S'`, `ι : X ⟶ S`). Suppose that over an open
`P ⊆ S` (the complement of the centre) the restricted map `g` is an isomorphism compatible with
`f`, that there are open charts `c' : W ⟶ X'`, `c : W ⟶ X` with `c' ≫ f = c`, that the chart and the
puncture cover both curves, and that `f` is surjective on points. Then `f` is an isomorphism
(`isIso_of_pieces`): over the puncture `f` is inverted by `g⁻¹`, over the chart `f` is inverted by the
chart parametrisation (a point of `X'` over the chart is a chart point or a puncture point, and puncture
points are separated by `g`), and `IsOpenImmersion` is local on the target.

This is lane F's `strictToFiber_isIso` argument made generic; it is applied to the step
projections of the strict transforms of the graph and of the fibre.

Also: the relative closedness of a closed curve in an open chart
(`mem_range_comp_of_mem_closure`), and ranges along isomorphisms (`range_comp_base_of_isIso`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.IsoOfPunctureAndChart

/-- Points of an isomorphism's source are determined by their images. -/
theorem base_injective_of_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    Function.Injective g.base := by
  intro a b h
  have h' := congrArg (inv g).base h
  rw [← Scheme.comp_base_apply, ← Scheme.comp_base_apply, IsIso.hom_inv_id] at h'
  exact h'

/-- The range of `e ≫ h` for an isomorphism `e` is the range of `h`. -/
theorem range_comp_base_of_isIso {X Y Z : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (h : Y ⟶ Z) :
    Set.range (e ≫ h).base = Set.range h.base := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e.base x, (Scheme.comp_base_apply e h x).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(inv e).base y, ?_⟩
    rw [Scheme.comp_base_apply, ← Scheme.comp_base_apply (inv e) e, IsIso.inv_hom_id]
    rfl

/-- **Relative closedness**: a point of the closure of a closed curve of an open chart which lies
in the chart is on the curve. -/
theorem mem_range_comp_of_mem_closure {Z X S : Scheme.{u}} (g : Z ⟶ X) (e : X ⟶ S)
    [IsClosedImmersion g] [IsOpenImmersion e] (y : S)
    (hy : y ∈ closure (Set.range (g ≫ e).base)) (hy' : y ∈ Set.range e.base) :
    y ∈ Set.range (g ≫ e).base := by
  obtain ⟨x, rfl⟩ := hy'
  have hpre : e.base ⁻¹' Set.range (g ≫ e).base = Set.range g.base := by
    ext z
    constructor
    · rintro ⟨w, hw⟩
      rw [Scheme.comp_base_apply] at hw
      exact ⟨w, e.isOpenEmbedding.injective hw⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w, Scheme.comp_base_apply g e w⟩
  have hx : x ∈ e.base ⁻¹' closure (Set.range (g ≫ e).base) := hy
  rw [e.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage e.continuous, hpre,
    g.isClosedEmbedding.isClosed_range.closure_eq] at hx
  obtain ⟨w, hw⟩ := hx
  exact ⟨w, by rw [Scheme.comp_base_apply, hw]⟩

variable {X' X S' S : Scheme.{u}}

/-- Membership in the source puncture is membership of the image in the target puncture. -/
theorem mem_puncture_iff (f : X' ⟶ X) (ι' : X' ⟶ S') (ι : X ⟶ S) (π : S' ⟶ S)
    (hsq : f ≫ ι = ι' ≫ π) (P : S.Opens) (x : X') :
    x ∈ ι' ⁻¹ᵁ (π ⁻¹ᵁ P) ↔ f.base x ∈ ι ⁻¹ᵁ P := by
  change π.base (ι'.base x) ∈ P ↔ ι.base (f.base x) ∈ P
  have h1 : π.base (ι'.base x) = (ι' ≫ π).base x := (Scheme.comp_base_apply ι' π x).symm
  have h2 : ι.base (f.base x) = (f ≫ ι).base x := (Scheme.comp_base_apply f ι x).symm
  rw [h1, h2, hsq]

/-! ## The puncture -/

section Puncture

variable (f : X' ⟶ X) (ι' : X' ⟶ S') (ι : X ⟶ S) (π : S' ⟶ S) (P : S.Opens)
variable (g : (ι' ⁻¹ᵁ (π ⁻¹ᵁ P)).toScheme ⟶ (ι ⁻¹ᵁ P).toScheme) [IsIso g]
variable (hg : g ≫ (ι ⁻¹ᵁ P).ι = (ι' ⁻¹ᵁ (π ⁻¹ᵁ P)).ι ≫ f)

/-- The section of `f` over the puncture: the inverse of `g` followed by the inclusion. -/
def punctureSection : (ι ⁻¹ᵁ P).toScheme ⟶ X' := inv g ≫ (ι' ⁻¹ᵁ (π ⁻¹ᵁ P)).ι

include hg in
theorem punctureSection_comp : punctureSection ι' ι π P g ≫ f = (ι ⁻¹ᵁ P).ι := by
  rw [punctureSection, Category.assoc, ← hg, IsIso.inv_hom_id_assoc]

include hg in
theorem range_punctureSection_subset :
    Set.range (punctureSection ι' ι π P g).base ⊆ Set.range (f ⁻¹ᵁ (ι ⁻¹ᵁ P)).ι.base := by
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι]
  change f.base ((punctureSection ι' ι π P g).base y) ∈ ι ⁻¹ᵁ P
  rw [← Scheme.comp_base_apply, punctureSection_comp f ι' ι π P g hg, Scheme.Opens.ι_base_apply]
  exact y.2

/-- The puncture section, into the part of `X'` over the puncture. -/
def punctureSection' : (ι ⁻¹ᵁ P).toScheme ⟶ (f ⁻¹ᵁ (ι ⁻¹ᵁ P)).toScheme :=
  IsOpenImmersion.lift (f ⁻¹ᵁ (ι ⁻¹ᵁ P)).ι (punctureSection ι' ι π P g)
    (range_punctureSection_subset f ι' ι π P g hg)

theorem punctureSection'_ι :
    punctureSection' f ι' ι π P g hg ≫ (f ⁻¹ᵁ (ι ⁻¹ᵁ P)).ι = punctureSection ι' ι π P g :=
  IsOpenImmersion.lift_fac _ _ _

theorem punctureSection'_isOpenImmersion : IsOpenImmersion (punctureSection' f ι' ι π P g hg) := by
  haveI : IsOpenImmersion (punctureSection' f ι' ι π P g hg ≫ (f ⁻¹ᵁ (ι ⁻¹ᵁ P)).ι) := by
    rw [punctureSection'_ι, punctureSection]
    infer_instance
  exact IsOpenImmersion.of_comp _ (f ⁻¹ᵁ (ι ⁻¹ᵁ P)).ι

/-- The section hits every point over the puncture. -/
theorem punctureSection'_surjective (hsq : f ≫ ι = ι' ≫ π) :
    Function.Surjective (punctureSection' f ι' ι π P g hg).base := by
  intro w
  have hw : w.1 ∈ ι' ⁻¹ᵁ (π ⁻¹ᵁ P) := (mem_puncture_iff f ι' ι π hsq P w.1).mpr w.2
  have key : (punctureSection ι' ι π P g).base (g.base ⟨w.1, hw⟩) = w.1 := by
    show (inv g ≫ (ι' ⁻¹ᵁ (π ⁻¹ᵁ P)).ι).base (g.base ⟨w.1, hw⟩) = w.1
    rw [Scheme.comp_base_apply, ← Scheme.comp_base_apply g (inv g), IsIso.hom_inv_id]
    rfl
  refine ⟨g.base ⟨w.1, hw⟩, (f ⁻¹ᵁ (ι ⁻¹ᵁ P)).ι.isOpenEmbedding.injective ?_⟩
  rw [← Scheme.comp_base_apply, punctureSection'_ι, key]
  rfl

/-- The puncture section is an isomorphism onto the part of `X'` over the puncture. -/
def punctureSectionIso (hsq : f ≫ ι = ι' ≫ π) :
    (ι ⁻¹ᵁ P).toScheme ≅ (f ⁻¹ᵁ (ι ⁻¹ᵁ P)).toScheme :=
  haveI := punctureSection'_isOpenImmersion f ι' ι π P g hg
  IsOpenImmersion.isoOfRangeEq (punctureSection' f ι' ι π P g hg) (𝟙 _)
    ((Set.range_eq_univ.mpr (punctureSection'_surjective f ι' ι π P g hg hsq)).trans
      (Set.range_eq_univ.mpr (fun x => ⟨x, rfl⟩)).symm)

theorem punctureSectionIso_hom (hsq : f ≫ ι = ι' ≫ π) :
    (punctureSectionIso f ι' ι π P g hg hsq).hom = punctureSection' f ι' ι π P g hg := by
  haveI := punctureSection'_isOpenImmersion f ι' ι π P g hg
  have h := IsOpenImmersion.isoOfRangeEq_hom_fac (punctureSection' f ι' ι π P g hg) (𝟙 _)
    ((Set.range_eq_univ.mpr (punctureSection'_surjective f ι' ι π P g hg hsq)).trans
      (Set.range_eq_univ.mpr (fun x => ⟨x, rfl⟩)).symm)
  rwa [Category.comp_id] at h

theorem punctureSection'_isIso (hsq : f ≫ ι = ι' ≫ π) :
    IsIso (punctureSection' f ι' ι π P g hg) := by
  rw [← punctureSectionIso_hom f ι' ι π P g hg hsq]
  infer_instance

theorem punctureSection'_restrict :
    punctureSection' f ι' ι π P g hg ≫ (f ∣_ (ι ⁻¹ᵁ P)) = 𝟙 _ := by
  apply (cancel_mono (ι ⁻¹ᵁ P).ι).mp
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, punctureSection'_ι,
    punctureSection_comp f ι' ι π P g hg, Category.id_comp]

include g hg in
/-- **`f` is an isomorphism over the puncture.** -/
theorem restrict_puncture_isIso (hsq : f ≫ ι = ι' ≫ π) : IsIso (f ∣_ (ι ⁻¹ᵁ P)) := by
  haveI := punctureSection'_isIso f ι' ι π P g hg hsq
  have h : f ∣_ (ι ⁻¹ᵁ P) = inv (punctureSection' f ι' ι π P g hg) := by
    rw [← IsIso.inv_hom_id_assoc (punctureSection' f ι' ι π P g hg) (f ∣_ (ι ⁻¹ᵁ P)),
      punctureSection'_restrict, Category.comp_id]
  rw [h]
  infer_instance

end Puncture

/-! ## The chart -/

section Chart

variable (f : X' ⟶ X) (ι' : X' ⟶ S') (ι : X ⟶ S) (π : S' ⟶ S) (hsq : f ≫ ι = ι' ≫ π) (P : S.Opens)
variable (g : (ι' ⁻¹ᵁ (π ⁻¹ᵁ P)).toScheme ⟶ (ι ⁻¹ᵁ P).toScheme) [IsIso g]
variable (hg : g ≫ (ι ⁻¹ᵁ P).ι = (ι' ⁻¹ᵁ (π ⁻¹ᵁ P)).ι ≫ f)
variable {W : Scheme.{u}} (c' : W ⟶ X') (c : W ⟶ X) [IsOpenImmersion c'] [IsOpenImmersion c]
variable (hc : c' ≫ f = c)
variable (hcover' : ∀ x : X', x ∈ Set.range c'.base ∨ x ∈ ι' ⁻¹ᵁ (π ⁻¹ᵁ P))

/-- The chart of `X` as an isomorphism onto its range. -/
def chartIso : W ≅ c.opensRange.toScheme :=
  IsOpenImmersion.isoOfRangeEq c c.opensRange.ι (by rw [Scheme.Opens.range_ι]; rfl)

theorem chartIso_hom_ι : (chartIso c).hom ≫ c.opensRange.ι = c :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The chart section of `f`. -/
def chartSection : c.opensRange.toScheme ⟶ X' := (chartIso c).inv ≫ c'

omit [IsOpenImmersion c'] in
include hc in
theorem chartSection_comp : chartSection c' c ≫ f = c.opensRange.ι := by
  rw [chartSection, Category.assoc, hc, ← Iso.inv_hom_id_assoc (chartIso c) c.opensRange.ι,
    chartIso_hom_ι]

omit [IsOpenImmersion c'] in
include hc in
theorem range_chartSection_subset :
    Set.range (chartSection c' c).base ⊆ Set.range (f ⁻¹ᵁ c.opensRange).ι.base := by
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι]
  change f.base ((chartSection c' c).base y) ∈ c.opensRange
  rw [← Scheme.comp_base_apply, chartSection_comp f c' c hc, Scheme.Opens.ι_base_apply]
  exact y.2

/-- The chart section, into the part of `X'` over the chart. -/
def chartSection' : c.opensRange.toScheme ⟶ (f ⁻¹ᵁ c.opensRange).toScheme :=
  IsOpenImmersion.lift (f ⁻¹ᵁ c.opensRange).ι (chartSection c' c) (range_chartSection_subset f c' c hc)

omit [IsOpenImmersion c'] in
theorem chartSection'_ι :
    chartSection' f c' c hc ≫ (f ⁻¹ᵁ c.opensRange).ι = chartSection c' c :=
  IsOpenImmersion.lift_fac _ _ _

theorem chartSection'_isOpenImmersion : IsOpenImmersion (chartSection' f c' c hc) := by
  haveI : IsOpenImmersion (chartSection' f c' c hc ≫ (f ⁻¹ᵁ c.opensRange).ι) := by
    rw [chartSection'_ι, chartSection]
    infer_instance
  exact IsOpenImmersion.of_comp _ (f ⁻¹ᵁ c.opensRange).ι

omit [IsOpenImmersion c'] [IsOpenImmersion c] in
include ι' ι π hsq P g hg hc hcover' in
/-- A point of `X'` over the chart is a chart point: either directly, or it is a puncture point
with the same image as a chart point, and `f` separates puncture points. -/
theorem mem_range_chart_of_mem (x : X') (hx : f.base x ∈ Set.range c.base) :
    x ∈ Set.range c'.base := by
  rcases hcover' x with h | h
  · exact h
  · obtain ⟨t, ht⟩ := hx
    have hft : f.base (c'.base t) = f.base x := by
      rw [← Scheme.comp_base_apply, hc, ht]
    have h0 : c'.base t ∈ ι' ⁻¹ᵁ (π ⁻¹ᵁ P) := by
      rw [mem_puncture_iff f ι' ι π hsq P, hft]
      exact (mem_puncture_iff f ι' ι π hsq P x).mp h
    have hg' : ∀ z : (ι' ⁻¹ᵁ (π ⁻¹ᵁ P)).toScheme,
        f.base ((ι' ⁻¹ᵁ (π ⁻¹ᵁ P)).ι.base z) = (ι ⁻¹ᵁ P).ι.base (g.base z) := by
      intro z
      rw [← Scheme.comp_base_apply, ← hg, Scheme.comp_base_apply]
    have heq : g.base ⟨c'.base t, h0⟩ = g.base ⟨x, h⟩ := by
      apply (ι ⁻¹ᵁ P).ι.isOpenEmbedding.injective
      rw [← hg', ← hg']
      exact hft
    have heq' := base_injective_of_isIso g heq
    exact ⟨t, congrArg Subtype.val heq'⟩

omit [IsOpenImmersion c'] in
include ι' ι π hsq P g hg hcover' in
theorem chartSection'_surjective : Function.Surjective (chartSection' f c' c hc).base := by
  intro w
  obtain ⟨t, ht⟩ := mem_range_chart_of_mem f ι' ι π hsq P g hg c' c hc hcover' w.1 w.2
  refine ⟨(chartIso c).hom.base t, (f ⁻¹ᵁ c.opensRange).ι.isOpenEmbedding.injective ?_⟩
  rw [← Scheme.comp_base_apply, chartSection'_ι, chartSection, Scheme.comp_base_apply,
    ← Scheme.comp_base_apply (chartIso c).hom (chartIso c).inv, Iso.hom_inv_id]
  exact ht

/-- The chart section is an isomorphism onto the part of `X'` over the chart. -/
def chartSectionIso : c.opensRange.toScheme ≅ (f ⁻¹ᵁ c.opensRange).toScheme :=
  haveI := chartSection'_isOpenImmersion f c' c hc
  IsOpenImmersion.isoOfRangeEq (chartSection' f c' c hc) (𝟙 _)
    ((Set.range_eq_univ.mpr (chartSection'_surjective f ι' ι π hsq P g hg c' c hc hcover')).trans
      (Set.range_eq_univ.mpr (fun x => ⟨x, rfl⟩)).symm)

theorem chartSectionIso_hom :
    (chartSectionIso f ι' ι π hsq P g hg c' c hc hcover').hom = chartSection' f c' c hc := by
  haveI := chartSection'_isOpenImmersion f c' c hc
  have h := IsOpenImmersion.isoOfRangeEq_hom_fac (chartSection' f c' c hc) (𝟙 _)
    ((Set.range_eq_univ.mpr (chartSection'_surjective f ι' ι π hsq P g hg c' c hc hcover')).trans
      (Set.range_eq_univ.mpr (fun x => ⟨x, rfl⟩)).symm)
  rwa [Category.comp_id] at h

include ι' ι π hsq P g hg hcover' in
theorem chartSection'_isIso : IsIso (chartSection' f c' c hc) := by
  rw [← chartSectionIso_hom f ι' ι π hsq P g hg c' c hc hcover']
  infer_instance

omit [IsOpenImmersion c'] in
theorem chartSection'_restrict : chartSection' f c' c hc ≫ (f ∣_ c.opensRange) = 𝟙 _ := by
  apply (cancel_mono c.opensRange.ι).mp
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, chartSection'_ι,
    chartSection_comp f c' c hc, Category.id_comp]

include ι' ι π hsq P g hg c' hc hcover' in
/-- **`f` is an isomorphism over the chart.** -/
theorem restrict_chart_isIso : IsIso (f ∣_ c.opensRange) := by
  haveI := chartSection'_isIso f ι' ι π hsq P g hg c' c hc hcover'
  have h : f ∣_ c.opensRange = inv (chartSection' f c' c hc) := by
    rw [← IsIso.inv_hom_id_assoc (chartSection' f c' c hc) (f ∣_ c.opensRange),
      chartSection'_restrict, Category.comp_id]
  rw [h]
  infer_instance

end Chart

/-! ## The assembly -/

/-- The two target opens: the puncture and the chart. -/
def coverOpens (ι : X ⟶ S) (P : S.Opens) {W : Scheme.{u}} (c : W ⟶ X) [IsOpenImmersion c] :
    Bool → X.Opens
  | true => ι ⁻¹ᵁ P
  | false => c.opensRange

theorem iSup_coverOpens (ι : X ⟶ S) (P : S.Opens) {W : Scheme.{u}} (c : W ⟶ X) [IsOpenImmersion c]
    (hcover : ∀ y : X, y ∈ Set.range c.base ∨ y ∈ ι ⁻¹ᵁ P) :
    iSup (coverOpens ι P c) = ⊤ := by
  apply eq_top_iff.mpr
  intro y _
  show y ∈ iSup (coverOpens ι P c)
  rw [Opens.mem_iSup]
  rcases hcover y with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

/-- **`f` is an isomorphism**: an open immersion (locally on the target, over the puncture and
over the chart) which is surjective on points. -/
theorem isIso_of_pieces (f : X' ⟶ X) (ι' : X' ⟶ S') (ι : X ⟶ S) (π : S' ⟶ S)
    (hsq : f ≫ ι = ι' ≫ π) (P : S.Opens)
    (g : (ι' ⁻¹ᵁ (π ⁻¹ᵁ P)).toScheme ⟶ (ι ⁻¹ᵁ P).toScheme) [IsIso g]
    (hg : g ≫ (ι ⁻¹ᵁ P).ι = (ι' ⁻¹ᵁ (π ⁻¹ᵁ P)).ι ≫ f)
    {W : Scheme.{u}} (c' : W ⟶ X') (c : W ⟶ X) [IsOpenImmersion c'] [IsOpenImmersion c]
    (hc : c' ≫ f = c)
    (hcover' : ∀ x : X', x ∈ Set.range c'.base ∨ x ∈ ι' ⁻¹ᵁ (π ⁻¹ᵁ P))
    (hcover : ∀ y : X, y ∈ Set.range c.base ∨ y ∈ ι ⁻¹ᵁ P)
    (hsurj : Function.Surjective f.base) : IsIso f := by
  haveI : IsOpenImmersion f := by
    apply IsLocalAtTarget.of_iSup_eq_top (P := @IsOpenImmersion) (coverOpens ι P c)
      (iSup_coverOpens ι P c hcover)
    intro b
    cases b
    · show IsOpenImmersion (f ∣_ c.opensRange)
      haveI := restrict_chart_isIso f ι' ι π hsq P g hg c' c hc hcover'
      infer_instance
    · show IsOpenImmersion (f ∣_ (ι ⁻¹ᵁ P))
      haveI := restrict_puncture_isIso f ι' ι π P g hg hsq
      infer_instance
  have h := IsOpenImmersion.isoOfRangeEq_hom_fac f (𝟙 X)
    ((Set.range_eq_univ.mpr hsurj).trans (Set.range_eq_univ.mpr (fun x => ⟨x, rfl⟩)).symm)
  rw [Category.comp_id] at h
  rw [← h]
  infer_instance

end KltDP.Geometry.IsoOfPunctureAndChart

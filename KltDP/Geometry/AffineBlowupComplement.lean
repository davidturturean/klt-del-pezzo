import KltDP.Geometry.AffineBlowupCenter
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# The blowup is an isomorphism away from its center

The canonical localization map from each Rees chart gives an actual open
immersion from `Spec R[1/a]` into the blowup. Its range is proved to be the
inverse image of `D(a)`. Equal-range isomorphisms identify the actual
restricted structure morphism with an isomorphism. The existing theorem
that isomorphisms are local on the target then treats the full complement
of the center, without a finite generation hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace KltDP.Geometry.AffineBlowup

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The canonical map from the base localization through its Rees chart. -/
def complementChartι (a : I) :
    Spec (CommRingCat.of (Localization.Away (a : R))) ⟶ scheme I :=
  Spec.map (CommRingCat.ofHom (chartToLocalization I a)) ≫ chartι I a

instance (a : I) : IsOpenImmersion (complementChartι I a) := by
  letI := chartLocalizationAlgebra I a
  letI : IsLocalization.Away (chartBaseMap I a (a : R)) (Localization.Away (a : R)) :=
    chartToLocalization_isLocalization I a
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (chartToLocalization I a))) :=
    IsOpenImmersion.of_isLocalization (chartBaseMap I a (a : R))
  unfold complementChartι
  infer_instance

/-- The base composite uses exactly the canonical localization map. -/
@[simp]
theorem complementChartι_toSpec (a : I) :
    complementChartι I a ≫ toSpec I =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (a : R)))) := by
  have hchart : chartι I a ≫ toSpec I =
      Spec.map (CommRingCat.ofHom (chartBaseMap I a)) := chartι_toSpec I a
  rw [complementChartι, Category.assoc, hchart, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext r
  exact chartToLocalization_baseMap I a r

/-- A point of the blowup lying over `D(a)` belongs to the actual `aT` chart. -/
theorem preimage_basicOpen_le_chartOpen (a : I) :
    (toSpec I) ⁻¹ᵁ PrimeSpectrum.basicOpen (a : R) ≤ chartOpen I a := by
  intro x hx
  obtain ⟨b, p, hp⟩ := (degreeOneAffineCover I).openCover.exists_eq x
  change (chartι I b).base p = x at hp
  subst x
  have hchart : chartι I b ≫ toSpec I =
      Spec.map (CommRingCat.ofHom (chartBaseMap I b)) := chartι_toSpec I b
  have hnot : chartBaseMap I b (a : R) ∉ p.asIdeal := by
    change (a : R) ∉ ((toSpec I).base ((chartι I b).base p)).asIdeal at hx
    change (a : R) ∉ ((chartι I b ≫ toSpec I).base p).asIdeal at hx
    rw [hchart] at hx
    exact hx
  apply (chartι_mem_chartOpen_iff I a b p).mpr
  intro hratio
  apply hnot
  rw [← chartBaseMap_mul_chartFraction I b a]
  exact Ideal.mul_mem_left _ _ hratio

/-- The localization immersion fills exactly the inverse image of `D(a)`. -/
theorem range_complementChartι (a : I) :
    Set.range (complementChartι I a).base =
      ((toSpec I) ⁻¹ᵁ PrimeSpectrum.basicOpen (a : R) : Set (scheme I)) := by
  letI := chartLocalizationAlgebra I a
  letI : IsLocalization.Away (chartBaseMap I a (a : R)) (Localization.Away (a : R)) :=
    chartToLocalization_isLocalization I a
  have hq : Set.range (Spec.map (CommRingCat.ofHom (chartToLocalization I a))).base =
      (PrimeSpectrum.basicOpen (chartBaseMap I a (a : R)) :
        Set (PrimeSpectrum (chartRing I a))) :=
    PrimeSpectrum.localization_away_comap_range
      (Localization.Away (a : R)) (chartBaseMap I a (a : R))
  apply Set.Subset.antisymm
  · rintro x ⟨p, rfl⟩
    change (a : R) ∉ ((complementChartι I a ≫ toSpec I).base p).asIdeal
    rw [complementChartι_toSpec]
    change algebraMap R (Localization.Away (a : R)) (a : R) ∉ p.asIdeal
    intro hmem
    exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem hmem
      (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (a : R)) (a : R)))
  · intro x hx
    have hxchart : x ∈ (chartι I a).opensRange := by
      rw [chartι_opensRange]
      exact preimage_basicOpen_le_chartOpen I a hx
    obtain ⟨p, hp⟩ := hxchart
    have hchart : chartι I a ≫ toSpec I =
        Spec.map (CommRingCat.ofHom (chartBaseMap I a)) := chartι_toSpec I a
    have hpa : p ∈ PrimeSpectrum.basicOpen (chartBaseMap I a (a : R)) := by
      rw [← hp] at hx
      change (a : R) ∉ ((chartι I a ≫ toSpec I).base p).asIdeal at hx
      rw [hchart] at hx
      exact hx
    have hprange : p ∈
        Set.range (Spec.map (CommRingCat.ofHom (chartToLocalization I a))).base := by
      rw [hq]
      exact hpa
    obtain ⟨q, hqpoint⟩ := hprange
    refine ⟨q, ?_⟩
    change (chartι I a).base
      ((Spec.map (CommRingCat.ofHom (chartToLocalization I a))).base q) = x
    rw [hqpoint, hp]

/-- A canonical isomorphism of the blowup restriction over one `D(a)`
with that actual open subscheme of the base. -/
def basicOpenIso (a : I) :
    ((toSpec I) ⁻¹ᵁ PrimeSpectrum.basicOpen (a : R)).toScheme ≅
      Scheme.Opens.toScheme (X := Spec (CommRingCat.of R)) (PrimeSpectrum.basicOpen (a : R)) := by
  let V := (toSpec I) ⁻¹ᵁ PrimeSpectrum.basicOpen (a : R)
  let U : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen (a : R)
  let eB := IsOpenImmersion.isoOfRangeEq (complementChartι I a) V.ι
    ((range_complementChartι I a).trans Subtype.range_coe.symm)
  let eR := IsOpenImmersion.isoOfRangeEq
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (a : R))))) U.ι
    ((PrimeSpectrum.localization_away_comap_range (Localization.Away (a : R))
      (a : R)).trans Subtype.range_coe.symm)
  exact eB.symm ≪≫ eR

/-- The isomorphism's morphism is the actual restricted structure morphism. -/
theorem basicOpenIso_hom (a : I) :
    (basicOpenIso I a).hom = (toSpec I) ∣_ PrimeSpectrum.basicOpen (a : R) := by
  apply (cancel_mono
    (Scheme.Opens.ι (X := Spec (CommRingCat.of R)) (PrimeSpectrum.basicOpen (a : R)))).mp
  rw [morphismRestrict_ι]
  dsimp only [basicOpenIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac,
    ← complementChartι_toSpec I a, ← Category.assoc,
    IsOpenImmersion.isoOfRangeEq_inv_fac]

/-- The actual blowup morphism restricts to an isomorphism on each `D(a)`. -/
theorem toSpec_restrict_basicOpen_isIso (a : I) :
    IsIso ((toSpec I) ∣_ PrimeSpectrum.basicOpen (a : R)) := by
  rw [← basicOpenIso_hom I a]
  infer_instance

/-- The actual open complement of the vanishing set of the original ideal. -/
def centerComplement : (Spec (CommRingCat.of R)).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (I : Set R))ᶜ,
    (PrimeSpectrum.isClosed_zeroLocus (I : Set R)).isOpen_compl⟩

/-- Membership in the complement supplies an actual center element which
is nonzero in the corresponding prime quotient. -/
theorem mem_centerComplement_iff (p : PrimeSpectrum R) :
    p ∈ centerComplement I ↔ ∃ a : I, (a : R) ∉ p.asIdeal := by
  change (¬ (I : Set R) ⊆ p.asIdeal) ↔ _
  constructor
  · intro hp
    obtain ⟨a, ha, hpa⟩ := Set.not_subset.mp hp
    exact ⟨⟨a, ha⟩, hpa⟩
  · rintro ⟨a, ha⟩ hp
    exact ha (hp a.property)

/-- Each center basic open belongs to the complement. -/
theorem basicOpen_le_centerComplement (a : I) :
    PrimeSpectrum.basicOpen (a : R) ≤ centerComplement I := by
  intro p hp
  exact (mem_centerComplement_iff I p).mpr ⟨a, hp⟩

/-- The structure morphism is an actual isomorphism over the entire
complement of the center, by the proved basic-open isomorphisms. -/
theorem toSpec_restrict_centerComplement_isIso :
    IsIso ((toSpec I) ∣_ centerComplement I) := by
  let U := centerComplement I
  let V : I → U.toScheme.Opens := fun a => U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (a : R)
  have hcover : (⨆ a, V a) = ⊤ := by
    apply top_unique
    intro p _
    obtain ⟨a, ha⟩ := (mem_centerComplement_iff I p.1).mp p.2
    exact (le_iSup V a) ha
  apply IsLocalAtTarget.of_iSup_eq_top
    (P := CategoryTheory.MorphismProperty.isomorphisms Scheme) V hcover
  intro a
  have himage : U.ι ''ᵁ V a = PrimeSpectrum.basicOpen (a : R) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inter, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr (basicOpen_le_centerComplement I a)
  let e := morphismRestrictRestrict (toSpec I) U (V a) ≪≫
    morphismRestrictEq (toSpec I) himage
  exact ((CategoryTheory.MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff e).mpr
    (toSpec_restrict_basicOpen_isIso I a)

/-- The actual isomorphism away from the original center. -/
def complementIso : ((toSpec I) ⁻¹ᵁ centerComplement I).toScheme ≅
    (centerComplement I).toScheme := by
  letI := toSpec_restrict_centerComplement_isIso I
  exact asIso ((toSpec I) ∣_ centerComplement I)

/-- Its forward morphism is exactly the restriction of the blowup morphism. -/
@[simp]
theorem complementIso_hom : (complementIso I).hom = (toSpec I) ∣_ centerComplement I := rfl

/-- The isomorphism retains the canonical composition to the affine base. -/
@[simp]
theorem complementIso_hom_ι :
    (complementIso I).hom ≫ (centerComplement I).ι =
      ((toSpec I) ⁻¹ᵁ centerComplement I).ι ≫ toSpec I :=
  morphismRestrict_ι _ _

end KltDP.Geometry.AffineBlowup

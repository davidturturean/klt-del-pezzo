import KltDP.Geometry.ReesChartLocalization
import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# An actual affine lift into a chosen Rees chart

Let `φ : R →+* S`, let `a ∈ I`, and suppose the extended ideal is contained
in `(φ a)` and `φ a` is a nonzerodivisor. The canonical map from the actual
Rees chart to `S[1/(φ a)]` then descends uniquely to `S`. Taking spectra
gives an actual morphism to the Rees Proj, over the prescribed `Spec φ`.

The ideal containment is equivalent to equality here because `a ∈ I`.
No factorization or division operation is included in the hypotheses.
Uniqueness is proved for lifts into this specified chart. Gluing when the
extended ideal has only local regular generators, and uniqueness among all
morphisms to the entire Proj, are separate remaining obligations.

Reuse: pinned Mathlib `Localization.awayMap`, `Ideal.map_pow`, localization
injectivity, and `AlgEquiv.ofInjective` for descent to the actual range.
See `docs/AFFINE_BLOWUP_LIFT_CORRESPONDENCE.md` for the source comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry.AffineBlowup

universe u v

variable {R : Type u} [CommRing R] (I : Ideal R) (a : I)

/-- Clearing the denominator of an actual homogeneous Rees-chart fraction. -/
theorem chartBaseMap_pow_mul_chartMonomialFraction (n : ℕ) (r : ↥(I ^ n)) :
    chartBaseMap I a (a : R) ^ n * chartMonomialFraction I a n r =
      chartBaseMap I a (r : R) := by
  apply chartToLocalization_injective I a
  rw [map_mul, map_pow, chartToLocalization_baseMap,
    chartToLocalization_monomialFraction, chartToLocalization_baseMap]
  have hc :
      algebraMap R (Localization.Away (a : R)) (a : R) ^ n *
        IsLocalization.Away.invSelf (S := Localization.Away (a : R)) (a : R) ^ n = 1 := by
    rw [← mul_pow, IsLocalization.Away.mul_invSelf, one_pow]
  calc
    _ = algebraMap R (Localization.Away (a : R)) (r : R) *
        (algebraMap R (Localization.Away (a : R)) (a : R) ^ n *
          IsLocalization.Away.invSelf (S := Localization.Away (a : R)) (a : R) ^ n) := by
      ring
    _ = _ := by rw [hc, mul_one]

variable {S : Type v} [CommRing S] (φ : R →+* S)

/-- The ideal containment in the lifting hypothesis is actual principal
generation, because the chosen equation comes from the center ideal. -/
theorem map_ideal_eq_span_of_le
    (hI : Ideal.map φ I ≤ Ideal.span {φ (a : R)}) :
    Ideal.map φ I = Ideal.span {φ (a : R)} := by
  apply le_antisymm hI
  apply Ideal.span_le.mpr
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  exact Ideal.mem_map_of_mem φ a.property

/-- The canonical chart map followed by the actual localization map induced by `φ`. -/
def chartToTargetLocalization :
    chartRing I a →+* Localization.Away (φ (a : R)) :=
  (Localization.awayMap φ (a : R)).comp (chartToLocalization I a)

@[simp]
theorem chartToTargetLocalization_baseMap (r : R) :
    chartToTargetLocalization I a φ (chartBaseMap I a r) =
      algebraMap S (Localization.Away (φ (a : R))) (φ r) := by
  simp only [chartToTargetLocalization, RingHom.comp_apply,
    chartToLocalization_baseMap, Localization.awayMap,
    IsLocalization.Away.map, IsLocalization.map_eq]

/-- Ideal powers give the actual divisibility needed to remove each denominator. -/
theorem exists_image_eq_pow_mul
    (hI : Ideal.map φ I ≤ Ideal.span {φ (a : R)})
    (n : ℕ) (r : ↥(I ^ n)) :
    ∃ s : S, φ (r : R) = φ (a : R) ^ n * s := by
  have hr : φ (r : R) ∈ Ideal.map φ (I ^ n) :=
    Ideal.mem_map_of_mem φ r.property
  rw [Ideal.map_pow] at hr
  have hs : φ (r : R) ∈ Ideal.span {φ (a : R)} ^ n :=
    (pow_le_pow_left' hI n) hr
  rw [Ideal.span_singleton_pow] at hs
  exact Ideal.mem_span_singleton.mp hs

/-- The canonical localized map has its values in the actual image of `S`. -/
theorem chartToTargetLocalization_mem_range
    (hI : Ideal.map φ I ≤ Ideal.span {φ (a : R)}) (x : chartRing I a) :
    chartToTargetLocalization I a φ x ∈
      (algebraMap S (Localization.Away (φ (a : R)))).range := by
  obtain ⟨n, r, rfl⟩ := exists_chartMonomialFraction I a x
  obtain ⟨s, hs⟩ := exists_image_eq_pow_mul I a φ hI n r
  refine ⟨s, ?_⟩
  apply (IsLocalization.Away.algebraMap_pow_isUnit
    (S := Localization.Away (φ (a : R))) (φ (a : R)) n).mul_left_cancel
  have h := congrArg (chartToTargetLocalization I a φ)
    (chartBaseMap_pow_mul_chartMonomialFraction I a n r)
  simp only [map_mul, map_pow, chartToTargetLocalization_baseMap] at h
  rw [h, hs, map_mul, map_pow]

/-- The injective localization map identifies `S` with its actual range. -/
def targetLocalizationRangeEquiv (hreg : φ (a : R) ∈ nonZeroDivisors S) :
    S ≃+* (algebraMap S (Localization.Away (φ (a : R)))).range :=
  (AlgEquiv.ofInjective (Algebra.ofId S (Localization.Away (φ (a : R))))
    (IsLocalization.injective (Localization.Away (φ (a : R)))
      (Submonoid.powers_le.mpr hreg))).toRingEquiv

/-- The unique ring map to `S`, constructed by descending the canonical
localized map through the range equivalence. -/
def chartLift (hreg : φ (a : R) ∈ nonZeroDivisors S)
    (hI : Ideal.map φ I ≤ Ideal.span {φ (a : R)}) : chartRing I a →+* S :=
  (targetLocalizationRangeEquiv I a φ hreg).symm.toRingHom.comp
    ((chartToTargetLocalization I a φ).codRestrict
      (algebraMap S (Localization.Away (φ (a : R)))).range
      (chartToTargetLocalization_mem_range I a φ hI))

@[simp]
theorem algebraMap_chartLift (hreg : φ (a : R) ∈ nonZeroDivisors S)
    (hI : Ideal.map φ I ≤ Ideal.span {φ (a : R)}) (x : chartRing I a) :
    algebraMap S (Localization.Away (φ (a : R))) (chartLift I a φ hreg hI x) =
      chartToTargetLocalization I a φ x := by
  exact congrArg Subtype.val
    ((targetLocalizationRangeEquiv I a φ hreg).apply_symm_apply _)

@[simp]
theorem chartLift_baseMap (hreg : φ (a : R) ∈ nonZeroDivisors S)
    (hI : Ideal.map φ I ≤ Ideal.span {φ (a : R)}) (r : R) :
    chartLift I a φ hreg hI (chartBaseMap I a r) = φ r := by
  apply IsLocalization.injective (Localization.Away (φ (a : R)))
    (Submonoid.powers_le.mpr hreg)
  rw [algebraMap_chartLift, chartToTargetLocalization_baseMap]

/-- The descended map agrees with the originally specified affine base map. -/
theorem chartLift_comp_baseMap (hreg : φ (a : R) ∈ nonZeroDivisors S)
    (hI : Ideal.map φ I ≤ Ideal.span {φ (a : R)}) :
    (chartLift I a φ hreg hI).comp (chartBaseMap I a) = φ := by
  ext r
  exact chartLift_baseMap I a φ hreg hI r

/-- Evaluation on every homogeneous fraction satisfies the required division equation. -/
theorem chartLift_monomialFraction_mul (hreg : φ (a : R) ∈ nonZeroDivisors S)
    (hI : Ideal.map φ I ≤ Ideal.span {φ (a : R)}) (n : ℕ) (r : ↥(I ^ n)) :
    φ (a : R) ^ n * chartLift I a φ hreg hI (chartMonomialFraction I a n r) =
      φ (r : R) := by
  have h := congrArg (chartLift I a φ hreg hI)
    (chartBaseMap_pow_mul_chartMonomialFraction I a n r)
  simpa only [map_mul, map_pow, chartLift_baseMap] using h

/-- Regularity of the pulled-back equation proves uniqueness in this actual chart. -/
theorem chartLift_unique (hreg : φ (a : R) ∈ nonZeroDivisors S)
    (hI : Ideal.map φ I ≤ Ideal.span {φ (a : R)})
    (ψ : chartRing I a →+* S) (hψ : ψ.comp (chartBaseMap I a) = φ) :
    ψ = chartLift I a φ hreg hI := by
  have hb (r : R) : ψ (chartBaseMap I a r) = φ r := RingHom.congr_fun hψ r
  ext x
  obtain ⟨n, r, rfl⟩ := exists_chartMonomialFraction I a x
  apply (mul_cancel_left_mem_nonZeroDivisors (pow_mem hreg n)).mp
  have h := congrArg ψ (chartBaseMap_pow_mul_chartMonomialFraction I a n r)
  simp only [map_mul, map_pow, hb] at h
  rw [h, chartLift_monomialFraction_mul]

/-- The chosen Rees chart has the actual ring-level universal mapping property
for test maps with this regular principal inverse-image equation. -/
theorem existsUnique_chartLift (hreg : φ (a : R) ∈ nonZeroDivisors S)
    (hI : Ideal.map φ I ≤ Ideal.span {φ (a : R)}) :
    ∃! ψ : chartRing I a →+* S, ψ.comp (chartBaseMap I a) = φ := by
  exact ⟨chartLift I a φ hreg hI, chartLift_comp_baseMap I a φ hreg hI,
    fun ψ hψ => chartLift_unique I a φ hreg hI ψ hψ⟩

section Scheme

variable {T : Type u} [CommRing T] (f : R →+* T)
    (hreg : f (a : R) ∈ nonZeroDivisors T)
    (hI : Ideal.map f I ≤ Ideal.span {f (a : R)})

/-- The actual affine test scheme maps into the chosen Rees chart. -/
def affineChartLift : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of (chartRing I a)) :=
  Spec.map (CommRingCat.ofHom (chartLift I a f hreg hI))

@[simp]
theorem affineChartLift_toSpec :
    affineChartLift I a f hreg hI ≫ Spec.map (CommRingCat.ofHom (chartBaseMap I a)) =
      Spec.map (CommRingCat.ofHom f) := by
  rw [affineChartLift, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    chartLift_comp_baseMap]

/-- The chart lift is unique among actual morphisms into this affine chart
with the prescribed composite to the base scheme. -/
theorem affineChartLift_unique
    (j : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of (chartRing I a)))
    (hj : j ≫ Spec.map (CommRingCat.ofHom (chartBaseMap I a)) =
      Spec.map (CommRingCat.ofHom f)) : j = affineChartLift I a f hreg hI := by
  have hc : CommRingCat.ofHom (chartBaseMap I a) ≫ Spec.preimage j =
      CommRingCat.ofHom f := by
    apply Spec.map_injective
    simpa only [Spec.map_comp, Spec.map_preimage] using hj
  have hr : (Spec.preimage j).hom.comp (chartBaseMap I a) = f :=
    congrArg CommRingCat.Hom.hom hc
  rw [← Spec.map_preimage j]
  exact congrArg (fun g : chartRing I a →+* T => Spec.map (CommRingCat.ofHom g))
    (chartLift_unique I a f hreg hI (Spec.preimage j).hom hr)

/-- The actual factorization through the existing Rees Proj. -/
def affineLift : Spec (CommRingCat.of T) ⟶ scheme I :=
  affineChartLift I a f hreg hI ≫ chartι I a

/-- Its composite is exactly the originally prescribed morphism `Spec f`. -/
@[simp]
theorem affineLift_toSpec :
    affineLift I a f hreg hI ≫ toSpec I = Spec.map (CommRingCat.ofHom f) := by
  rw [affineLift, Category.assoc, chartι_toSpec]
  exact affineChartLift_toSpec I a f hreg hI

end Scheme

end KltDP.Geometry.AffineBlowup

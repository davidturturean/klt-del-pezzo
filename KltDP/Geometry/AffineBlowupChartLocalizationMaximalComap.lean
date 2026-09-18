import KltDP.Geometry.AffineBlowupChartLocalizationDenominators
import KltDP.Geometry.AffineBlowupConormal

/-! A closed localized-chart point over the closed centre comes from an original closed point. -/

noncomputable section

namespace KltDP.Geometry.AffineBlowupChartBaseChange

open AffineBlowup

universe u

private theorem comap_isMaximal_of_base_denominators
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (α : R →+* A) (χ : A →+* B) (m : Ideal R) [m.IsMaximal]
    (Q : Ideal B) [Q.IsMaximal] (hbase : Q.comap (χ.comp α) = m)
    (hden : ∀ z : B, ∃ (w : A) (r : R), r ∉ m ∧ χ (α r) * z = χ w) :
    (Q.comap χ).IsMaximal := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  letI : Field (B ⧸ Q) := Ideal.Quotient.field Q
  let ψ : A →+* B ⧸ Q := (Ideal.Quotient.mk Q).comp χ
  let τ : R ⧸ m →+* B ⧸ Q := Ideal.quotientMap Q (χ.comp α) hbase.symm.le
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨w, r, hr, hw⟩ := hden b
    have hr0 : Ideal.Quotient.mk m r ≠ 0 := by
      simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hr
    obtain ⟨r', hr'⟩ := Ideal.Quotient.mk_surjective ((Ideal.Quotient.mk m r)⁻¹)
    have hinv : ψ (α r') * ψ (α r) = 1 := by
      change τ (Ideal.Quotient.mk m r') * τ (Ideal.Quotient.mk m r) = 1
      rw [← map_mul, hr', inv_mul_cancel₀ hr0, map_one]
    have hwq : ψ (α r) * Ideal.Quotient.mk Q b = ψ w := by
      simpa only [ψ, RingHom.comp_apply, map_mul] using
        congrArg (Ideal.Quotient.mk Q) hw
    refine ⟨α r' * w, ?_⟩
    rw [map_mul, ← hwq, ← mul_assoc, hinv, one_mul]
  letI : (⊥ : Ideal (B ⧸ Q)).IsMaximal := Ideal.bot_isMaximal
  have hmax : (Ideal.comap ψ (⊥ : Ideal (B ⧸ Q))).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective ψ hsurj
  have heq : Ideal.comap ψ (⊥ : Ideal (B ⧸ Q)) = Q.comap χ := by
    ext z
    simp only [Ideal.mem_comap, Ideal.mem_bot, ψ, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem]
  exact heq ▸ hmax

variable {R : Type u} [CommRing R]

/-- Denominators outside the original maximal centre ideal are already
invertible in its residue field. Thus the actual original chart comap of a
closed localized-chart point over that centre is maximal. -/
theorem localization_comap_isMaximal (I : Ideal R) (m : Ideal R) [m.IsMaximal] (a : I)
    (Q : Ideal (chartRing (I.map (algebraMap R (Localization.AtPrime m)))
      (mappedElement I (algebraMap R (Localization.AtPrime m)) a))) [Q.IsMaximal]
    (hQm : Q.comap (baseMap I (algebraMap R (Localization.AtPrime m)) a) = m) :
    (Q.comap (chartMap I (algebraMap R (Localization.AtPrime m)) a)).IsMaximal := by
  have hbase : Q.comap ((chartMap I (algebraMap R (Localization.AtPrime m)) a).comp
      (chartBaseMap I a)) = m := by
    have heq : (chartMap I (algebraMap R (Localization.AtPrime m)) a).comp
        (chartBaseMap I a) = baseMap I (algebraMap R (Localization.AtPrime m)) a := by
      apply RingHom.ext
      intro r
      exact chartMap_baseMap I (algebraMap R (Localization.AtPrime m)) a r
    rw [heq]
    exact hQm
  apply comap_isMaximal_of_base_denominators (chartBaseMap I a)
    (chartMap I (algebraMap R (Localization.AtPrime m)) a) m Q hbase
  intro z
  obtain ⟨w, s, hs⟩ := exists_original_chart_denominator I m.primeCompl a z
  refine ⟨w, s, s.property, ?_⟩
  simpa only [chartMap_baseMap, baseMap, RingHom.comp_apply] using hs

/-- The original exceptional-centre containment alone supplies the required
base-point equality; no maximality of the original chart prime is assumed. -/
theorem localization_comap_isMaximal_of_center (m : Ideal R) [m.IsMaximal] (a : m)
    (Q : Ideal (chartRing (m.map (algebraMap R (Localization.AtPrime m)))
      (mappedElement m (algebraMap R (Localization.AtPrime m)) a))) [Q.IsMaximal]
    (hcenter : chartCenterIdeal (m.map (algebraMap R (Localization.AtPrime m)))
      (mappedElement m (algebraMap R (Localization.AtPrime m)) a) ≤ Q) :
    (Q.comap (chartMap m (algebraMap R (Localization.AtPrime m)) a)).IsMaximal := by
  apply localization_comap_isMaximal m m a Q
  have hle : m ≤ Q.comap (baseMap m (algebraMap R (Localization.AtPrime m)) a) := by
    apply Ideal.map_le_iff_le_comap.mp
    change m.map ((chartBaseMap (m.map (algebraMap R (Localization.AtPrime m)))
      (mappedElement m (algebraMap R (Localization.AtPrime m)) a)).comp
        (algebraMap R (Localization.AtPrime m))) ≤ Q
    rw [← Ideal.map_map]
    exact hcenter
  exact (Ideal.IsMaximal.eq_of_le (inferInstance : m.IsMaximal)
    (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top (inferInstance : Q.IsMaximal))) hle).symm

end KltDP.Geometry.AffineBlowupChartBaseChange

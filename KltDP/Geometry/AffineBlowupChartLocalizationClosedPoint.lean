import KltDP.Geometry.AffineBlowupChartStalkAtCenter
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! The derived localized chart prime remains closed when the original one is closed. -/

noncomputable section

namespace KltDP.Geometry.AffineBlowupChartBaseChange

open AffineBlowup

universe u

private theorem residueMap_surjective_at_maximal {A : Type u} [CommRing A]
    (P : Ideal A) [P.IsMaximal] :
    Function.Surjective ((IsLocalRing.residue (Localization.AtPrime P)).comp
      (algebraMap A (Localization.AtPrime P))) := by
  have hP : (IsLocalRing.maximalIdeal (Localization.AtPrime P)).comap
      (algebraMap A (Localization.AtPrime P)) = P :=
    Localization.AtPrime.comap_maximalIdeal
  have hmax : ((IsLocalRing.maximalIdeal (Localization.AtPrime P)).comap
      (algebraMap A (Localization.AtPrime P))).IsMaximal := hP.symm ▸ inferInstance
  have hq := IsLocalization.surjective_quotientMap_of_maximal_of_localization
    P.primeCompl (Localization.AtPrime P) (J := P) (H := hP.symm.le) hmax
  intro z
  obtain ⟨t, ht⟩ := hq z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective t
  exact ⟨r, ht⟩

variable {R : Type u} [CommRing R] (I : Ideal R) (a : I)
variable (m : Ideal R) [m.IsPrime]
variable (P : Ideal (chartRing I a)) [P.IsMaximal]
variable (hPm : P.comap (chartBaseMap I a) = m)

/-- Closedness is proved from the original residue field, not imposed on the
constructed localized-chart point. -/
instance localizedChartPrime_isMaximal : (localizedChartPrime I a m P hPm).IsMaximal := by
  let ψ := (IsLocalRing.residue (Localization.AtPrime P)).comp
    (localizedChartToStalk I a m P hPm)
  have hcomp : ψ.comp (chartMap I (algebraMap R (Localization.AtPrime m)) a) =
      (IsLocalRing.residue (Localization.AtPrime P)).comp
        (algebraMap (chartRing I a) (Localization.AtPrime P)) := by
    dsimp only [ψ]
    rw [RingHom.comp_assoc, localizedChartToStalk_comp_chartMap]
  have hsurj : Function.Surjective ψ := by
    apply Function.Surjective.of_comp
      (g := chartMap I (algebraMap R (Localization.AtPrime m)) a)
    change Function.Surjective (ψ.comp (chartMap I (algebraMap R (Localization.AtPrime m)) a))
    rw [hcomp]
    exact residueMap_surjective_at_maximal P
  letI : (⊥ : Ideal (IsLocalRing.ResidueField (Localization.AtPrime P))).IsMaximal :=
    Ideal.bot_isMaximal
  have hmax : (Ideal.comap ψ (⊥ : Ideal (IsLocalRing.ResidueField
      (Localization.AtPrime P)))).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective ψ hsurj
  convert hmax using 1
  ext z
  simp only [localizedChartPrime, Ideal.mem_comap, ψ, RingHom.comp_apply,
    Ideal.mem_bot, IsLocalRing.residue_eq_zero_iff]

end KltDP.Geometry.AffineBlowupChartBaseChange

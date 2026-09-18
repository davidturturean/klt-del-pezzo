import KltDP.Geometry.DivisorOrderTransport

/-!
# The existing normalized order under a compatible field map

This is the two-field form of the existing common-field transport proof.
It reuses the proved DVR normalization and pinned localization uniqueness;
no new valuation or order is defined. In the geometric consumer, both maps
and their compatibility come from the original scheme morphism.
-/

noncomputable section
open IsDedekindDomain
open scoped Multiplicative
universe u v w z

namespace KltDP.RingTheory

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {S : Type v} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
variable {K : Type w} [Field K] [Algebra R K] [IsFractionRing R K]
variable {L : Type z} [Field L] [Algebra S L] [IsFractionRing S L]

/-- The original fraction-field valuations commute with a field map that
extends the given isomorphism of their original DVRs. -/
theorem fractionFieldValuation_comp_eq_of_ringEquiv (e : R ≃+* S) (φ : K →+* L)
    (hcompat : ∀ r : R, algebraMap S L (e r) = φ (algebraMap R K r)) :
    (fractionFieldValuation S L).comap φ = fractionFieldValuation R K := by
  have hbase (r : R) :
      (fractionFieldValuation S L).comap φ (algebraMap R K r) =
        fractionFieldValuation R K (algebraMap R K r) := by
    change fractionFieldValuation S L (φ (algebraMap R K r)) = _
    rw [← hcompat r]
    change (dvrHeightOnePrime S).valuation L (algebraMap S L (e r)) =
      (dvrHeightOnePrime R).valuation K (algebraMap R K r)
    simp only [HeightOneSpectrum.valuation_of_algebraMap]
    exact dvrIntValuation_eq_of_ringEquiv e r
  have hhom :
      ((fractionFieldValuation S L).comap φ).toMonoidWithZeroHom.toMonoidHom =
        (fractionFieldValuation R K).toMonoidWithZeroHom.toMonoidHom :=
    (IsLocalization.toLocalizationMap (nonZeroDivisors R) K).epic_of_localizationMap
      hbase
  exact Valuation.ext (fun x => DFunLike.congr_fun hhom x)

/-- The integer order, with its existing sign convention, is preserved
on the original units by that same compatible field map. -/
theorem divisorOrder_map_of_ringEquiv (e : R ≃+* S) (φ : K →+* L)
    (hcompat : ∀ r : R, algebraMap S L (e r) = φ (algebraMap R K r)) (f : Kˣ) :
    divisorOrder S L (Units.map φ.toMonoidHom f) = divisorOrder R K f := by
  apply (divisorOrder_eq_iff S L _ _).mpr
  change fractionFieldValuation S L (φ (f : K)) = _
  calc
    fractionFieldValuation S L (φ (f : K)) =
        fractionFieldValuation R K (f : K) :=
      DFunLike.congr_fun (fractionFieldValuation_comp_eq_of_ringEquiv e φ hcompat) (f : K)
    _ = ((Multiplicative.ofAdd (-divisorOrder R K f) : Multiplicative ℤ) : ℤₘ₀) :=
      (coe_neg_divisorOrder R K f).symm

end KltDP.RingTheory

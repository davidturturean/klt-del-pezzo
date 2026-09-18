import KltDP.Geometry.AffineBlowupParameterChartCoefficients
import Mathlib.RingTheory.Localization.Ideal

/-!
# Original reduced boundary ideals across parameter charts

The original two-chart stalk equivalence carries every extended base
ideal to the same extended base ideal. Localization and ring-equivalence
compatibility with radicals then identify the actual reduced ideal of
the exceptional divisor together with the pulled boundary equation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineBlowup

private theorem map_radical_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (J : Ideal A) :
    Ideal.map e.toRingHom J.radical = (Ideal.map e.toRingHom J).radical := by
  calc
    _ = J.radical.comap e.symm := Ideal.map_comap_of_equiv e
    _ = (J.comap e.symm).radical := Ideal.comap_radical e.symm J
    _ = _ := congrArg Ideal.radical (Ideal.map_comap_of_equiv e).symm

variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)
variable (p : PrimeSpectrum (chartRing I a)) (q : PrimeSpectrum (chartRing I b))
variable (h : (chartι I a).base p = (chartι I b).base q)

/-- The original stalk comparison preserves every extended base ideal. -/
theorem parameterChartStalkEquiv_baseIdeal (J : Ideal R) :
    Ideal.map (parameterChartStalkEquiv I a b p q h).toRingHom
      (Ideal.map (algebraMap (chartRing I a) (Localization.AtPrime p.asIdeal))
        (Ideal.map (chartBaseMap I a) J)) =
      Ideal.map (algebraMap (chartRing I b) (Localization.AtPrime q.asIdeal))
        (Ideal.map (chartBaseMap I b) J) := by
  have hmap : (parameterChartStalkEquiv I a b p q h).toRingHom.comp
      ((algebraMap (chartRing I a) (Localization.AtPrime p.asIdeal)).comp
        (chartBaseMap I a)) =
      (algebraMap (chartRing I b) (Localization.AtPrime q.asIdeal)).comp
        (chartBaseMap I b) := by
    apply RingHom.ext
    intro r
    exact parameterChartStalkEquiv_baseMap I a b p q h r
  simpa only [Ideal.map_map] using congrArg (fun f => Ideal.map f J) hmap

/-- The original stalk comparison identifies the localized radical of
the actual exceptional-plus-pullback ideal in the two original charts. -/
theorem parameterChartStalkEquiv_reducedBoundaryIdeal (c : R) :
    Ideal.map (parameterChartStalkEquiv I a b p q h).toRingHom
      (Ideal.map (algebraMap (chartRing I a) (Localization.AtPrime p.asIdeal))
        (chartCenterIdeal I a * Ideal.map (chartBaseMap I a) (Ideal.span {c})).radical) =
      Ideal.map (algebraMap (chartRing I b) (Localization.AtPrime q.asIdeal))
        (chartCenterIdeal I b * Ideal.map (chartBaseMap I b) (Ideal.span {c})).radical := by
  rw [IsLocalization.map_radical p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal),
    IsLocalization.map_radical q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal),
    map_radical_ringEquiv]
  simp only [chartCenterIdeal, Ideal.map_mul]
  rw [parameterChartStalkEquiv_baseIdeal I a b p q h I,
    parameterChartStalkEquiv_baseIdeal I a b p q h (Ideal.span {c})]

end KltDP.Geometry.AffineBlowup

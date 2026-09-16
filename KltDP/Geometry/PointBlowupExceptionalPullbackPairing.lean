import KltDP.Geometry.PointBlowupPicardSplitting
import KltDP.Geometry.PrimeCurveInclusionLift

/-!
# `σ^*D · E = 0` on the glued point blowup

BRIEF34, task 2. On the blowup surface of `Geometry/PointBlowupPicardSplitting`, the exceptional curve
pairs to zero with every class pulled back from the base: `E · σ^*c = 0`.

The argument is the accepted one, not a new one. `Geometry/PrimeCurveInclusionLift` already proves,
generically, that if `ι ≫ π` factors through the spectrum of a principal ideal domain then the
restriction to the prime curve of `ι` of any `π`-pullback has degree zero
(`restrictionDegree_pullback_eq_zero` and its Picard-class and degree-homomorphism forms): the pullback
to `Spec R` is trivial (`AffineModuleTilde.pidInvertibleUnitIso`) and pullbacks of the unit are the
unit. Lane A2's `FrobeniusStageExceptionalPairing.exceptionalPairing_pullback` is the Frobenius-stage
instance of exactly this. What is supplied here is the instantiation for the accepted glued point
blowup:

* `ι := PointBlowupGluing.globalCenterFiberι j q hclosed`, a closed immersion (accepted instance) whose
  source is reduced because Stacks 0AGQ makes it isomorphic to `P¹` (accepted
  `isIntegral_of_iso_projectiveLine`);
* `hP` is `rfl`: the exceptional curve of `PointBlowupSplitting.exceptionalCurve` is by construction the
  prime curve of that immersion;
* the factorisation is **`pullback.condition`**: the accepted `globalCenterFiber` *is*
  `pullback (projection) (closedCenterInclusion)`, with `globalCenterFiberι = pullback.fst` and
  `globalCenterFiberToCenter = pullback.snd`, so `ι ≫ σ = globalCenterFiberToCenter ≫ closedCenterInclusion`
  factors through `Spec (R ⧸ q.asIdeal)`;
* that residue ring is a **field** (`Ideal.Quotient.field`, `q.asIdeal` maximal), hence a domain and a
  principal ideal ring, which is the hypothesis the accepted lemma needs.

**`exceptional_pullback_pairing_zero`** is the headline: `E · σ^*c = 0` for every Picard class `c` of
the base, with `exceptional_pullback_restrictionDegree_zero` (invertible-sheaf form) and
`exceptional_pullback_pairing_zero_hom` (the `picardRestrictionDegreeHom` form, matching lane A2's
`exceptionalPairing`).

Not stated here: the same identity phrased for a *Cartier divisor* `D` on the base. The accepted
`Geometry/CartierDivisorPullback` constructs the pulled-back divisor from regular equation charts but
carries no `cartierPicardClass` compatibility lemma, so `E · σ^*D` cannot be reduced to the class form
without first proving that compatibility. Since the accepted `intersectionNumber` depends only on the
Picard class (`intersectionNumber_eq_picardRestrictionDegree`), the class form below is the substance of
`σ^*D · E = 0`; the divisor form is a packaging step waiting on that missing lemma.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Geometry.PointBlowupSplitting

open KltDP.Geometry.NormalProjectiveSurface KltDP.Literature.Stacks

variable {k : Type u} [Field k] [IsAlgClosed k] {R : Type u} [CommRing R]
  (S : NormalProjectiveSurface k) (j : Spec (CommRingCat.of R) ⟶ S.toScheme) [IsOpenImmersion j]
  (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
  (hclosed : IsClosed ({j.base q} : Set S.toScheme))
  (hR : BlowupChartRegularLiteral k) (hP : RegularProperProjectiveLiteral k)
  (hreg : ∀ x : S.Point, RegularPoint S.toScheme x)

/-- The centre fibre maps to the reduced centre, and that is the factorisation of `E ↪ T → S` through a
point: it is the defining pullback square of the accepted `globalCenterFiber`. -/
theorem globalCenterFiberι_projection :
    PointBlowupGluing.globalCenterFiberι j q hclosed ≫ PointBlowupGluing.projection j q hclosed =
      PointBlowupGluing.globalCenterFiberToCenter j q hclosed ≫
        PointBlowupGluing.closedCenterInclusion j q :=
  pullback.condition

/-- **`E · σ^*L = 0`** for every invertible sheaf `L` on the base. -/
theorem exceptional_pullback_restrictionDegree_zero
    (eF : PointBlowupGluing.globalCenterFiber j q hclosed ≅ projectiveSpace k 1)
    (L : InvertibleSheaf S.toScheme) :
    (exceptionalCurve S j q hclosed hR hP hreg eF).restrictionDegree
      (pullbackInvertibleSheaf (PointBlowupGluing.projection j q hclosed) L) = 0 := by
  letI : IsIntegral (PointBlowupGluing.globalCenterFiber j q hclosed) :=
    PrimeCurveOfClosedImmersion.isIntegral_of_iso_projectiveLine eF
  letI : Field (R ⧸ q.asIdeal) := Ideal.Quotient.field _
  exact PrimeCurveInclusionLift.restrictionDegree_pullback_eq_zero
    (exceptionalCurve S j q hclosed hR hP hreg eF)
    (PointBlowupGluing.globalCenterFiberι j q hclosed) rfl
    (PointBlowupGluing.projection j q hclosed)
    (PointBlowupGluing.globalCenterFiberToCenter j q hclosed)
    (PointBlowupGluing.closedCenterInclusion j q)
    (globalCenterFiberι_projection S j q hclosed) L

/-- **`E · σ^*c = 0`** for every Picard class `c` of the base: the exceptional curve of the blowup
pairs to zero with everything pulled back from below. -/
theorem exceptional_pullback_pairing_zero
    (eF : PointBlowupGluing.globalCenterFiber j q hclosed ≅ projectiveSpace k 1)
    (c : S.toScheme.Pic) :
    (exceptionalCurve S j q hclosed hR hP hreg eF).picardRestrictionDegree
      (schemePicardPullbackHom (PointBlowupGluing.projection j q hclosed) c) = 0 := by
  letI : IsIntegral (PointBlowupGluing.globalCenterFiber j q hclosed) :=
    PrimeCurveOfClosedImmersion.isIntegral_of_iso_projectiveLine eF
  letI : Field (R ⧸ q.asIdeal) := Ideal.Quotient.field _
  exact PrimeCurveInclusionLift.picardRestrictionDegree_pullback_eq_zero
    (exceptionalCurve S j q hclosed hR hP hreg eF)
    (PointBlowupGluing.globalCenterFiberι j q hclosed) rfl
    (PointBlowupGluing.projection j q hclosed)
    (PointBlowupGluing.globalCenterFiberToCenter j q hclosed)
    (PointBlowupGluing.closedCenterInclusion j q)
    (globalCenterFiberι_projection S j q hclosed) c

/-- The `picardRestrictionDegreeHom` form, matching lane A2's `exceptionalPairing`. -/
theorem exceptional_pullback_pairing_zero_hom
    (eF : PointBlowupGluing.globalCenterFiber j q hclosed ≅ projectiveSpace k 1)
    (c : Additive S.toScheme.Pic) :
    (blowupSurf S j q hclosed hR hP hreg).picardRestrictionDegreeHom
        (exceptionalCurve S j q hclosed hR hP hreg eF)
        ((schemePicardPullbackHom (PointBlowupGluing.projection j q hclosed)).toAdditive c) = 0 := by
  letI : IsIntegral (PointBlowupGluing.globalCenterFiber j q hclosed) :=
    PrimeCurveOfClosedImmersion.isIntegral_of_iso_projectiveLine eF
  letI : Field (R ⧸ q.asIdeal) := Ideal.Quotient.field _
  exact PrimeCurveInclusionLift.picardRestrictionDegreeHom_pullback_eq_zero
    (exceptionalCurve S j q hclosed hR hP hreg eF)
    (PointBlowupGluing.globalCenterFiberι j q hclosed) rfl
    (PointBlowupGluing.projection j q hclosed)
    (PointBlowupGluing.globalCenterFiberToCenter j q hclosed)
    (PointBlowupGluing.closedCenterInclusion j q)
    (globalCenterFiberι_projection S j q hclosed) c

/-- Universe check at `Type`/`Scheme.{0}`. -/
example (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (R₀ : Type) [CommRing R₀]
    (S₀ : NormalProjectiveSurface k₀) (j₀ : Spec (CommRingCat.of R₀) ⟶ S₀.toScheme)
    [IsOpenImmersion j₀] (q₀ : PrimeSpectrum R₀) [q₀.asIdeal.IsMaximal]
    (hclosed₀ : IsClosed ({j₀.base q₀} : Set S₀.toScheme)) (hR₀ : BlowupChartRegularLiteral k₀)
    (hP₀ : RegularProperProjectiveLiteral k₀)
    (hreg₀ : ∀ x : S₀.Point, RegularPoint S₀.toScheme x)
    (eF₀ : PointBlowupGluing.globalCenterFiber j₀ q₀ hclosed₀ ≅ projectiveSpace k₀ 1)
    (c₀ : S₀.toScheme.Pic) :
    (exceptionalCurve S₀ j₀ q₀ hclosed₀ hR₀ hP₀ hreg₀ eF₀).picardRestrictionDegree
      (schemePicardPullbackHom (PointBlowupGluing.projection j₀ q₀ hclosed₀) c₀) = 0 :=
  exceptional_pullback_pairing_zero S₀ j₀ q₀ hclosed₀ hR₀ hP₀ hreg₀ eF₀ c₀

end KltDP.Geometry.PointBlowupSplitting

import KltDP.Geometry.PointBlowupSNCBoundaryParameters
import KltDP.Geometry.StrictNormalCrossingsEquiv

/-!
# Original affine numerators adapted to the actual SNC germ

The actual SNC germ produces its own parameter pair. The existing
localization numerator and denominator-unit construction then gives
original affine elements, without assuming coordinate alignment.
Unit rescaling preserves their maximal-ideal span, so actual smooth
centre regularity proves both original regular-pair conditions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Geometry

private theorem span_pair_unit_mul {A : Type u} [CommRing A]
    (f g : A) (v w : Aˣ) :
    Ideal.span {(v : A) * f, (w : A) * g} = Ideal.span {f, g} := by
  calc
    Ideal.span {(v : A) * f, (w : A) * g} =
        Ideal.span {(v : A) * f} ⊔ Ideal.span {(w : A) * g} := Ideal.span_insert _ _
    _ = Ideal.span {f} ⊔ Ideal.span {g} := congrArg₂ (fun I J : Ideal A => I ⊔ J)
      (Ideal.span_singleton_mul_left_unit v.isUnit f)
      (Ideal.span_singleton_mul_left_unit w.isUnit g)
    _ = Ideal.span {f, g} := (Ideal.span_insert _ _).symm

namespace NormalProjectiveSurface

open LocalizedParameterReesChart

variable {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]

/-- The original affine numerators of the actual SNC parameters generate
the original localized centre, form a genuine regular pair, and retain
the zero-, one-, or two-branch equation up to an actual unit. -/
theorem pointBlowup_snc_original_parameters
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))
    (c : Localization.AtPrime q.asIdeal)
    (hc : IsStrictNormalCrossingsEquation (Localization.AtPrime q.asIdeal) c) :
    ∃ a b : q.asIdeal,
      Ideal.span {algebraMap R (Localization.AtPrime q.asIdeal) (a : R),
        algebraMap R (Localization.AtPrime q.asIdeal) (b : R)} = localCenter q.asIdeal ∧
      algebraMap R (Localization.AtPrime q.asIdeal) (a : R) ∈
        nonZeroDivisors (Localization.AtPrime q.asIdeal) ∧
      Ideal.Quotient.mk
          (Ideal.span {algebraMap R (Localization.AtPrime q.asIdeal) (a : R)})
          (algebraMap R (Localization.AtPrime q.asIdeal) (b : R)) ∈
        nonZeroDivisors (Localization.AtPrime q.asIdeal ⧸
          Ideal.span {algebraMap R (Localization.AtPrime q.asIdeal) (a : R)}) ∧
      (IsUnit c ∨ ∃ v : (Localization.AtPrime q.asIdeal)ˣ,
        c = (v : Localization.AtPrime q.asIdeal) *
            algebraMap R (Localization.AtPrime q.asIdeal) (a : R) ∨
        c = (v : Localization.AtPrime q.asIdeal) *
          (algebraMap R (Localization.AtPrime q.asIdeal) (a : R) *
            algebraMap R (Localization.AtPrime q.asIdeal) (b : R))) := by
  obtain ⟨f, g, hfg, hform⟩ := X.pointBlowup_snc_boundary_parameters j q hclosed c hc
  let a := originalNumerator q.asIdeal f
  let b := originalNumerator q.asIdeal g
  let vf := denominatorUnit q.asIdeal f
  let vg := denominatorUnit q.asIdeal g
  have ha : algebraMap R (Localization.AtPrime q.asIdeal) (a : R) =
      (vf : Localization.AtPrime q.asIdeal) * (f : Localization.AtPrime q.asIdeal) :=
    mappedNumerator_eq q.asIdeal f
  have hb : algebraMap R (Localization.AtPrime q.asIdeal) (b : R) =
      (vg : Localization.AtPrime q.asIdeal) * (g : Localization.AtPrime q.asIdeal) :=
    mappedNumerator_eq q.asIdeal g
  have hspan : Ideal.span {algebraMap R (Localization.AtPrime q.asIdeal) (a : R),
      algebraMap R (Localization.AtPrime q.asIdeal) (b : R)} = localCenter q.asIdeal := by
    calc
      _ = Ideal.span {(vf : Localization.AtPrime q.asIdeal) * f,
          (vg : Localization.AtPrime q.asIdeal) * g} :=
        congrArg₂ (fun x y : Localization.AtPrime q.asIdeal => Ideal.span {x, y}) ha hb
      _ = Ideal.span {(f : Localization.AtPrime q.asIdeal),
          (g : Localization.AtPrime q.asIdeal)} := span_pair_unit_mul _ _ vf vg
      _ = _ := hfg
  let e := openImmersionStalkLocalizationEquiv j q
  have hR : RegularLocal (Localization.AtPrime q.asIdeal) :=
    regularLocal_of_ringEquiv e (X.regularPoints_of_isSmooth (j.base q))
  have hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 2 :=
    (ringKrullDim_eq_of_ringEquiv e).symm.trans
      (X.closed_stalk_dimension_two (j.base q) hclosed)
  have hmax : localCenter q.asIdeal = maximalIdeal (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.map_eq_maximalIdeal (I := q.asIdeal)
  have hpair := RegularLocalTwoParameters.regular_pair hR hdim _ _ (hspan.trans hmax)
  refine ⟨a, b, hspan, hpair.1, hpair.2, ?_⟩
  rcases hform with hu | ⟨v, hv | hv⟩
  · exact Or.inl hu
  · refine Or.inr ⟨v * vf⁻¹, Or.inl ?_⟩
    rw [ha, Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
    exact hv
  · refine Or.inr ⟨v * vf⁻¹ * vg⁻¹, Or.inr ?_⟩
    calc
      c = (v : Localization.AtPrime q.asIdeal) * (f * g) := hv
      _ = (v : Localization.AtPrime q.asIdeal) *
          (((vf⁻¹ : (Localization.AtPrime q.asIdeal)ˣ) : Localization.AtPrime q.asIdeal) * vf) *
          (((vg⁻¹ : (Localization.AtPrime q.asIdeal)ˣ) : Localization.AtPrime q.asIdeal) * vg) *
          (f * g) := by simp
      _ = _ := by rw [ha, hb]; simp only [Units.val_mul]; ring

end NormalProjectiveSurface
end KltDP.Geometry

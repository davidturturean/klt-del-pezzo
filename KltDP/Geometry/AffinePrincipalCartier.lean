import KltDP.Geometry.CartierDivisorOfEquations

/-!
# Principal effective Cartier divisors on the spectrum of a domain

For a domain `R`, every nonzero element `f` gives the principal Cartier divisor `specDivisor f` on
`Spec R` (accepted `principalCartierDivisorHom`), additive in `f`, with the single regular equation chart
`⊤` and coefficient `f`, hence effective with regular equations; the evaluation ideal of its canonical
section (accepted `effectiveCartierSection_evaluationIdeal`) is the ideal `(f)`, and its Picard class
is trivial. This is the chart-level building block for effective Cartier divisors given by regular
equations on affine charts.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

variable (R : Type u) [CommRing R]

/-- Elements of `R` as global sections of `Spec R`. -/
def specSectionHom : R →+* Γ(Spec (CommRingCat.of R), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem specSectionHom_injective : Function.Injective (specSectionHom R) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.injective

variable [IsDomain R]
variable {R}

/-- The rational function of a nonzero element. -/
def specRational (f : R) (hf : f ≠ 0) : (Spec (CommRingCat.of R)).functionFieldˣ :=
  Units.mk0 ((Spec (CommRingCat.of R)).germToFunctionField ⊤ (specSectionHom R f)) (by
    intro h
    apply hf
    apply specSectionHom_injective R
    rw [map_zero]
    apply (Spec (CommRingCat.of R)).germToFunctionField_injective ⊤
    rw [map_zero]
    exact h)

theorem specRational_val (f : R) (hf : f ≠ 0) :
    (specRational f hf : (Spec (CommRingCat.of R)).functionField) =
      (Spec (CommRingCat.of R)).germToFunctionField ⊤ (specSectionHom R f) := rfl

theorem specRational_mul (f g : R) (hf : f ≠ 0) (hg : g ≠ 0) :
    specRational (f * g) (mul_ne_zero hf hg) = specRational f hf * specRational g hg := by
  apply Units.ext
  rw [Units.val_mul, specRational_val, specRational_val, specRational_val, map_mul, map_mul]

theorem specRational_pow (f : R) (hf : f ≠ 0) (n : ℕ) :
    specRational (f ^ n) (pow_ne_zero n hf) = specRational f hf ^ n := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, specRational_val, specRational_val, map_pow, map_pow]

/-- The principal Cartier divisor of a nonzero element of `R` on `Spec R`. -/
def specDivisor (f : R) (hf : f ≠ 0) : CartierDivisor (Spec (CommRingCat.of R)) :=
  principalCartierDivisorHom (Spec (CommRingCat.of R)) (Additive.ofMul (specRational f hf))

theorem specDivisor_congr {f g : R} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f = g) :
    specDivisor f hf = specDivisor g hg := by
  subst hfg
  rfl

theorem specDivisor_mul (f g : R) (hf : f ≠ 0) (hg : g ≠ 0) :
    specDivisor (f * g) (mul_ne_zero hf hg) = specDivisor f hf + specDivisor g hg := by
  rw [specDivisor, specDivisor, specDivisor, specRational_mul f g hf hg, ofMul_mul, map_add]

theorem specDivisor_pow (f : R) (hf : f ≠ 0) (n : ℕ) :
    specDivisor (f ^ n) (pow_ne_zero n hf) = n • specDivisor f hf := by
  rw [specDivisor, specDivisor, specRational_pow f hf n, ofMul_pow, map_nsmul]

/-- The whole spectrum is an equation chart of the principal divisor. -/
def specDivisor_chart (f : R) (hf : f ≠ 0) :
    CartierEquationChart (Spec (CommRingCat.of R)) (specDivisor f hf) where
  openSet := ⊤
  nonempty := inferInstance
  equation := specRational f hf
  represents := by
    simpa only [specDivisor, principalCartierDivisorHom] using
      (cartierEquationClassHom_restrict (Spec (CommRingCat.of R))
        (show (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ⊤ from le_rfl) (specRational f hf)).symm

/-- The element itself is a regular coefficient on the whole spectrum. -/
def specDivisor_regularChart (f : R) (hf : f ≠ 0) :
    RegularCartierEquationChart (Spec (CommRingCat.of R)) (specDivisor f hf) where
  chart := specDivisor_chart f hf
  coefficient := specSectionHom R f
  germ_eq := rfl

theorem specDivisor_hasRegularEquations (f : R) (hf : f ≠ 0) :
    HasRegularCartierEquations (Spec (CommRingCat.of R)) (specDivisor f hf) :=
  fun _ => ⟨specDivisor_regularChart f hf, trivial⟩

/-- The zero scheme of the principal divisor (evaluation ideal of its canonical section) is `(f)`. -/
theorem specDivisor_zeroScheme_ideal (f : R) (hf : f ≠ 0) :
    sectionEvaluationIdeal (Spec (CommRingCat.of R))
        (cartierDivisorModule (Spec (CommRingCat.of R)) (specDivisor f hf))
        (effectiveCartierSection (Spec (CommRingCat.of R)) (specDivisor f hf)
          (specDivisor_hasRegularEquations f hf)) ⊤ =
      Ideal.span {specSectionHom R f} :=
  effectiveCartierSection_evaluationIdeal (Spec (CommRingCat.of R)) (specDivisor f hf)
    (specDivisor_hasRegularEquations f hf) (specDivisor_regularChart f hf)

theorem specDivisor_picard (f : R) (hf : f ≠ 0) :
    cartierPicardHom (Spec (CommRingCat.of R)) (specDivisor f hf) = 0 :=
  cartierPicardHom_principal (Spec (CommRingCat.of R)) _

end KltDP.Geometry

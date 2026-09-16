import KltDP.Geometry.PrimeCurveIntersectionAdditive
import KltDP.Geometry.PrimeCurveIntersectionZero
import KltDP.Geometry.PrimeCurveIntersectionLocalLength
import KltDP.Geometry.CartierPicardHom
import KltDP.Geometry.SchemeInvertibleSheafPullback

/-!
# The F03 intersection laws on a prime curve

For a prime curve `C` on a normal projective surface over `k` and effective Cartier divisors `D`
with regular local equations not containing `C` in their support, the intersection number
`C·D = intersectionDegree C D hD hC = dim_k Γ(C ∩ D, O)` satisfies:
1. it is the degree of the restricted line bundle `O_C(D|_C)` and of the pulled-back line bundle
   `i^*O_X(D)` (Stacks 0AYY, task 12);
2. additivity `C·(D₁ + D₂) = C·D₁ + C·D₂` (task 13, through the admitted 0AYX additivity);
3. nonnegativity and the zero criterion `C·D = 0 ↔ C ∩ D = ∅`;
4. dependence only on the linear-equivalence class of `D` (the Picard class of `O_X(D)`), in
   particular invariance under adding a principal divisor;
5. the sum over the points of `C ∩ D` of the local `k`-dimensions (accepted 3b(i));
6. (separately, `intersectionDegree_eq_sum_cartierOrderAt`) the local-length form at regular points of
   `C` (accepted 3b(ii), for `k` algebraically closed).
Items 1–5 and the sum over points are bundled in `f03_prime_curve_intersection_laws`. Symmetry and the self-intersection `C·C`
are not part of this statement.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped BigOperators

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)

/-- **Class dependence**: divisors with the same Picard class have the same intersection number
with `C`. -/
theorem intersectionDegree_eq_of_cartierPicardClass_eq (D₁ D₂ : CartierDivisor X.toScheme)
    (hD₁ : HasRegularCartierEquations X.toScheme D₁) (hD₂ : HasRegularCartierEquations X.toScheme D₂)
    (hC₁ : C.NotInSupport D₁ hD₁) (hC₂ : C.NotInSupport D₂ hD₂)
    (h : cartierPicardClass X.toScheme D₁ = cartierPicardClass X.toScheme D₂) :
    C.intersectionDegree D₁ hD₁ hC₁ = C.intersectionDegree D₂ hD₂ hC₂ := by
  have hpic : (pullbackInvertibleSheaf C.inclusion (cartierDivisorInvertibleSheaf X.toScheme D₁)).toPic =
      (pullbackInvertibleSheaf C.inclusion (cartierDivisorInvertibleSheaf X.toScheme D₂)).toPic := by
    rw [← schemePicardPullbackHom_toPic, ← schemePicardPullbackHom_toPic]
    exact congrArg (schemePicardPullbackHom C.inclusion) h
  have h1 := C.lineDegree_pullback_eq_intersectionDegree D₁ hD₁ hC₁
  have h2 := C.lineDegree_pullback_eq_intersectionDegree D₂ hD₂ hC₂
  have h3 := C.lineDegree_eq_of_toPic_eq hpic
  exact_mod_cast h1.symm.trans (h3.trans h2)

/-- Adding a principal divisor does not change the intersection number. -/
theorem intersectionDegree_add_principal (D : CartierDivisor X.toScheme)
    (hD : HasRegularCartierEquations X.toScheme D) (hC : C.NotInSupport D hD)
    (f : X.toScheme.functionFieldˣ)
    (hD' : HasRegularCartierEquations X.toScheme
      (D + principalCartierDivisorHom X.toScheme (Additive.ofMul f)))
    (hC' : C.NotInSupport (D + principalCartierDivisorHom X.toScheme (Additive.ofMul f)) hD') :
    C.intersectionDegree (D + principalCartierDivisorHom X.toScheme (Additive.ofMul f)) hD' hC' =
      C.intersectionDegree D hD hC :=
  C.intersectionDegree_eq_of_cartierPicardClass_eq _ _ hD' hD hC' hC
    (by rw [cartierPicardClass_add, cartierPicardClass_principal, mul_one])

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

namespace KltDP.Geometry

open KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- **The F03 prime-curve intersection laws.** For `C : X.PrimeCurve` on a normal projective
surface `X` over `k`, and effective Cartier divisors (`HasRegularCartierEquations`) not containing
`C` (`NotInSupport`): (1) `C·D` is the degree of `O_C(D|_C)` and of `i^*O_X(D)`; (2) additivity in
`D`; (3) nonnegativity; (4) `C·D = 0 ↔ C ∩ D = ∅`; (5) dependence only on the Picard class of
`O_X(D)`; (6) the sum over the points of `C ∩ D`. The local-length form at regular points of `C`
(`k` algebraically closed, DVR stalks) is the accepted `intersectionDegree_eq_sum_cartierOrderAt`,
stated in its own module with the stalk instances it needs. Symmetry and `C·C` are not covered.
All universes coincide (`u`). -/
theorem f03_prime_curve_intersection_laws {k : Type u} [Field k]
    {X : NormalProjectiveSurface k} (C : X.PrimeCurve) :
    (∀ (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)
        (hC : C.NotInSupport D hD),
      (C.intersectionDegree D hD hC : ℤ) =
          C.lineDegree (cartierDivisorInvertibleSheaf C.toScheme (C.restrictCartier D hD hC)) ∧
        (C.intersectionDegree D hD hC : ℤ) =
          C.lineDegree (pullbackInvertibleSheaf C.inclusion
            (cartierDivisorInvertibleSheaf X.toScheme D))) ∧
    (∀ (D₁ D₂ : CartierDivisor X.toScheme) (hD₁ : HasRegularCartierEquations X.toScheme D₁)
        (hD₂ : HasRegularCartierEquations X.toScheme D₂) (hC₁ : C.NotInSupport D₁ hD₁)
        (hC₂ : C.NotInSupport D₂ hD₂) (hD₁₂ : HasRegularCartierEquations X.toScheme (D₁ + D₂))
        (hC₁₂ : C.NotInSupport (D₁ + D₂) hD₁₂),
      C.intersectionDegree (D₁ + D₂) hD₁₂ hC₁₂ =
        C.intersectionDegree D₁ hD₁ hC₁ + C.intersectionDegree D₂ hD₂ hC₂) ∧
    (∀ (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)
        (hC : C.NotInSupport D hD), (0 : ℤ) ≤ (C.intersectionDegree D hD hC : ℤ)) ∧
    (∀ (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)
        (hC : C.NotInSupport D hD),
      C.intersectionDegree D hD hC = 0 ↔ IsEmpty (C.intersectionScheme D hD hC)) ∧
    (∀ (D₁ D₂ : CartierDivisor X.toScheme) (hD₁ : HasRegularCartierEquations X.toScheme D₁)
        (hD₂ : HasRegularCartierEquations X.toScheme D₂) (hC₁ : C.NotInSupport D₁ hD₁)
        (hC₂ : C.NotInSupport D₂ hD₂),
      cartierPicardClass X.toScheme D₁ = cartierPicardClass X.toScheme D₂ →
        C.intersectionDegree D₁ hD₁ hC₁ = C.intersectionDegree D₂ hD₂ hC₂) ∧
    (∀ (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)
        (hC : C.NotInSupport D hD),
      letI : Fintype (C.intersectionScheme D hD hC) :=
        haveI := C.intersectionScheme_finite D hD hC
          (C.range_intersectionToSurface_finite_and_isClosed D hD hC).1
        Fintype.ofFinite _
      letI : DiscreteTopology (C.intersectionScheme D hD hC) :=
        DiscreteTopology.of_finite_of_isClosed_singleton
          (C.intersectionScheme_isClosed_singleton D hD hC
            (C.range_intersectionToSurface_finite_and_isClosed D hD hC).2)
      letI : ∀ z : C.intersectionScheme D hD hC,
          Module k Γ(C.intersectionScheme D hD hC, singletonOpen (C.intersectionScheme D hD hC) z) :=
        fun z => sectionsBaseModule (C.intersectionScheme D hD hC)
          (baseFieldToGlobalSections (C.intersectionToSpec D hD hC))
          (singletonOpen (C.intersectionScheme D hD hC) z)
      C.intersectionDegree D hD hC = ∑ z : C.intersectionScheme D hD hC,
        Module.finrank k Γ(C.intersectionScheme D hD hC,
          singletonOpen (C.intersectionScheme D hD hC) z)) :=
  ⟨fun D hD hC => ⟨(C.lineDegree_restrictCartier_eq_intersectionDegree D hD hC).symm,
      (C.lineDegree_pullback_eq_intersectionDegree D hD hC).symm⟩,
    fun D₁ D₂ hD₁ hD₂ hC₁ hC₂ hD₁₂ hC₁₂ =>
      C.intersectionDegree_add D₁ D₂ hD₁ hD₂ hC₁ hC₂ hD₁₂ hC₁₂,
    fun D hD hC => C.intersectionDegree_nonneg D hD hC,
    fun D hD hC => C.intersectionDegree_eq_zero_iff D hD hC,
    fun D₁ D₂ hD₁ hD₂ hC₁ hC₂ h =>
      C.intersectionDegree_eq_of_cartierPicardClass_eq D₁ D₂ hD₁ hD₂ hC₁ hC₂ h,
    fun D hD hC => C.intersectionDegree_eq_sum_points'' D hD hC⟩

/-- Universe check: the laws instantiate at a single universe `u`. -/
example {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
    (D₁ D₂ : CartierDivisor X.toScheme) (hD₁ : HasRegularCartierEquations X.toScheme D₁)
    (hD₂ : HasRegularCartierEquations X.toScheme D₂) (hC₁ : C.NotInSupport D₁ hD₁)
    (hC₂ : C.NotInSupport D₂ hD₂) (hD₁₂ : HasRegularCartierEquations X.toScheme (D₁ + D₂))
    (hC₁₂ : C.NotInSupport (D₁ + D₂) hD₁₂) :
    C.intersectionDegree (D₁ + D₂) hD₁₂ hC₁₂ =
      C.intersectionDegree D₁ hD₁ hC₁ + C.intersectionDegree D₂ hD₂ hC₂ :=
  (f03_prime_curve_intersection_laws C).2.1 D₁ D₂ hD₁ hD₂ hC₁ hC₂ hD₁₂ hC₁₂

end KltDP.Geometry

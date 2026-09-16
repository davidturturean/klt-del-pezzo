import KltDP.Geometry.PrimeCurveComplementPicardKernel
import KltDP.Geometry.PrimeCurveIntersectionNumber

/-!
# Infinite order of `[O_X(E)]` from `E · E = −1`, and `Pic ≃ Pic × ℤ`

BRIEF32, task 2 (F09 step (iv), conditional form). On a normal projective surface with factorial
stalks, the class `[O_X(E)]` of a prime curve `E` with `E · E = −1` has infinite order: the accepted
F03 pairing `picardRestrictionDegreeHom` at `E` is an additive map `Pic X → ℤ` sending `[O_X(E)]` to
`E · E = −1`, so it sends `[O_X(E)]^n` to `−n`, which vanishes only for `n = 0`.

* **`infiniteOrder_of_intersectionNumber_neg_one`**: `E · E = −1` implies
  `InfiniteOrder (primeCurveClass E)`, the named hypothesis of
  `Geometry/PrimeCurveComplementPicardKernel`. The self-intersection enters exactly as the accepted
  `PrimeCurve.intersectionNumber E (cartierWeilEquiv.symm (single E 1))`, which is the accepted
  `selfIntersectionNumber` on a regular surface (where `regularCartierWeilEquiv` is `cartierWeilEquiv`).
  It is **carried as a hypothesis**: the generic `E · E = −1` for the exceptional curve of a point
  blowup is lane E's BRIEF_E4 item 3, and is not reproved here.
* **`picardEquivProdInt`**: any retraction `ρ` of a homomorphism `s : H →* Pic X` whose kernel is the
  kernel of restriction to `X ∖ E` splits `Pic X ≃* H × ℤ` — BRIEF29's `splitEquiv` composed with
  `kernelEquivInt`. For the blowup of a closed point this is `Pic T ≃* Pic S × ℤ`, with `s` the
  pullback `σ^*` and `ρ` BRIEF29's `retraction` (whose kernel is `ker (Pic T → Pic (T ∖ E))` by the
  accepted `ker_retraction`, and BRIEF31's `restrictPuncture_bijective` supplies `hρ`).

Open: the identification of the exceptional curve of a general point blowup as a prime curve `E` with
`T ∖ E` its complement and `E · E = −1` (lane E).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

namespace KltDP.Geometry.PrimeCurveComplementKernel

open KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] {X : NormalProjectiveSurface k}
  [∀ y : X.toScheme, UniqueFactorizationMonoid (X.stalk y)]

/-! ## Infinite order from the self-intersection -/

/-- The accepted F03 restriction degree of the class of a prime divisor along that curve is its
self-intersection number. -/
theorem picardRestrictionDegree_primeCurveClass (E : X.PrimeCurve) :
    E.picardRestrictionDegree (primeCurveClass E) =
      E.intersectionNumber (X.cartierWeilEquiv.symm (Finsupp.single E 1)) := by
  have hrep : primeCurveClass E =
      cartierPicardClass X.toScheme (X.cartierWeilEquiv.symm (Finsupp.single E 1)) :=
    X.weilClassPicardEquiv_representative (Finsupp.single E 1)
  rw [hrep]
  exact (E.intersectionNumber_eq_picardRestrictionDegree
    (X.cartierWeilEquiv.symm (Finsupp.single E 1))).symm

/-- **Step (iv), conditional form: a `(−1)`-curve has a class of infinite order.** The only input is
`E · E = −1` in the accepted F03 pairing. -/
theorem infiniteOrder_of_intersectionNumber_neg_one (E : X.PrimeCurve)
    (hEE : E.intersectionNumber (X.cartierWeilEquiv.symm (Finsupp.single E 1)) = -1) :
    InfiniteOrder (primeCurveClass E) := by
  intro n hn
  -- `picardRestrictionDegreeHom` is by definition `p ↦ C.picardRestrictionDegree p.toMul`.
  have hval : X.picardRestrictionDegreeHom E (Additive.ofMul (primeCurveClass E)) = -1 :=
    (picardRestrictionDegree_primeCurveClass E).trans hEE
  have h1 : X.picardRestrictionDegreeHom E (Additive.ofMul (primeCurveClass E ^ n)) =
      n • X.picardRestrictionDegreeHom E (Additive.ofMul (primeCurveClass E)) := by
    rw [ofMul_zpow, map_zsmul]
  rw [hn, show Additive.ofMul (1 : X.toScheme.Pic) = 0 from rfl, map_zero, hval] at h1
  simp only [zsmul_eq_mul, smul_eq_mul, mul_neg_one, mul_one] at h1
  omega

/-! ## The splitting `Pic X ≃* H × ℤ` -/

variable {V : X.toScheme.Opens} [Nonempty V.toScheme]

/-- **`Pic X ≃* H × ℤ`**: a retraction of `s : H →* Pic X` whose kernel is the kernel of restriction
to `X ∖ E` splits the Picard group, the second factor being `ℤ · [O_X(E)]`. -/
def picardEquivProdInt {H : Type v} [CommGroup H] (E : X.PrimeCurve)
    (hV : ∀ C : X.PrimeCurve, C.genericPoint ∈ V ↔ C ≠ E)
    (hinf : InfiniteOrder (primeCurveClass E))
    (s : H →* X.toScheme.Pic) (ρ : X.toScheme.Pic →* H) (hρ : ∀ a, ρ (s a) = a)
    (hker : ρ.ker = (schemePicardPullbackHom V.ι).ker) :
    X.toScheme.Pic ≃* H × Multiplicative ℤ :=
  (PointBlowupPicard.splitEquiv s ρ hρ).trans
    (MulEquiv.prodCongr (MulEquiv.refl H)
      ((MulEquiv.subgroupCongr hker).trans (kernelEquivInt E hV hinf)))

/-- The same splitting with the self-intersection hypothesis in place of the infinite-order one. -/
def picardEquivProdInt_of_intersectionNumber {H : Type v} [CommGroup H] (E : X.PrimeCurve)
    (hV : ∀ C : X.PrimeCurve, C.genericPoint ∈ V ↔ C ≠ E)
    (hEE : E.intersectionNumber (X.cartierWeilEquiv.symm (Finsupp.single E 1)) = -1)
    (s : H →* X.toScheme.Pic) (ρ : X.toScheme.Pic →* H) (hρ : ∀ a, ρ (s a) = a)
    (hker : ρ.ker = (schemePicardPullbackHom V.ι).ker) :
    X.toScheme.Pic ≃* H × Multiplicative ℤ :=
  picardEquivProdInt E hV (infiniteOrder_of_intersectionNumber_neg_one E hEE) s ρ hρ hker

/-- Universe check at `Type`/`Scheme.{0}`. -/
example (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (X₀ : NormalProjectiveSurface k₀)
    [∀ y : X₀.toScheme, UniqueFactorizationMonoid (X₀.stalk y)] (E₀ : X₀.PrimeCurve)
    (hEE : E₀.intersectionNumber (X₀.cartierWeilEquiv.symm (Finsupp.single E₀ 1)) = -1) :
    InfiniteOrder (primeCurveClass E₀) :=
  infiniteOrder_of_intersectionNumber_neg_one E₀ hEE

end KltDP.Geometry.PrimeCurveComplementKernel

import KltDP.Geometry.PrimeCurveIntersectionSymm
import KltDP.Geometry.CartierEulerPairingTwisted
import KltDP.Geometry.RegularSurfaceWeilPicard
import KltDP.Geometry.CartierPicardComparison

/-!
# The symmetric bilinear intersection pairing on divisors and on `Pic` (the F03 remainder)

The accepted tree has the Euler-characteristic pairing `cartierEulerPairing` — symmetric and
class-invariant, but additive only against effective divisors with regular equations
(`cartierEulerPairing_add_left_of_hasRegularEquations`) or against prime-curve divisors
(`cartierEulerPairing_add_left`). Bilinearity in general is the vanishing of the third finite
difference of `D ↦ χ(O(−D))`, which needs Riemann–Roch; the survey of the three possible routes is
in `laneE/F03_PAIRING_PLAN.md`.

This module takes the third route and defines the pairing in prime-curve coordinates, through the
accepted `regularCartierWeilEquiv : CartierDivisor ≃+ WeilDivisor` of a regular surface (so neither
ampleness nor a "difference of effective divisors" step is needed):

  `intersectionPairing D₁ D₂ := Σ_C Σ_{C'} a_C · b_{C'} · (C · D_{C'})`,  `a = cartierToWeilHom D₁`,
  `b = cartierToWeilHom D₂`.

* `addMonoidHom_eq_weil_sum`: every additive map on Cartier divisors is determined by its values on
  prime-curve divisors, `f D = Σ_C a_C · f (D_C)`; with `intersectionNumberHom` this is
  `intersectionNumber_eq_weil_sum`.
* **Bilinear, unconditionally**: `intersectionPairing_add_left`, `_add_right`, `_zero_left`,
  `_zero_right`, `_neg_left`, `_neg_right`; **mixed form** `intersectionPairing_eq_weil_sum_right`
  (`D₁ · D₂ = Σ_C a_C · (C · D₂)`); **class invariance in the second argument** and **vanishing
  against principal divisors** there (accepted `intersectionNumber_eq_of_cartierPicardClass_eq`,
  `intersectionNumber_principal`).
* Under the named hypothesis `PrimeCurveIntersectionSymmetric` (the matrix `(C, C') ↦ C · D_{C'}` is
  symmetric; the accepted `intersectionNumber_symm` gives it for curves off each other's support,
  `primeCurveIntersectionSymmetric_of_notInSupport`, and the diagonal is trivial): **symmetry**
  `intersectionPairing_comm`, class invariance in the first argument, the identification
  `intersectionPairing_primeCurveCartier : D · D_C = intersectionNumber C D` with the accepted F03
  intersection number, and agreement with the accepted Euler pairing against a prime curve
  (`intersectionPairing_eq_cartierEulerPairing_primeCurveCartier`).
* **On `Pic`**: `picardPairing` (descent along the accepted surjection `cartierPicardClass`), its
  characterisation `picardPairing_cartierPicardClass`, symmetry, bilinearity, and
  `selfIntersection L := picardPairing L.toPic L.toPic`, which for a prime-curve class is the
  accepted `selfIntersectionNumber` (`selfIntersection_cartierDivisorInvertibleSheaf_primeCurve`).
* **Comparison with the Euler pairing**: under the single named hypothesis
  `CartierEulerPairingAdditive` (the accepted pairing is additive in its second argument for an
  arbitrary first argument — Riemann–Roch would discharge it), the two pairings agree everywhere
  (`cartierEulerPairing_eq_intersectionPairing`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- The intersection matrix entry `C · C' = C · D_{C'}`. -/
def primeCurveMatrix (C C' : X.PrimeCurve) : ℤ :=
  C.intersectionNumber (X.primeCurveCartier hregular C')

/-- **Named hypothesis**: the prime-curve intersection matrix is symmetric. -/
def PrimeCurveIntersectionSymmetric : Prop :=
  ∀ C C' : X.PrimeCurve, primeCurveMatrix X hregular C C' = primeCurveMatrix X hregular C' C

/-- The accepted `intersectionNumber_symm`, in matrix form, for curves off each other's support. -/
theorem primeCurveIntersectionSymmetric_of_notInSupport (C C' : X.PrimeCurve)
    (hC : C.NotInSupport (X.primeCurveCartier hregular C')
      (X.primeCurveCartier_hasRegularEquations hregular C'))
    (hC' : C'.NotInSupport (X.primeCurveCartier hregular C)
      (X.primeCurveCartier_hasRegularEquations hregular C)) :
    primeCurveMatrix X hregular C C' = primeCurveMatrix X hregular C' C :=
  X.intersectionNumber_symm hregular C C' hC hC'

/-- **An additive map on Cartier divisors is the coordinate sum of its values on prime-curve
divisors**, through the accepted `regularCartierWeilEquiv`. -/
theorem addMonoidHom_eq_weil_sum (f : CartierDivisor X.toScheme →+ ℤ)
    (D : CartierDivisor X.toScheme) :
    f D = (X.cartierToWeilHom D).sum fun C b => b * f (X.primeCurveCartier hregular C) := by
  have hD : D = (X.regularCartierWeilEquiv hregular).symm
      ((X.cartierToWeilHom D).sum Finsupp.single) := by
    rw [Finsupp.sum_single, ← X.regularCartierWeilEquiv_apply hregular D,
      AddEquiv.symm_apply_apply]
  calc f D
      = f ((X.regularCartierWeilEquiv hregular).symm
          ((X.cartierToWeilHom D).sum Finsupp.single)) := by rw [← hD]
    _ = (X.cartierToWeilHom D).sum fun C b =>
          f ((X.regularCartierWeilEquiv hregular).symm (Finsupp.single C b)) := by
        rw [map_finsuppSum, map_finsuppSum]
    _ = (X.cartierToWeilHom D).sum fun C b => b * f (X.primeCurveCartier hregular C) := by
        refine Finsupp.sum_congr fun C _ => ?_
        have hsingle : (Finsupp.single C ((X.cartierToWeilHom D) C) : X.WeilDivisor) =
            ((X.cartierToWeilHom D) C) • Finsupp.single C (1 : ℤ) := by
          rw [Finsupp.smul_single, smul_eq_mul, mul_one]
        rw [hsingle, map_zsmul, map_zsmul, zsmul_eq_mul]
        rfl

/-- Expansion of an intersection number along the Weil coordinates. -/
theorem intersectionNumber_eq_weil_sum (C : X.PrimeCurve) (D : CartierDivisor X.toScheme) :
    C.intersectionNumber D =
      (X.cartierToWeilHom D).sum fun C' b => b * primeCurveMatrix X hregular C C' := by
  rw [← C.intersectionNumberHom_apply D]
  refine (X.addMonoidHom_eq_weil_sum hregular C.intersectionNumberHom D).trans ?_
  refine Finsupp.sum_congr fun C' _ => ?_
  rw [C.intersectionNumberHom_apply]
  rfl

/-- **The intersection pairing** of two Cartier divisors, in prime-curve coordinates. -/
def intersectionPairing (D₁ D₂ : CartierDivisor X.toScheme) : ℤ :=
  (X.cartierToWeilHom D₁).sum fun C a =>
    a * (X.cartierToWeilHom D₂).sum fun C' b => b * primeCurveMatrix X hregular C C'

/-- **Mixed form**: `D₁ · D₂ = Σ_C a_C · (C · D₂)`. -/
theorem intersectionPairing_eq_weil_sum_right (D₁ D₂ : CartierDivisor X.toScheme) :
    intersectionPairing X hregular D₁ D₂ =
      (X.cartierToWeilHom D₁).sum fun C a => a * C.intersectionNumber D₂ := by
  refine Finsupp.sum_congr fun C _ => ?_
  rw [X.intersectionNumber_eq_weil_sum hregular C D₂]

/-- **Additivity in the first argument** (unconditional). -/
theorem intersectionPairing_add_left (D₁ D₁' D₂ : CartierDivisor X.toScheme) :
    intersectionPairing X hregular (D₁ + D₁') D₂ =
      intersectionPairing X hregular D₁ D₂ + intersectionPairing X hregular D₁' D₂ := by
  unfold intersectionPairing
  rw [map_add]
  exact Finsupp.sum_add_index' (fun _ => by ring) (fun _ _ _ => by ring)

/-- **Additivity in the second argument** (unconditional). -/
theorem intersectionPairing_add_right (D₁ D₂ D₂' : CartierDivisor X.toScheme) :
    intersectionPairing X hregular D₁ (D₂ + D₂') =
      intersectionPairing X hregular D₁ D₂ + intersectionPairing X hregular D₁ D₂' := by
  rw [X.intersectionPairing_eq_weil_sum_right hregular D₁ (D₂ + D₂'),
    X.intersectionPairing_eq_weil_sum_right hregular D₁ D₂,
    X.intersectionPairing_eq_weil_sum_right hregular D₁ D₂']
  unfold Finsupp.sum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun C _ => ?_
  dsimp only
  rw [C.intersectionNumber_add]
  ring

theorem intersectionPairing_zero_left (D : CartierDivisor X.toScheme) :
    intersectionPairing X hregular 0 D = 0 := by
  unfold intersectionPairing
  rw [map_zero]
  exact Finsupp.sum_zero_index

theorem intersectionPairing_zero_right (D : CartierDivisor X.toScheme) :
    intersectionPairing X hregular D 0 = 0 := by
  rw [X.intersectionPairing_eq_weil_sum_right hregular D 0]
  unfold Finsupp.sum
  refine Finset.sum_eq_zero fun C _ => ?_
  dsimp only
  rw [PrimeCurve.intersectionNumber_zero, mul_zero]

theorem intersectionPairing_neg_left (D₁ D₂ : CartierDivisor X.toScheme) :
    intersectionPairing X hregular (-D₁) D₂ = -intersectionPairing X hregular D₁ D₂ := by
  have h := X.intersectionPairing_add_left hregular D₁ (-D₁) D₂
  rw [add_neg_cancel, X.intersectionPairing_zero_left hregular D₂] at h
  omega

theorem intersectionPairing_neg_right (D₁ D₂ : CartierDivisor X.toScheme) :
    intersectionPairing X hregular D₁ (-D₂) = -intersectionPairing X hregular D₁ D₂ := by
  have h := X.intersectionPairing_add_right hregular D₁ D₂ (-D₂)
  rw [add_neg_cancel, X.intersectionPairing_zero_right hregular D₁] at h
  omega

/-- **Vanishing against a principal divisor** in the second argument: well-definedness on linear
equivalence classes there (accepted `intersectionNumber_principal`). -/
theorem intersectionPairing_principal_right (D : CartierDivisor X.toScheme)
    (f : X.toScheme.functionFieldˣ) :
    intersectionPairing X hregular D
      (principalCartierDivisorHom X.toScheme (Additive.ofMul f)) = 0 := by
  rw [X.intersectionPairing_eq_weil_sum_right hregular]
  unfold Finsupp.sum
  refine Finset.sum_eq_zero fun C _ => ?_
  dsimp only
  rw [C.intersectionNumber_principal f, mul_zero]

/-- **Class invariance in the second argument** (accepted class dependence of the intersection
number). -/
theorem intersectionPairing_eq_of_class_eq_right (D E E' : CartierDivisor X.toScheme)
    (h : cartierPicardClass X.toScheme E = cartierPicardClass X.toScheme E') :
    intersectionPairing X hregular D E = intersectionPairing X hregular D E' := by
  rw [X.intersectionPairing_eq_weil_sum_right hregular D E,
    X.intersectionPairing_eq_weil_sum_right hregular D E']
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun C _ => ?_
  dsimp only
  rw [C.intersectionNumber_eq_of_cartierPicardClass_eq E E' h]

section Symmetric

variable (hsymm : PrimeCurveIntersectionSymmetric X hregular)

include hsymm in
/-- **Symmetry** of the pairing, from the symmetry of the intersection matrix. -/
theorem intersectionPairing_comm (D₁ D₂ : CartierDivisor X.toScheme) :
    intersectionPairing X hregular D₁ D₂ = intersectionPairing X hregular D₂ D₁ := by
  unfold intersectionPairing Finsupp.sum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun C' _ => ?_
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [hsymm C C']
  ring

include hsymm in
/-- **`D · D_C = intersectionNumber C D`**: the pairing against a prime curve is the accepted F03
intersection number. -/
theorem intersectionPairing_primeCurveCartier (D : CartierDivisor X.toScheme) (C : X.PrimeCurve) :
    intersectionPairing X hregular D (X.primeCurveCartier hregular C) = C.intersectionNumber D := by
  rw [X.intersectionPairing_eq_weil_sum_right hregular D (X.primeCurveCartier hregular C),
    X.intersectionNumber_eq_weil_sum hregular C D]
  refine Finsupp.sum_congr fun C'' _ => ?_
  have hmat : C''.intersectionNumber (X.primeCurveCartier hregular C) =
      primeCurveMatrix X hregular C C'' := hsymm C'' C
  rw [hmat]

include hsymm in
/-- Against a prime-curve divisor the new pairing agrees with the accepted Euler pairing. -/
theorem intersectionPairing_eq_cartierEulerPairing_primeCurveCartier
    (D : CartierDivisor X.toScheme) (C : X.PrimeCurve) :
    intersectionPairing X hregular D (X.primeCurveCartier hregular C) =
      X.cartierEulerPairing D (X.primeCurveCartier hregular C) := by
  rw [X.intersectionPairing_primeCurveCartier hregular hsymm D C,
    X.cartierEulerPairing_primeCurveCartier hregular C D]

include hsymm in
/-- **Class invariance in the first argument**, by symmetry. -/
theorem intersectionPairing_eq_of_class_eq_left (D D' E : CartierDivisor X.toScheme)
    (h : cartierPicardClass X.toScheme D = cartierPicardClass X.toScheme D') :
    intersectionPairing X hregular D E = intersectionPairing X hregular D' E := by
  rw [X.intersectionPairing_comm hregular hsymm D E, X.intersectionPairing_comm hregular hsymm D' E]
  exact X.intersectionPairing_eq_of_class_eq_right hregular E D D' h

end Symmetric

/-! ### The pairing on the Picard group -/

/-- A Cartier divisor representing a Picard class (accepted `cartierPicardClass_surjective`). -/
def picardRepresentative (p : X.toScheme.Pic) : CartierDivisor X.toScheme :=
  Classical.choose (cartierPicardClass_surjective X.toScheme p)

omit [IsAlgClosed k] in
@[simp] theorem cartierPicardClass_picardRepresentative (p : X.toScheme.Pic) :
    cartierPicardClass X.toScheme (picardRepresentative X p) = p :=
  Classical.choose_spec (cartierPicardClass_surjective X.toScheme p)

/-- **The intersection pairing on `Pic`.** -/
def picardPairing (p q : X.toScheme.Pic) : ℤ :=
  intersectionPairing X hregular (picardRepresentative X p) (picardRepresentative X q)

section PicardSymmetric

variable (hsymm : PrimeCurveIntersectionSymmetric X hregular)

include hsymm in
/-- **Characterisation**: the Picard pairing of two divisor classes is the pairing of any
representatives. -/
theorem picardPairing_cartierPicardClass (D E : CartierDivisor X.toScheme) :
    picardPairing X hregular (cartierPicardClass X.toScheme D)
        (cartierPicardClass X.toScheme E) = intersectionPairing X hregular D E := by
  unfold picardPairing
  rw [X.intersectionPairing_eq_of_class_eq_left hregular hsymm _ D _
      (by rw [cartierPicardClass_picardRepresentative]),
    X.intersectionPairing_eq_of_class_eq_right hregular D _ E
      (by rw [cartierPicardClass_picardRepresentative])]

include hsymm in
/-- **Symmetry** of the Picard pairing. -/
theorem picardPairing_comm (p q : X.toScheme.Pic) :
    picardPairing X hregular p q = picardPairing X hregular q p :=
  X.intersectionPairing_comm hregular hsymm _ _

include hsymm in
/-- **Bilinearity** of the Picard pairing in the first argument (the group law of `Pic` is
multiplicative). -/
theorem picardPairing_mul_left (p p' q : X.toScheme.Pic) :
    picardPairing X hregular (p * p') q =
      picardPairing X hregular p q + picardPairing X hregular p' q := by
  obtain ⟨D, rfl⟩ := cartierPicardClass_surjective X.toScheme p
  obtain ⟨D', rfl⟩ := cartierPicardClass_surjective X.toScheme p'
  obtain ⟨E, rfl⟩ := cartierPicardClass_surjective X.toScheme q
  rw [← cartierPicardClass_add, X.picardPairing_cartierPicardClass hregular hsymm (D + D') E,
    X.picardPairing_cartierPicardClass hregular hsymm D E,
    X.picardPairing_cartierPicardClass hregular hsymm D' E,
    X.intersectionPairing_add_left hregular D D' E]

include hsymm in
/-- **Bilinearity** in the second argument. -/
theorem picardPairing_mul_right (p q q' : X.toScheme.Pic) :
    picardPairing X hregular p (q * q') =
      picardPairing X hregular p q + picardPairing X hregular p q' := by
  rw [X.picardPairing_comm hregular hsymm p (q * q'), X.picardPairing_comm hregular hsymm p q,
    X.picardPairing_comm hregular hsymm p q', X.picardPairing_mul_left hregular hsymm q q' p]

/-- **The self-intersection of an invertible sheaf**, `L²`. -/
def selfIntersection (L : InvertibleSheaf X.toScheme) : ℤ :=
  picardPairing X hregular L.toPic L.toPic

include hsymm in
/-- **`L² = C·C`** for the line bundle of a prime-curve divisor: the accepted
`selfIntersectionNumber`. -/
theorem selfIntersection_cartierDivisorInvertibleSheaf_primeCurve (C : X.PrimeCurve) :
    selfIntersection X hregular
        (cartierDivisorInvertibleSheaf X.toScheme (X.primeCurveCartier hregular C)) =
      C.selfIntersectionNumber hregular := by
  unfold selfIntersection
  rw [show (cartierDivisorInvertibleSheaf X.toScheme (X.primeCurveCartier hregular C)).toPic =
      cartierPicardClass X.toScheme (X.primeCurveCartier hregular C) from rfl,
    X.picardPairing_cartierPicardClass hregular hsymm (X.primeCurveCartier hregular C)
      (X.primeCurveCartier hregular C),
    X.intersectionPairing_primeCurveCartier hregular hsymm (X.primeCurveCartier hregular C) C]
  rfl

end PicardSymmetric

/-! ### Comparison with the accepted Euler pairing -/

/-- **Named hypothesis**: the accepted Euler pairing is additive in its second argument for an
arbitrary first argument. Riemann–Roch on the surface discharges it; the accepted tree proves it
only when one argument is effective with regular equations or a prime-curve divisor. -/
def CartierEulerPairingAdditive : Prop :=
  ∀ D E E' : CartierDivisor X.toScheme,
    X.cartierEulerPairing D (E + E') = X.cartierEulerPairing D E + X.cartierEulerPairing D E'

/-- **The two pairings agree**, under the additivity hypothesis for the Euler pairing and the
symmetry of the intersection matrix. -/
theorem cartierEulerPairing_eq_intersectionPairing
    (hsymm : PrimeCurveIntersectionSymmetric X hregular)
    (hadd : CartierEulerPairingAdditive X) (D₁ D₂ : CartierDivisor X.toScheme) :
    X.cartierEulerPairing D₁ D₂ = intersectionPairing X hregular D₁ D₂ := by
  have hhom : (AddMonoidHom.mk' (fun E => X.cartierEulerPairing D₁ E) (hadd D₁)) D₂ =
      (X.cartierToWeilHom D₂).sum fun C b =>
        b * (AddMonoidHom.mk' (fun E => X.cartierEulerPairing D₁ E) (hadd D₁))
          (X.primeCurveCartier hregular C) :=
    X.addMonoidHom_eq_weil_sum hregular _ D₂
  rw [X.intersectionPairing_comm hregular hsymm D₁ D₂,
    X.intersectionPairing_eq_weil_sum_right hregular D₂ D₁]
  refine hhom.trans (Finsupp.sum_congr fun C _ => ?_)
  rw [show (AddMonoidHom.mk' (fun E => X.cartierEulerPairing D₁ E) (hadd D₁))
      (X.primeCurveCartier hregular C) = X.cartierEulerPairing D₁ (X.primeCurveCartier hregular C)
    from rfl, X.cartierEulerPairing_primeCurveCartier hregular C D₁]

end KltDP.Geometry.NormalProjectiveSurface

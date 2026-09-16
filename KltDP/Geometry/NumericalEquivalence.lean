import KltDP.AdmissionProbe.CurveTensorDegreeConsumers
import KltDP.Geometry.SmoothSurfaceDivisorPicard
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Numerical equivalence and the numerical quotient `N¹(X)_ℚ`

For an actual normal projective surface `X : NormalProjectiveSurface k` over any
field, a surface Picard class is tested against EVERY actual prime curve
`C : X.PrimeCurve` through the existing restriction degree
`C.picardRestrictionDegree` (degree of the original line bundle pulled back
along the original closed immersion `C.inclusion`).

Constructed here, for any such `X` (no regularity, closure or characteristic
hypothesis):

* `picardRestrictionDegreeHom C : Additive X.toScheme.Pic →+ ℤ`, the degree along
  `C` as a homomorphism (additivity is the proved consumer
  `picardRestrictionDegree_mul` of the inactive Stacks 0AYX literal);
* `numericallyTrivialSubgroup`, the subgroup of numerically trivial integral
  classes, and `PicardNumericallyEquivalent`;
* `RationalPicard := ℚ ⊗[ℤ] Additive X.toScheme.Pic`, the actual rationalized
  Picard group, with the ℚ-linear extensions `rationalPicardRestrictionDegree C`;
* `numericallyTrivialSubmodule`, `NumericalClassGroup` (the quotient `N¹(X)_ℚ`),
  the descended degrees `numericalRestrictionDegree C`, and the actual
  homomorphism `picardNumericalMap : Pic → Pic ⊗ ℚ → N¹` whose kernel is exactly
  the numerically trivial classes; torsion classes are numerically trivial.

On a regular surface (`[IsAlgClosed k]`, every point regular), rational Weil
divisors map to `RationalPicard` through the accepted rational class map and the
accepted tensor equivalence, and the forward implications
linear ⇒ ℚ-linear ⇒ numerical are proved for actual Weil divisors, with the
integral test identified with the accepted `regularWeilRestrictionDegree`.

Everything is conditional on the single literal
`KltDP.Literature.Stacks.proper_curve_tensor_degree_literal` (inactive; through
the imported consumers) and on the accepted literature entries already in the
import cone. No new axiom, no assumed pairing, no symmetry, no local-length
comparison, no finite dimensionality or nontriviality of `N¹` is asserted; the
converse implications (numerical ⇒ ℚ-linear) are false in general and not stated.
-/

noncomputable section

open AlgebraicGeometry KltDP.Geometry
open scoped TensorProduct

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-! ### Integral Picard classes -/

/-- The actual restriction degree along one original prime curve, as a
homomorphism on the additive surface Picard group. Additivity is the proved
consumer of the (inactive) Stacks 0AYX literal; no degree law is assumed. -/
def picardRestrictionDegreeHom (C : X.PrimeCurve) : Additive X.toScheme.Pic →+ ℤ where
  toFun p := C.picardRestrictionDegree p.toMul
  map_zero' := C.picardRestrictionDegree_one
  map_add' p q :=
    KltDP.AdmissionProbe.CurveTensorDegreeConsumers.picardRestrictionDegree_mul C p.toMul q.toMul

@[simp]
theorem picardRestrictionDegreeHom_apply (C : X.PrimeCurve) (p : Additive X.toScheme.Pic) :
    X.picardRestrictionDegreeHom C p = C.picardRestrictionDegree p.toMul := rfl

/-- Restriction degree is additive under tensor product and hence turns
quotients of Picard classes into differences of degrees. -/
theorem picardRestrictionDegree_div (C : X.PrimeCurve) (p q : X.toScheme.Pic) :
    C.picardRestrictionDegree (p / q) =
      C.picardRestrictionDegree p - C.picardRestrictionDegree q := by
  have h := map_sub (X.picardRestrictionDegreeHom C) (Additive.ofMul p) (Additive.ofMul q)
  simpa only [picardRestrictionDegreeHom_apply, toMul_sub, toMul_ofMul] using h

/-- A surface Picard class is numerically trivial when its actual restriction
to every original prime curve has degree zero. The index set is all prime curves. -/
def NumericallyTrivial (p : X.toScheme.Pic) : Prop :=
  ∀ C : X.PrimeCurve, C.picardRestrictionDegree p = 0

/-- Two surface Picard classes are numerically equivalent when they have the
same actual restriction degree on every original prime curve. -/
def PicardNumericallyEquivalent (p q : X.toScheme.Pic) : Prop :=
  ∀ C : X.PrimeCurve, C.picardRestrictionDegree p = C.picardRestrictionDegree q

theorem picardNumericallyEquivalent_refl (p : X.toScheme.Pic) :
    X.PicardNumericallyEquivalent p p := fun _ => rfl

theorem picardNumericallyEquivalent_symm {p q : X.toScheme.Pic}
    (h : X.PicardNumericallyEquivalent p q) : X.PicardNumericallyEquivalent q p :=
  fun C => (h C).symm

theorem picardNumericallyEquivalent_trans {p q r : X.toScheme.Pic}
    (hpq : X.PicardNumericallyEquivalent p q) (hqr : X.PicardNumericallyEquivalent q r) :
    X.PicardNumericallyEquivalent p r :=
  fun C => (hpq C).trans (hqr C)

/-- Equal Picard classes (isomorphic original line bundles) are numerically equivalent. -/
theorem picardNumericallyEquivalent_of_eq {p q : X.toScheme.Pic} (h : p = q) :
    X.PicardNumericallyEquivalent p q := fun C => by rw [h]

/-- The numerically trivial classes form a subgroup: the intersection over all
actual prime curves of the kernels of the degree homomorphisms. -/
def numericallyTrivialSubgroup : AddSubgroup (Additive X.toScheme.Pic) :=
  ⨅ C : X.PrimeCurve, (X.picardRestrictionDegreeHom C).ker

theorem mem_numericallyTrivialSubgroup_iff (p : Additive X.toScheme.Pic) :
    p ∈ X.numericallyTrivialSubgroup ↔ X.NumericallyTrivial p.toMul := by
  simp only [numericallyTrivialSubgroup, AddSubgroup.mem_iInf, AddMonoidHom.mem_ker,
    picardRestrictionDegreeHom_apply, NumericallyTrivial]

/-- Numerical equivalence is triviality of the quotient class. -/
theorem picardNumericallyEquivalent_iff_div (p q : X.toScheme.Pic) :
    X.PicardNumericallyEquivalent p q ↔ X.NumericallyTrivial (p / q) := by
  simp only [PicardNumericallyEquivalent, NumericallyTrivial, picardRestrictionDegree_div,
    sub_eq_zero]

/-- Torsion Picard classes are numerically trivial: a positive multiple of the
degree vanishes in `ℤ`. -/
theorem numericallyTrivial_of_torsion (p : Additive X.toScheme.Pic) {n : ℕ} (hn : 0 < n)
    (h : n • p = 0) : X.NumericallyTrivial p.toMul := by
  intro C
  have hdeg := congrArg (X.picardRestrictionDegreeHom C) h
  rw [map_nsmul, map_zero, picardRestrictionDegreeHom_apply, ← natCast_zsmul, zsmul_eq_mul] at hdeg
  rcases mul_eq_zero.mp hdeg with h0 | h0
  · exact absurd h0 (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hn))
  · exact h0

/-! ### The rationalized Picard group and its numerical quotient -/

/-- The actual rationalized Picard group `Pic(X) ⊗ ℚ`, written in the pinned
scalar-extension order `ℚ ⊗[ℤ] Additive Pic` of the accepted rational endpoints. -/
abbrev RationalPicard := ℚ ⊗[ℤ] Additive X.toScheme.Pic

/-- The integer degree homomorphism along `C` with its values cast into `ℚ`. -/
def picardRestrictionDegreeRat (C : X.PrimeCurve) : Additive X.toScheme.Pic →ₗ[ℤ] ℚ :=
  (Int.castAddHom ℚ).toIntLinearMap.comp (X.picardRestrictionDegreeHom C).toIntLinearMap

theorem picardRestrictionDegreeRat_apply (C : X.PrimeCurve) (p : Additive X.toScheme.Pic) :
    X.picardRestrictionDegreeRat C p = (C.picardRestrictionDegree p.toMul : ℚ) := rfl

/-- The ℚ-linear extension of the restriction degree along `C` to the actual
rationalized Picard group, by the heterobasic tensor lift `ℚ ⊗[ℤ] M →ₗ[ℚ] ℚ`. -/
def rationalPicardRestrictionDegree (C : X.PrimeCurve) : X.RationalPicard →ₗ[ℚ] ℚ :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℚ (Additive X.toScheme.Pic →ₗ[ℤ] ℚ) (X.picardRestrictionDegreeRat C))

/-- On a pure tensor the extension is the scalar times the original integer degree. -/
@[simp]
theorem rationalPicardRestrictionDegree_tmul (C : X.PrimeCurve) (q : ℚ)
    (p : Additive X.toScheme.Pic) :
    X.rationalPicardRestrictionDegree C (q ⊗ₜ[ℤ] p) =
      q * (C.picardRestrictionDegree p.toMul : ℚ) := rfl

/-- On the canonical image `1 ⊗ p` of an integral class the extension is the
original integer degree. -/
theorem rationalPicardRestrictionDegree_inclusion (C : X.PrimeCurve)
    (p : Additive X.toScheme.Pic) :
    X.rationalPicardRestrictionDegree C (X.picardTensorInclusion p) =
      (C.picardRestrictionDegree p.toMul : ℚ) := by
  change X.rationalPicardRestrictionDegree C ((1 : ℚ) ⊗ₜ[ℤ] p) = _
  rw [rationalPicardRestrictionDegree_tmul, one_mul]

/-- Numerically trivial rational classes: simultaneous vanishing of the
extended degree on every actual prime curve. -/
def numericallyTrivialSubmodule : Submodule ℚ X.RationalPicard :=
  ⨅ C : X.PrimeCurve, LinearMap.ker (X.rationalPicardRestrictionDegree C)

theorem mem_numericallyTrivialSubmodule_iff (v : X.RationalPicard) :
    v ∈ X.numericallyTrivialSubmodule ↔
      ∀ C : X.PrimeCurve, X.rationalPicardRestrictionDegree C v = 0 := by
  simp only [numericallyTrivialSubmodule, Submodule.mem_iInf, LinearMap.mem_ker]

/-- Numerical equivalence of rational Picard classes. -/
def RationalNumericallyEquivalent (v w : X.RationalPicard) : Prop :=
  ∀ C : X.PrimeCurve,
    X.rationalPicardRestrictionDegree C v = X.rationalPicardRestrictionDegree C w

theorem rationalNumericallyEquivalent_iff_sub_mem (v w : X.RationalPicard) :
    X.RationalNumericallyEquivalent v w ↔ v - w ∈ X.numericallyTrivialSubmodule := by
  simp only [RationalNumericallyEquivalent, mem_numericallyTrivialSubmodule_iff, map_sub,
    sub_eq_zero]

/-- The numerical quotient `N¹(X)_ℚ`: the actual rationalized Picard group modulo
the numerically trivial subspace. No finite dimensionality is asserted. -/
abbrev NumericalClassGroup := X.RationalPicard ⧸ X.numericallyTrivialSubmodule

/-- The quotient map `Pic ⊗ ℚ → N¹`. -/
def rationalPicardNumericalMap : X.RationalPicard →ₗ[ℚ] X.NumericalClassGroup :=
  X.numericallyTrivialSubmodule.mkQ

theorem rationalPicardNumericalMap_surjective :
    Function.Surjective X.rationalPicardNumericalMap :=
  X.numericallyTrivialSubmodule.mkQ_surjective

theorem rationalPicardNumericalMap_eq_iff (v w : X.RationalPicard) :
    X.rationalPicardNumericalMap v = X.rationalPicardNumericalMap w ↔
      X.RationalNumericallyEquivalent v w := by
  change Submodule.Quotient.mk v = Submodule.Quotient.mk w ↔ _
  rw [Submodule.Quotient.eq, rationalNumericallyEquivalent_iff_sub_mem]

theorem rationalPicardNumericalMap_eq_zero_iff (v : X.RationalPicard) :
    X.rationalPicardNumericalMap v = 0 ↔
      ∀ C : X.PrimeCurve, X.rationalPicardRestrictionDegree C v = 0 :=
  (Submodule.Quotient.mk_eq_zero X.numericallyTrivialSubmodule).trans
    (X.mem_numericallyTrivialSubmodule_iff v)

/-- Each actual prime-curve degree descends to the numerical quotient. -/
def numericalRestrictionDegree (C : X.PrimeCurve) : X.NumericalClassGroup →ₗ[ℚ] ℚ :=
  X.numericallyTrivialSubmodule.liftQ (X.rationalPicardRestrictionDegree C) (iInf_le _ C)

@[simp]
theorem numericalRestrictionDegree_mk (C : X.PrimeCurve) (v : X.RationalPicard) :
    X.numericalRestrictionDegree C (X.rationalPicardNumericalMap v) =
      X.rationalPicardRestrictionDegree C v := rfl

/-- The descended curve tests jointly detect zero in `N¹`. -/
theorem numericalClass_eq_zero_iff (c : X.NumericalClassGroup) :
    c = 0 ↔ ∀ C : X.PrimeCurve, X.numericalRestrictionDegree C c = 0 := by
  obtain ⟨v, rfl⟩ := X.rationalPicardNumericalMap_surjective c
  simp only [numericalRestrictionDegree_mk]
  exact X.rationalPicardNumericalMap_eq_zero_iff v

theorem numericalClass_eq_iff (c d : X.NumericalClassGroup) :
    c = d ↔ ∀ C : X.PrimeCurve,
      X.numericalRestrictionDegree C c = X.numericalRestrictionDegree C d := by
  rw [← sub_eq_zero, numericalClass_eq_zero_iff]
  simp only [map_sub, sub_eq_zero]

/-! ### The homomorphism `Pic → Pic ⊗ ℚ → N¹` -/

/-- The composite of the accepted canonical map `p ↦ 1 ⊗ p` with the numerical
quotient map, as an actual integer-linear homomorphism. -/
def picardNumericalMap : Additive X.toScheme.Pic →ₗ[ℤ] X.NumericalClassGroup :=
  (X.rationalPicardNumericalMap.restrictScalars ℤ).comp X.picardTensorInclusion

theorem picardNumericalMap_apply (p : Additive X.toScheme.Pic) :
    X.picardNumericalMap p = X.rationalPicardNumericalMap ((1 : ℚ) ⊗ₜ[ℤ] p) := rfl

/-- The same map on the multiplicative Picard group. -/
def picardNumericalClass (p : X.toScheme.Pic) : X.NumericalClassGroup :=
  X.picardNumericalMap (Additive.ofMul p)

theorem picardNumericalClass_mul (p q : X.toScheme.Pic) :
    X.picardNumericalClass (p * q) = X.picardNumericalClass p + X.picardNumericalClass q := by
  unfold picardNumericalClass
  rw [ofMul_mul, map_add]

theorem picardNumericalClass_one : X.picardNumericalClass 1 = 0 := by
  unfold picardNumericalClass
  rw [ofMul_one, map_zero]

/-- The descended degree of the numerical class of an integral Picard class is
its original integer restriction degree. -/
theorem numericalRestrictionDegree_picardNumericalMap (C : X.PrimeCurve)
    (p : Additive X.toScheme.Pic) :
    X.numericalRestrictionDegree C (X.picardNumericalMap p) =
      (C.picardRestrictionDegree p.toMul : ℚ) := by
  rw [picardNumericalMap_apply, numericalRestrictionDegree_mk,
    rationalPicardRestrictionDegree_tmul, one_mul]

theorem intCast_eq_zero_iff (d : ℤ) : (d : ℚ) = 0 ↔ d = 0 := by
  constructor
  · intro h
    exact Int.cast_injective (h.trans Int.cast_zero.symm)
  · rintro rfl
    exact Int.cast_zero

/-- The kernel of `Pic → N¹` is exactly the set of numerically trivial classes:
rationalization loses no zero detection on the original integer degrees. -/
theorem picardNumericalMap_eq_zero_iff (p : Additive X.toScheme.Pic) :
    X.picardNumericalMap p = 0 ↔ X.NumericallyTrivial p.toMul := by
  rw [picardNumericalMap_apply, rationalPicardNumericalMap_eq_zero_iff]
  simp only [rationalPicardRestrictionDegree_tmul, one_mul, intCast_eq_zero_iff,
    NumericallyTrivial]

theorem picardNumericalMap_eq_iff (p q : Additive X.toScheme.Pic) :
    X.picardNumericalMap p = X.picardNumericalMap q ↔
      X.PicardNumericallyEquivalent p.toMul q.toMul := by
  rw [← sub_eq_zero, ← map_sub, picardNumericalMap_eq_zero_iff, toMul_sub]
  exact (X.picardNumericallyEquivalent_iff_div _ _).symm

theorem picardNumericalClass_eq_iff (p q : X.toScheme.Pic) :
    X.picardNumericalClass p = X.picardNumericalClass q ↔ X.PicardNumericallyEquivalent p q :=
  X.picardNumericalMap_eq_iff (Additive.ofMul p) (Additive.ofMul q)

/-- Equal rationalized Picard classes have equal numerical classes; in
particular the map `Pic → N¹` factors through `Pic ⊗ ℚ`. -/
theorem picardNumericalMap_eq_of_inclusion_eq {p q : Additive X.toScheme.Pic}
    (h : X.picardTensorInclusion p = X.picardTensorInclusion q) :
    X.picardNumericalMap p = X.picardNumericalMap q := by
  change X.rationalPicardNumericalMap (X.picardTensorInclusion p) =
    X.rationalPicardNumericalMap (X.picardTensorInclusion q)
  rw [h]

/-! ### Actual Weil divisors on a regular surface: linear ⇒ ℚ-linear ⇒ numerical -/

section Regular

variable [IsAlgClosed k] (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- Rational Weil divisors to the actual rationalized Picard group: the accepted
rational class map followed by the inverse of the accepted tensor equivalence. -/
def rationalWeilToRationalPicard : X.RationalWeilDivisor →ₗ[ℚ] X.RationalPicard :=
  (X.regularPicardTensorRationalEquiv hregular).symm.toLinearMap.comp X.rationalWeilClassMap

theorem rationalWeilToRationalPicard_apply (D : X.RationalWeilDivisor) :
    X.rationalWeilToRationalPicard hregular D =
      (X.regularPicardTensorRationalEquiv hregular).symm (X.rationalWeilClassMap D) := rfl

/-- Two rational divisors have the same rationalized Picard class exactly when
they are ℚ-linearly equivalent. -/
theorem rationalWeilToRationalPicard_eq_iff (D E : X.RationalWeilDivisor) :
    X.rationalWeilToRationalPicard hregular D = X.rationalWeilToRationalPicard hregular E ↔
      X.QLinearlyEquivalent D E := by
  rw [rationalWeilToRationalPicard_apply, rationalWeilToRationalPicard_apply,
    (X.regularPicardTensorRationalEquiv hregular).symm.injective.eq_iff,
    X.rationalWeilClassMap_eq_iff]

/-- An actual integral Weil divisor is sent to the canonical image of its
actual Picard class (the class of the constructed O(D)). -/
theorem rationalWeilToRationalPicard_rationalize (D : X.WeilDivisor) :
    X.rationalWeilToRationalPicard hregular (rationalizeWeilDivisor X D) =
      X.picardTensorInclusion (Additive.ofMul (X.regularWeilPicardClass hregular D)) := by
  apply (X.regularPicardTensorRationalEquiv hregular).injective
  rw [rationalWeilToRationalPicard_apply, LinearEquiv.apply_symm_apply]
  change _ = X.regularPicardTensorRationalEquiv hregular
    ((1 : ℚ) ⊗ₜ[ℤ] Additive.ofMul (X.regularWeilPicardClass hregular D))
  rw [X.regularPicardTensorRationalEquiv_one_tmul]
  change _ = X.weilClassRationalization ((X.regularWeilClassPicardEquiv hregular).symm
    (Additive.ofMul (X.regularWeilClassPicardEquiv hregular (X.weilClassMap D)).toMul))
  rw [ofMul_toMul, AddEquiv.symm_apply_apply, X.weilClassRationalization_class]

/-- Numerical equivalence of actual rational Weil divisors on the regular
surface, tested through their rationalized Picard classes on every prime curve. -/
def NumericallyEquivalent (D E : X.RationalWeilDivisor) : Prop :=
  X.RationalNumericallyEquivalent (X.rationalWeilToRationalPicard hregular D)
    (X.rationalWeilToRationalPicard hregular E)

/-- ℚ-linear equivalence implies numerical equivalence. -/
theorem numericallyEquivalent_of_qLinearlyEquivalent {D E : X.RationalWeilDivisor}
    (h : X.QLinearlyEquivalent D E) : X.NumericallyEquivalent hregular D E := by
  have hclass := (X.rationalWeilToRationalPicard_eq_iff hregular D E).mpr h
  intro C
  rw [hclass]

/-- Linear equivalence of actual integral divisors implies numerical
equivalence of their rationalizations, through the accepted
`qLinearlyEquivalent_of_linearlyEquivalent`. -/
theorem numericallyEquivalent_of_linearlyEquivalent {D E : X.WeilDivisor}
    (h : X.LinearlyEquivalent D E) :
    X.NumericallyEquivalent hregular (rationalizeWeilDivisor X D) (rationalizeWeilDivisor X E) :=
  X.numericallyEquivalent_of_qLinearlyEquivalent hregular
    (X.qLinearlyEquivalent_of_linearlyEquivalent h)

/-- On an actual integral divisor the rational test along `C` is the accepted
regular Weil restriction degree against the prime divisor `C`. -/
theorem rationalPicardRestrictionDegree_rationalize (C : X.PrimeCurve) (D : X.WeilDivisor) :
    X.rationalPicardRestrictionDegree C
        (X.rationalWeilToRationalPicard hregular (rationalizeWeilDivisor X D)) =
      (X.regularWeilRestrictionDegree hregular D (Finsupp.single C 1) : ℚ) := by
  rw [rationalWeilToRationalPicard_rationalize, rationalPicardRestrictionDegree_inclusion,
    toMul_ofMul]
  exact congrArg (fun n : ℤ => (n : ℚ)) (by
    change _ = X.picardWeilRestrictionDegree (X.regularWeilPicardClass hregular D)
      (Finsupp.single C 1)
    rw [X.picardWeilRestrictionDegree_single, one_mul])

/-- Numerical equivalence of actual integral Weil divisors: the same regular
restriction degree against every original prime curve. -/
def WeilNumericallyEquivalent (D E : X.WeilDivisor) : Prop :=
  ∀ C : X.PrimeCurve,
    X.regularWeilRestrictionDegree hregular D (Finsupp.single C 1) =
      X.regularWeilRestrictionDegree hregular E (Finsupp.single C 1)

/-- The integral test agrees with the rational test on rationalizations. -/
theorem weilNumericallyEquivalent_iff_rationalize (D E : X.WeilDivisor) :
    X.WeilNumericallyEquivalent hregular D E ↔
      X.NumericallyEquivalent hregular (rationalizeWeilDivisor X D)
        (rationalizeWeilDivisor X E) := by
  simp only [WeilNumericallyEquivalent, NumericallyEquivalent, RationalNumericallyEquivalent,
    rationalPicardRestrictionDegree_rationalize, Int.cast_injective.eq_iff]

/-- Linear equivalence implies integral numerical equivalence, directly from the
accepted invariance of the regular restriction degree. -/
theorem weilNumericallyEquivalent_of_linearlyEquivalent {D E : X.WeilDivisor}
    (h : X.LinearlyEquivalent D E) : X.WeilNumericallyEquivalent hregular D E := fun C => by
  rw [X.regularWeilRestrictionDegree_eq_of_linearlyEquivalent hregular h]

/-- Rational Weil divisors to the numerical quotient. -/
def rationalWeilNumericalMap : X.RationalWeilDivisor →ₗ[ℚ] X.NumericalClassGroup :=
  X.rationalPicardNumericalMap.comp (X.rationalWeilToRationalPicard hregular)

theorem rationalWeilNumericalMap_eq_iff (D E : X.RationalWeilDivisor) :
    X.rationalWeilNumericalMap hregular D = X.rationalWeilNumericalMap hregular E ↔
      X.NumericallyEquivalent hregular D E :=
  X.rationalPicardNumericalMap_eq_iff _ _

theorem rationalWeilNumericalMap_surjective :
    Function.Surjective (X.rationalWeilNumericalMap hregular) :=
  X.rationalPicardNumericalMap_surjective.comp
    ((X.regularPicardTensorRationalEquiv hregular).symm.surjective.comp
      X.rationalPrincipalSubmodule.mkQ_surjective)

/-- Rational linear-equivalence classes to numerical classes; this is the
second arrow of the F02 clause, descended from the accepted tensor equivalence. -/
def rationalWeilClassNumericalMap : X.RationalWeilClassGroup →ₗ[ℚ] X.NumericalClassGroup :=
  X.rationalPicardNumericalMap.comp (X.regularPicardTensorRationalEquiv hregular).symm.toLinearMap

theorem rationalWeilClassNumericalMap_class (D : X.RationalWeilDivisor) :
    X.rationalWeilClassNumericalMap hregular (X.rationalWeilClassMap D) =
      X.rationalWeilNumericalMap hregular D := rfl

/-- The Picard route and the divisor route to `N¹` agree on actual integral divisors. -/
theorem picardNumericalMap_regularWeilPicardClass (D : X.WeilDivisor) :
    X.picardNumericalMap (Additive.ofMul (X.regularWeilPicardClass hregular D)) =
      X.rationalWeilNumericalMap hregular (rationalizeWeilDivisor X D) := by
  change X.rationalPicardNumericalMap (X.picardTensorInclusion _) =
    X.rationalPicardNumericalMap (X.rationalWeilToRationalPicard hregular _)
  rw [rationalWeilToRationalPicard_rationalize]

end Regular

end KltDP.Geometry.NormalProjectiveSurface

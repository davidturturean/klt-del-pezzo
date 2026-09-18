import KltDP.Geometry.ContractionPicardSplitting
import KltDP.Geometry.BirationalPicardIntersectionPullback
import KltDP.Geometry.BirationalRationalPicardPullback
import KltDP.Geometry.RationalPicardIntersection

/-!
# The original contraction Picard splitting preserves the integral form

The normalized splitting uses the original pullback and original prime
Cartier divisor. Their mixed pairing vanishes, the pullback preserves the
target pairing, and the given actual minus-one curve has square minus one.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

open PrimeCurveClassPairing

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S T : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme}
  {E : S.PrimeCurve}

/-- The original exceptional class is orthogonal to every original
pulled-back Picard class. -/
theorem IsContraction.pairing_pullback_exceptional
    (hb : IsContraction S T b E)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s) (p : T.toScheme.Pic) :
    pairing S hS (Additive.ofMul (schemePicardPullbackHom b p))
      (cartierPicardHom S.toScheme (S.primeCurveCartier hS E)) = 0 := by
  rw [pairing_primeCurve_right]
  change E.picardRestrictionDegree (schemePicardPullbackHom b p) = 0
  obtain ⟨z, _, himage, _, _⟩ := hb.center
  exact BirationalNumericalPullback.picard_degree_exceptional b hb.over_base E
    ⟨z, himage⟩ p

/-- The self-pairing is the original self-intersection in the minus-one
curve witness, with the positive Cartier divisor convention. -/
theorem IsMinusOneCurve.pairing_self_eq_neg_one
    {hS : ∀ s : S.Point, RegularPoint S.toScheme s}
    (hminus : IsMinusOneCurve hS E) :
    pairing S hS (cartierPicardHom S.toScheme (S.primeCurveCartier hS E))
      (cartierPicardHom S.toScheme (S.primeCurveCartier hS E)) = -1 := by
  change S.picardPairing hS
    (cartierPicardClass S.toScheme (S.primeCurveCartier hS E))
    (cartierPicardClass S.toScheme (S.primeCurveCartier hS E)) = -1
  rw [S.picardPairing_class hS, S.intersectionPairing_primeCurve hS]
  exact hminus.selfIntersection

/-- The actual normalized Picard splitting identifies the original pairing
with the target pairing orthogonally summed with the rank-one form [-1]. -/
theorem IsContraction.picardDecomposition_pairing
    (hb : IsContraction S T b E)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (hminus : IsMinusOneCurve hS E)
    (p q : T.toScheme.Pic) (n m : ℤ) :
    S.picardPairing hS
      ((hb.picardDecomposition hS hminus).symm (p, Multiplicative.ofAdd n))
      ((hb.picardDecomposition hS hminus).symm (q, Multiplicative.ofAdd m)) =
      T.picardPairing hb.regular p q - n * m := by
  letI : IsProper b := hb.isProper
  let hbir : IsBirationalScheme b :=
    (isBirational_iff_isBirationalScheme b).mp hb.birational
  let B := S.integralPicardIntersectionBilinForm hS
  let cE := cartierPicardHom S.toScheme (S.primeCurveCartier hS E)
  let p' := Additive.ofMul (schemePicardPullbackHom b p)
  let q' := Additive.ofMul (schemePicardPullbackHom b q)
  have hpp : B p' q' = T.picardPairing hb.regular p q :=
    (S.integralPicardIntersectionBilinForm_apply hS p' q').trans
      (BirationalPicardIntersectionPullback.picardPairing_pullback
        b hb.over_base hbir hS hb.regular p q)
  have hpE : B p' cE = 0 :=
    (S.integralPicardIntersectionBilinForm_apply hS p' cE).trans
      (hb.pairing_pullback_exceptional hS p)
  have hEq : B cE q' = 0 :=
    (S.integralPicardIntersectionBilinForm_apply hS cE q').trans
      ((pairing_symm S hS cE q').trans (hb.pairing_pullback_exceptional hS q))
  have hEE : B cE cE = -1 :=
    (S.integralPicardIntersectionBilinForm_apply hS cE cE).trans
      hminus.pairing_self_eq_neg_one
  rw [hb.picardDecomposition_symm_apply hS hminus,
    hb.picardDecomposition_symm_apply hS hminus]
  change S.picardPairing hS (p' + n • cE).toMul (q' + m • cE).toMul = _
  rw [← S.integralPicardIntersectionBilinForm_apply hS]
  change B (p' + n • cE) (q' + m • cE) = _
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    hpp, hpE, hEq, hEE, smul_eq_mul]
  ring

end KltDP.Geometry

#check @KltDP.Geometry.IsContraction.picardDecomposition_pairing
#print axioms KltDP.Geometry.IsContraction.picardDecomposition_pairing

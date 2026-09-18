import KltDP.Geometry.ContractionPicardPairing
import KltDP.Geometry.NefLineEffectivePicardPairing
import KltDP.Geometry.DominantCartierPullbackEffective

/-!
# Nef lines descend through the actual minus-one contraction

The normalized original Picard splitting supplies the target class and
integer exceptional coefficient. Nefness makes that coefficient nonpositive.
For each original target prime, its literal Cartier pullback is effective;
the original intersection formula therefore proves the target line is nef.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.IsContraction

open PrimeCurveClassPairing

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S T : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme}
  {E : S.PrimeCurve} (hb : IsContraction S T b E)
  (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
  (hminus : IsMinusOneCurve hS E)

local instance nefDescentSourceIntegral : IsIntegral S.toScheme := S.integral
local instance nefDescentTargetIntegral : IsIntegral T.toScheme := T.integral

/-- Pairing against the original pullback reads the target component of
the actual normalized Picard decomposition. -/
theorem picardDecomposition_pairing_pullback
    (p q : T.toScheme.Pic) (m : ℤ) :
    S.picardPairing hS
      ((hb.picardDecomposition hS hminus).symm (p, Multiplicative.ofAdd m))
      (schemePicardPullbackHom b q) = T.picardPairing hb.regular p q := by
  have hpull : (hb.picardDecomposition hS hminus).symm
      (q, Multiplicative.ofAdd (0 : ℤ)) = schemePicardPullbackHom b q := by
    simpa only [zpow_zero, mul_one] using
      hb.picardDecomposition_symm_apply hS hminus q 0
  rw [← hpull]
  simpa only [mul_zero, sub_zero] using
    hb.picardDecomposition_pairing hS hminus p q m 0

/-- The original exceptional degree is minus the integer coordinate. -/
theorem picardDecomposition_pairing_exceptional (p : T.toScheme.Pic) (m : ℤ) :
    S.picardPairing hS
      ((hb.picardDecomposition hS hminus).symm (p, Multiplicative.ofAdd m))
      (cartierPicardClass S.toScheme (S.primeCurveCartier hS E)) = -m := by
  have hexc : (hb.picardDecomposition hS hminus).symm
      (1, Multiplicative.ofAdd (1 : ℤ)) =
      cartierPicardClass S.toScheme (S.primeCurveCartier hS E) := by
    simpa only [map_one, zpow_one, one_mul] using
      hb.picardDecomposition_symm_apply hS hminus 1 1
  have hzero : T.picardPairing hb.regular p 1 = 0 :=
    (T.picardPairing_symm hb.regular p 1).trans
      (pairing_zero_left T hb.regular (Additive.ofMul p))
  rw [← hexc]
  simpa only [hzero, mul_one, zero_sub] using
    hb.picardDecomposition_pairing hS hminus p 1 m 1

/-- Both the actual target nef divisor and the nonpositive exceptional
coefficient are produced from the original nef line. -/
theorem exists_nef_picardDecomposition
    (H : InvertibleSheaf S.toScheme)
    (hH : Positivity.IsNef S.structureMorphism H) :
    ∃ (A : CartierDivisor T.toScheme) (m : ℤ),
      m ≤ 0 ∧
      Positivity.IsNef T.structureMorphism (cartierDivisorInvertibleSheaf T.toScheme A) ∧
      H.toPic = (hb.picardDecomposition hS hminus).symm
        (cartierPicardClass T.toScheme A, Multiplicative.ofAdd m) := by
  letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
  let e := hb.picardDecomposition hS hminus
  let A := T.picardRepresentative (e H.toPic).1
  let m : ℤ := (e H.toPic).2.toAdd
  have hclass : cartierPicardClass T.toScheme A = (e H.toPic).1 :=
    T.cartierPicardClass_picardRepresentative (e H.toPic).1
  have hHclass : H.toPic = e.symm
      (cartierPicardClass T.toScheme A, Multiplicative.ofAdd m) := by
    rw [hclass]
    exact (e.symm_apply_apply H.toPic).symm
  have hE : 0 ≤ S.picardPairing hS H.toPic
      (cartierPicardClass S.toScheme (S.primeCurveCartier hS E)) := by
    change 0 ≤ pairing S hS (Additive.ofMul H.toPic)
      (cartierPicardHom S.toScheme (S.primeCurveCartier hS E))
    rw [pairing_primeCurve_right]
    change 0 ≤ E.picardRestrictionDegree H.toPic
    rw [E.picardRestrictionDegree_toPic]
    exact (Positivity.isNef_iff_forall_primeCurve S H).mp hH E
  have hm : m ≤ 0 := by
    rw [hHclass, hb.picardDecomposition_pairing_exceptional hS hminus] at hE
    omega
  refine ⟨A, m, hm, ?_, hHclass⟩
  apply (T.isNef_iff_pairing hb.regular A).mpr
  intro C
  let D := T.primeCurveCartier hb.regular C
  have heffective := DominantCartierPullback.pullbackHom_effective_of_regularEquations
    b D (T.primeCurveCartier_hasRegularEquations hb.regular C)
  have hnonneg := S.picardPairing_nonneg_of_nef_of_effective hS H hH
    (DominantCartierPullback.pullbackHom b D) heffective
  rw [← DominantCartierPullback.cartierPicardClass_pullback b D,
    hHclass, hb.picardDecomposition_pairing_pullback hS hminus] at hnonneg
  rw [← T.picardPairing_class hb.regular A (T.primeCurveCartier hb.regular C)]
  exact hnonneg

end KltDP.Geometry.IsContraction

#check @KltDP.Geometry.IsContraction.exists_nef_picardDecomposition
#print axioms KltDP.Geometry.IsContraction.exists_nef_picardDecomposition

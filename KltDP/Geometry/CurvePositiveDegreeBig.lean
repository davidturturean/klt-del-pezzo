import KltDP.Geometry.CurveDegreeZeroNotBig

/-!
# Positive degree gives actual bigness on a proper curve

The existing tensor-degree law computes the original Euler value of each
tensor power as n deg(L)+χ(O). The proper dimension-one Euler formula
then bounds the original h⁰ below by this value. Positive integral degree
is at least one, so h⁰(Lⁿ)≥n/2 for arbitrarily large n.

All cohomology groups and scalar actions are the existing ones induced by
the original proper morphism. Proper invertible-cohomology finiteness is
already proved by the imported producer; no section bound, RR formula,
Euler-characteristic value or finiteness premise is supplied here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.CurvePositiveDegreeBig

variable {k : Type u} [Field k] {Y : Scheme.{u}}
  (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]
  (hdim : topologicalKrullDim Y ≤ 1)

include hdim in
/-- The original Picard Euler difference is linear on actual powers. -/
theorem picardEulerDifference_pow (p : Y.Pic) (n : ℕ) :
    picardEulerValue f (p ^ n) - picardEulerValue f 1 =
      (n : ℤ) * (picardEulerValue f p - picardEulerValue f 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,
      KltDP.AdmissionProbe.CurveTensorDegreeConsumers.proper_picardEulerDifference_mul
        f hdim, ih, Nat.cast_succ]
    ring

include hdim in
/-- The Euler value of the original tensor-power representative. -/
theorem eulerCharacteristic_power (L : InvertibleSheaf Y) (n : ℕ) :
    eulerCharacteristic f (InvertibleSheafSectionPowers.power L n).obj =
      (n : ℤ) * (eulerCharacteristic f L.obj -
        eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)) +
          eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf) := by
  have h := picardEulerDifference_pow f hdim L.toPic n
  rw [← InvertibleSheafSectionPowers.power_toPic L n,
    picardEulerValue_toPic, picardEulerValue_toPic, picardEulerValue_one] at h
  linarith

include hdim in
/-- The original section dimension dominates n deg(L)+χ(O), with the
nonnegative actual H¹ dimension supplying the inequality. -/
theorem section_growth_lowerBound (L : InvertibleSheaf Y) (n : ℕ) :
    (n : ℤ) * (eulerCharacteristic f L.obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)) +
        eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf) ≤
          (Positivity.picardHZero f (L.toPic ^ n) : ℤ) := by
  have h : eulerCharacteristic f (InvertibleSheafSectionPowers.power L n).obj ≤
      (cohomologyDimension f (InvertibleSheafSectionPowers.power L n).obj 0 : ℤ) := by
    rw [proper_eulerCharacteristic_eq_h0_sub_h1 f hdim]
    exact sub_le_self _ (Nat.cast_nonneg _)
  rw [eulerCharacteristic_power f hdim,
    ← Positivity.picardHZero_toPic f (InvertibleSheafSectionPowers.power L n),
    InvertibleSheafSectionPowers.power_toPic] at h
  exact h

/-- Positive original Euler degree gives bigness in the unchanged
section-growth definition. The base field need not be algebraically closed. -/
theorem isBig_of_degree_pos (hdimOne : topologicalKrullDim Y = 1)
    (L : InvertibleSheaf Y)
    (hdeg : 0 < eulerCharacteristic f L.obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)) :
    Positivity.IsBig f L := by
  let d : ℤ := eulerCharacteristic f L.obj -
    eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)
  let z : ℤ := eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)
  have hd : (1 : ℤ) ≤ d := by omega
  obtain ⟨M, hM⟩ := exists_nat_ge (2 * |z|)
  have hdimNat : Positivity.natDim Y = 1 := by
    unfold Positivity.natDim
    rw [hdimOne]
    rfl
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro N
  let n := max N M
  have hn : 2 * |z| ≤ (n : ℤ) :=
    hM.trans (by exact_mod_cast (Nat.le_max_right N M))
  have hnd : (n : ℤ) ≤ (n : ℤ) * d := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg n : (0 : ℤ) ≤ n)
  have hgrowth := section_growth_lowerBound f (le_of_eq hdimOne) L n
  change (n : ℤ) * d + z ≤ (Positivity.picardHZero f (L.toPic ^ n) : ℤ) at hgrowth
  have hlinear : (n : ℤ) ≤ 2 * (Positivity.picardHZero f (L.toPic ^ n) : ℤ) := by
    have hz := neg_abs_le z
    omega
  have hlinearQ : (n : ℚ) ≤ 2 * (Positivity.picardHZero f (L.toPic ^ n) : ℚ) := by
    exact_mod_cast hlinear
  refine ⟨n, Nat.le_max_left N M, ?_⟩
  rw [hdimNat, pow_one]
  linarith

section Integral

variable [IsIntegral Y] [IsAlgClosed k]

/-- On an actual integral proper curve, a line bundle of nonnegative
degree is big exactly when its original Euler degree is strictly positive. -/
theorem isBig_iff_degree_pos_of_nonneg (hdimOne : topologicalKrullDim Y = 1)
    (L : InvertibleSheaf Y)
    (hdeg : 0 ≤ eulerCharacteristic f L.obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)) :
    Positivity.IsBig f L ↔ 0 < eulerCharacteristic f L.obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf) := by
  constructor
  · intro hbig
    by_cases hpos : 0 < eulerCharacteristic f L.obj -
        eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)
    · exact hpos
    · have hzero : eulerCharacteristic f L.obj -
          eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf) = 0 := by omega
      exact False.elim (CurveDegreeZeroNotBig.not_isBig f hdimOne L hzero hbig)
  · exact isBig_of_degree_pos f hdimOne L

/-- The complementary degree-zero characterization on the same actual curve. -/
theorem not_isBig_iff_degree_zero_of_nonneg (hdimOne : topologicalKrullDim Y = 1)
    (L : InvertibleSheaf Y)
    (hdeg : 0 ≤ eulerCharacteristic f L.obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)) :
    ¬ Positivity.IsBig f L ↔ eulerCharacteristic f L.obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf) = 0 := by
  rw [isBig_iff_degree_pos_of_nonneg f hdimOne L hdeg]
  omega

end Integral

end KltDP.Geometry.CurvePositiveDegreeBig

import KltDP.LinearAlgebra.ChainMatrix
import KltDP.LinearAlgebra.Stieltjes
import Mathlib.Tactic

/-!
# A path with two higher-weight endpoints

The endpoint weights are `β` and three, with weight-two interior vertices.
For a path of `d ≥ 1` edges, the source endpoint equations are solved over a
field and give the manuscript's denominator `D_d` and two coefficients.

The file defines the actual tridiagonal matrix and proves its row action via
the chain second-difference theorem. Positive-definite path matrices can be
inverted using the existing Stieltjes API; no geometric path or restriction
of a surface discrepancy vector is assumed here.
-/

namespace KltDP.LinearAlgebra

open Matrix

variable {𝕜 : Type*} [Field 𝕜]

/-- Denominator in the two-end path calculation. -/
def twoEndDenominator (β d : 𝕜) : 𝕜 := 2 * β * d + β - 2 * d + 1

/-- Coefficient at the endpoint of weight `β`. -/
def twoEndFirst (β d : 𝕜) : 𝕜 :=
  ((β - 2) * (2 * d + 1) + 1) / twoEndDenominator β d

/-- Coefficient at the endpoint of weight three. -/
def twoEndLast (β d : 𝕜) : 𝕜 :=
  (β - 1) * (d + 1) / twoEndDenominator β d

/-- Factorization displaying the positive terms in the denominator. -/
theorem twoEndDenominator_eq (β d : 𝕜) :
    twoEndDenominator β d = 2 * d * (β - 1) + β + 1 := by
  unfold twoEndDenominator
  ring

/-- The two explicit coefficients satisfy both scaled endpoint equations. -/
theorem twoEnd_coefficients_satisfy (β d : 𝕜) (hD : twoEndDenominator β d ≠ 0) :
    ((β - 1) * d + 1) * twoEndFirst β d - twoEndLast β d = (β - 2) * d ∧
      -twoEndFirst β d + (2 * d + 1) * twoEndLast β d = d := by
  constructor <;> unfold twoEndFirst twoEndLast <;>
    field_simp [hD] <;> unfold twoEndDenominator <;> ring

/-- Solving the actual endpoint system uniquely, rather than assuming the
closed coefficient formulas. Both necessary nonzero factors are explicit. -/
theorem twoEnd_endpoint_system_unique (β d u w : 𝕜) (hd : d ≠ 0)
    (hD : twoEndDenominator β d ≠ 0)
    (hfirst : ((β - 1) * d + 1) * u - w = (β - 2) * d)
    (hlast : -u + (2 * d + 1) * w = d) :
    u = twoEndFirst β d ∧ w = twoEndLast β d := by
  have hu : d * (twoEndDenominator β d * u) = d * ((β - 2) * (2 * d + 1) + 1) := by
    unfold twoEndDenominator
    linear_combination (2 * d + 1) * hfirst + hlast
  have hw : d * (twoEndDenominator β d * w) = d * ((β - 1) * (d + 1)) := by
    unfold twoEndDenominator
    linear_combination hfirst + ((β - 1) * d + 1) * hlast
  have hu' := mul_left_cancel₀ hd hu
  have hw' := mul_left_cancel₀ hd hw
  constructor
  · apply (eq_div_iff hD).mpr
    simpa only [mul_comm] using hu'
  · apply (eq_div_iff hD).mpr
    simpa only [mul_comm] using hw'

/-- A pair of weight-three endpoints gives exactly the constant coefficient
one half, independently of the path length. -/
theorem twoEnd_three [CharZero 𝕜] (d : 𝕜) (hD : twoEndDenominator 3 d ≠ 0) :
    twoEndFirst 3 d = 1 / 2 ∧ twoEndLast 3 d = 1 / 2 := by
  constructor <;> simp only [twoEndFirst, twoEndLast] <;>
    field_simp [hD] <;> unfold twoEndDenominator <;> ring

/-- Exact identity used in the source's lower bound for `v-ℓ`. -/
theorem twoEnd_charge_identity [CharZero 𝕜] (β d : 𝕜)
    (hD : twoEndDenominator β d ≠ 0) :
    1 - β + 2 / 3 + (β - 1) * twoEndFirst β d + twoEndLast β d =
      (β * d - β - d + 5) / (3 * twoEndDenominator β d) := by
  unfold twoEndFirst twoEndLast
  field_simp [hD]
  unfold twoEndDenominator
  ring

section Ordered

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The denominator is positive at the manuscript's weight and edge bounds. -/
theorem twoEndDenominator_pos {β d : 𝕜} (hβ : 3 ≤ β) (hd : 1 ≤ d) :
    0 < twoEndDenominator β d := by
  rw [twoEndDenominator_eq]
  have hprod : 0 ≤ 2 * d * (β - 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  linarith

/-- The excess numerator is `(β-1)(d-1)+4`, hence strictly positive. -/
theorem twoEnd_charge_pos {β d : 𝕜} (hβ : 3 ≤ β) (hd : 1 ≤ d) :
    0 < (β * d - β - d + 5) / (3 * twoEndDenominator β d) := by
  apply div_pos
  · have hprod : 0 ≤ (β - 1) * (d - 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  · exact mul_pos (by norm_num) (twoEndDenominator_pos hβ hd)

/-- Lower bounds by the path coefficients contradict the charge budget used
in the forest reduction. All scalar comparison hypotheses are stated. -/
theorem twoEnd_excludes_nonpositive_charge {β d a u w extra : 𝕜}
    (hβ : 3 ≤ β) (hd : 1 ≤ d) (ha : 1 / 3 ≤ a)
    (hu : twoEndFirst β d ≤ u) (hw : twoEndLast β d ≤ w) (hextra : 0 ≤ extra) :
    0 < 1 - β + 2 * a + (β - 1) * u + w + extra := by
  have hD := ne_of_gt (twoEndDenominator_pos hβ hd)
  have hbase : 0 < 1 - β + 2 / 3 + (β - 1) * twoEndFirst β d + twoEndLast β d := by
    rw [twoEnd_charge_identity β d hD]
    exact twoEnd_charge_pos hβ hd
  have hmul := mul_le_mul_of_nonneg_left hu (by linarith : 0 ≤ β - 1)
  linarith

end Ordered

/-- The actual canonical source at the two endpoints of a `d`-edge path. -/
def twoEndSource (d : ℕ) (β : 𝕜) : Fin (d + 1) → 𝕜 :=
  Pi.single (0 : Fin (d + 1)) (β - 2) + Pi.single (Fin.last d) (1 : 𝕜)

/-- Actual tridiagonal path matrix: start with the weight-two chain and add
the endpoint diagonal corrections `β-2` and one. The endpoint statements
below require `d ≥ 1`, so these are distinct vertices. -/
def weightedTwoEndPath (d : ℕ) (β : 𝕜) : Matrix (Fin (d + 1)) (Fin (d + 1)) 𝕜 :=
  weightTwoChain (d + 1) + Matrix.diagonal (twoEndSource d β)

/-- Direct agreement of the defined source with the actual matrix diagonal. -/
theorem weightedTwoEndPath_diagonal_source (d : ℕ) (β : 𝕜) :
    (fun i => weightedTwoEndPath d β i i - 2) = twoEndSource d β := by
  funext i
  simp [weightedTwoEndPath, weightTwoChain_apply]

/-- The row equation for the actual weighted path, expressed as a discrete
second difference with the two actual diagonal corrections. -/
theorem weightedTwoEndPath_mulVec_of_boundary (d : ℕ) (β : 𝕜) (f : ℕ → 𝕜)
    (hzero : f 0 = 0) (hlast : f (d + 2) = 0) (i : Fin (d + 1)) :
    (weightedTwoEndPath d β *ᵥ (fun j => f (j.val + 1))) i =
      2 * f (i.val + 1) - f i.val - f (i.val + 2) +
        twoEndSource d β i * f (i.val + 1) := by
  rw [weightedTwoEndPath, Matrix.add_mulVec]
  change (weightTwoChain (d + 1) *ᵥ (fun j => f (j.val + 1))) i + _ = _
  rw [Matrix.mulVec_diagonal]
  rw [weightTwoChain_mulVec_of_boundary (d + 1) f hzero (by simpa [Nat.add_assoc] using hlast)]

/-- A solution candidate constructed from the actual chain Green matrix and
the two endpoint residual sources. Its coordinates are not assumed. -/
def twoEndGreenSolution (d : ℕ) (β : 𝕜) : Fin (d + 1) → 𝕜 :=
  chainGreen (d + 1) *ᵥ
    (Pi.single (0 : Fin (d + 1)) ((β - 2) * (1 - twoEndFirst β (d : 𝕜))) +
      Pi.single (Fin.last d) (1 - twoEndLast β (d : 𝕜)))

/-- The candidate's two chain columns, as a coordinate identity. -/
theorem twoEndGreenSolution_apply (d : ℕ) (β : 𝕜) (i : Fin (d + 1)) :
    twoEndGreenSolution d β i =
      chainGreen (d + 1) i 0 * ((β - 2) * (1 - twoEndFirst β (d : 𝕜))) +
      chainGreen (d + 1) i (Fin.last d) * (1 - twoEndLast β (d : 𝕜)) := by
  simp only [twoEndGreenSolution, Matrix.mulVec_add, Pi.add_apply, Matrix.mulVec,
    dotProduct_add, dotProduct_single]

private theorem twoEnd_green_system (β d : 𝕜) (hD : twoEndDenominator β d ≠ 0) :
    (d + 1) * ((β - 2) * (1 - twoEndFirst β d)) + (1 - twoEndLast β d) =
        (d + 2) * twoEndFirst β d ∧
      ((β - 2) * (1 - twoEndFirst β d)) + (d + 1) * (1 - twoEndLast β d) =
        (d + 2) * twoEndLast β d := by
  constructor <;> simp only [twoEndFirst, twoEndLast] <;>
    field_simp [hD] <;> unfold twoEndDenominator <;> ring

/-- Computing the actual candidate at both endpoints gives the scalar
coefficients derived above. This also holds for `d=0`, when the endpoints
coincide and their two source terms add. -/
theorem twoEndGreenSolution_endpoints [CharZero 𝕜] (d : ℕ) (β : 𝕜)
    (hD : twoEndDenominator β (d : 𝕜) ≠ 0) :
    twoEndGreenSolution d β 0 = twoEndFirst β (d : 𝕜) ∧
      twoEndGreenSolution d β (Fin.last d) = twoEndLast β (d : 𝕜) := by
  have hden : ((d + 2 : ℕ) : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hden' : (d : 𝕜) + 2 ≠ 0 := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hden
  obtain ⟨hfirst, hlast⟩ := twoEnd_green_system β (d : 𝕜) hD
  have h00 : chainGreen (𝕜 := 𝕜) (d + 1) 0 0 =
      ((d + 1 : ℕ) : 𝕜) / ((d + 2 : ℕ) : 𝕜) := by
    rw [chainGreen_apply]
    simp [Nat.add_assoc]
  have h0l : chainGreen (𝕜 := 𝕜) (d + 1) 0 (Fin.last d) =
      1 / ((d + 2 : ℕ) : 𝕜) := by
    rw [chainGreen_apply]
    simp [Nat.add_assoc]
  have hl0 : chainGreen (𝕜 := 𝕜) (d + 1) (Fin.last d) 0 =
      1 / ((d + 2 : ℕ) : 𝕜) := by
    rw [chainGreen_apply]
    simp [Nat.add_assoc]
  have hll : chainGreen (𝕜 := 𝕜) (d + 1) (Fin.last d) (Fin.last d) =
      ((d + 1 : ℕ) : 𝕜) / ((d + 2 : ℕ) : 𝕜) := by
    rw [chainGreen_apply]
    simp [Nat.add_assoc]
  constructor
  · rw [twoEndGreenSolution_apply, h00, h0l]
    push_cast
    calc
      _ = (((d : 𝕜) + 1) * ((β - 2) * (1 - twoEndFirst β (d : 𝕜))) +
          (1 - twoEndLast β (d : 𝕜))) / ((d : 𝕜) + 2) := by ring
      _ = _ := (div_eq_iff hden').mpr (hfirst.trans (mul_comm _ _))
  · rw [twoEndGreenSolution_apply, hl0, hll]
    push_cast
    calc
      _ = (((β - 2) * (1 - twoEndFirst β (d : 𝕜))) +
          ((d : 𝕜) + 1) * (1 - twoEndLast β (d : 𝕜))) / ((d : 𝕜) + 2) := by ring
      _ = _ := (div_eq_iff hden').mpr (hlast.trans (mul_comm _ _))

/-- Multiplication by the actual weighted matrix gives its actual
diagonal-minus-two source. The only inverse used to construct this certificate
is the already proved Green matrix of the weight-two chain. -/
theorem weightedTwoEndPath_mul_solution [CharZero 𝕜] (d : ℕ) (β : 𝕜)
    (hD : twoEndDenominator β (d : 𝕜) ≠ 0) :
    weightedTwoEndPath d β *ᵥ twoEndGreenSolution d β = twoEndSource d β := by
  obtain ⟨hfirst, hlast⟩ := twoEndGreenSolution_endpoints d β hD
  have hchain : weightTwoChain (d + 1) *ᵥ twoEndGreenSolution d β =
      Pi.single (0 : Fin (d + 1)) ((β - 2) * (1 - twoEndFirst β (d : 𝕜))) +
        Pi.single (Fin.last d) (1 - twoEndLast β (d : 𝕜)) := by
    rw [twoEndGreenSolution, Matrix.mulVec_mulVec, weightTwoChain_mul_chainGreen,
      Matrix.one_mulVec]
  rw [weightedTwoEndPath, Matrix.add_mulVec, hchain]
  ext i
  simp only [Pi.add_apply, Matrix.mulVec_diagonal]
  by_cases hi0 : i = 0
  · subst i
    by_cases h0l : (0 : Fin (d + 1)) = Fin.last d
    · have hfirst' : twoEndGreenSolution d β (Fin.last d) =
          twoEndFirst β (d : 𝕜) := by
        simpa only [h0l] using hfirst
      have hsingle (a : 𝕜) :
          (Pi.single (Fin.last d) a : Fin (d + 1) → 𝕜) 0 = a := by
        have h := congrArg (Pi.single (Fin.last d) a : Fin (d + 1) → 𝕜) h0l
        exact h.trans (Pi.single_eq_same (f := fun _ : Fin (d + 1) => 𝕜) (Fin.last d) a)
      simp only [twoEndSource, Pi.add_apply, h0l, Pi.single_eq_same]
      rw [← hlast, ← hfirst']
      simp only [hsingle]
      ring
    · simp only [twoEndSource, Pi.add_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne h0l, add_zero, hfirst]
      ring
  · by_cases hil : i = Fin.last d
    · subst i
      simp only [twoEndSource, Pi.add_apply, Pi.single_eq_of_ne hi0,
        Pi.single_eq_same, zero_add, hlast]
      ring
    · simp only [twoEndSource, Pi.add_apply, Pi.single_eq_of_ne hi0,
        Pi.single_eq_of_ne hil, zero_add, zero_mul]

/-- The actual inverse solution has the claimed two endpoint coefficients
whenever the actual weighted matrix is invertible. -/
theorem weightedTwoEndPath_inverse_endpoints [CharZero 𝕜] (d : ℕ) (β : 𝕜)
    (hD : twoEndDenominator β (d : 𝕜) ≠ 0)
    (hA : IsUnit (weightedTwoEndPath d β)) :
    ((weightedTwoEndPath d β)⁻¹ *ᵥ twoEndSource d β) 0 = twoEndFirst β (d : 𝕜) ∧
      ((weightedTwoEndPath d β)⁻¹ *ᵥ twoEndSource d β) (Fin.last d) =
        twoEndLast β (d : 𝕜) := by
  letI : Invertible (weightedTwoEndPath d β) := hA.invertible
  have hsol : (weightedTwoEndPath d β)⁻¹ *ᵥ twoEndSource d β =
      twoEndGreenSolution d β :=
    Matrix.inv_mulVec_eq_vec (weightedTwoEndPath_mul_solution d β hD).symm
  rw [hsol]
  exact twoEndGreenSolution_endpoints d β hD

section OrderedMatrix

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The actual weighted path has nonpositive entries off the diagonal,
irrespective of its endpoint weight. -/
theorem weightedTwoEndPath_offDiagonal (d : ℕ) (β : 𝕜)
    (i j : Fin (d + 1)) (hij : i ≠ j) : weightedTwoEndPath d β i j ≤ 0 := by
  simp only [weightedTwoEndPath, Matrix.add_apply, Matrix.diagonal_apply_ne _ hij,
    weightTwoChain_apply, if_neg hij, add_zero]
  split_ifs <;> norm_num

variable [StarRing 𝕜] [TrivialStar 𝕜]

/-- The path comparison actually used by the source: if the path matrix is
positive definite and a vector's row images dominate the canonical source,
both endpoint coordinates dominate the computed path coefficients. A later
geometric adapter must establish these two hypotheses for the restricted
resolution matrix and its restricted discrepancy vector. -/
theorem weightedTwoEndPath_endpoint_lower_bounds (d : ℕ) (β : 𝕜)
    (hD : twoEndDenominator β (d : 𝕜) ≠ 0)
    (hA : (weightedTwoEndPath d β).PosDef) (coeff : Fin (d + 1) → 𝕜)
    (hrows : ∀ i, twoEndSource d β i ≤ (weightedTwoEndPath d β *ᵥ coeff) i) :
    twoEndFirst β (d : 𝕜) ≤ coeff 0 ∧
      twoEndLast β (d : 𝕜) ≤ coeff (Fin.last d) := by
  have hdiff : ∀ i, 0 ≤ (weightedTwoEndPath d β *ᵥ
      (coeff - twoEndGreenSolution d β)) i := by
    rw [Matrix.mulVec_sub, weightedTwoEndPath_mul_solution d β hD]
    intro i
    exact sub_nonneg.mpr (hrows i)
  have hnonneg := nonneg_of_mulVec_nonneg hA (weightedTwoEndPath_offDiagonal d β) hdiff
  obtain ⟨hfirst, hlast⟩ := twoEndGreenSolution_endpoints d β hD
  constructor
  · rw [← hfirst]
    exact sub_nonneg.mp (hnonneg 0)
  · rw [← hlast]
    exact sub_nonneg.mp (hnonneg (Fin.last d))

end OrderedMatrix

end KltDP.LinearAlgebra

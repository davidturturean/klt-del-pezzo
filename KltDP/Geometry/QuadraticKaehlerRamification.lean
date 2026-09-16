import KltDP.Geometry.QuadraticRootQuotient
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Algebra.GroupWithZero.Action.Units

/-!
# The intrinsic annihilator of quadratic Kähler differentials

For the actual algebra `A = R[t]/(t²-s)`, the annihilator of `Ω[A/R]`
is the principal root ideal when two is invertible. Differentiating the
original equation shows that the root annihilates the differentials.
Conversely, the actual coefficient derivation to `A/(t)`, sending the
root to one, and its universal Kähler lift detect every annihilator.

Reuse: pinned `Derivation.mk'`, `Derivation.liftKaehlerDifferential`,
`Derivation.liftKaehlerDifferential_comp_D`, and
`KaehlerDifferential.span_range_derivation` supply the existing universal
module and its generation. These APIs were compared with official Mathlib
revision `80cbd0498ab39e21d24d6730b3f932cec672a702`,
`Mathlib/RingTheory/Kaehler/Basic.lean` and `Kaehler/Polynomial.lean`
(Apache 2.0, Lean 4.34.0-rc2). No new universal construction or newer API
is ported; the actual quadratic coefficient calculation is the adapter.

The public annihilator equality includes the trivial base ring. It uses
no regularity or nonvanishing assumption on the branch coefficient and
does not assert a Fitting-ideal identity or any global ideal-sheaf gluing.
-/

noncomputable section

namespace KltDP.Geometry.QuadraticCover

variable {R : Type*} [CommRing R]

/-- Killing the actual root leaves the original constant coefficient. -/
theorem rootQuotient_mk_ofCoeffs (s a b : R) :
    Ideal.Quotient.mk (rootIdeal s) (ofCoeffs s a b) =
      algebraMap R (CoverAlgebra s ⧸ rootIdeal s) a := by
  simp only [ofCoeffs, map_add, map_mul, rootQuotient_mk_root,
    mul_zero, add_zero, Ideal.Quotient.mk_algebraMap]

/-- The universal derivation is determined by the actual root coordinate. -/
theorem kaehler_D_ofCoeffs (s a b : R) :
    KaehlerDifferential.D R (CoverAlgebra s) (ofCoeffs s a b) =
      algebraMap R (CoverAlgebra s) b •
        KaehlerDifferential.D R (CoverAlgebra s) (root s) := by
  simp only [ofCoeffs, map_add, Derivation.leibniz, Derivation.map_algebraMap,
    smul_zero, add_zero, zero_add]

/-- Differentiating the actual quadratic relation makes its root annihilate `dt`
as soon as two is a unit. -/
theorem root_smul_kaehler_D_root (s : R) (h2 : IsUnit (2 : R)) :
    root s • KaehlerDifferential.D R (CoverAlgebra s) (root s) = 0 := by
  have hd := congrArg (KaehlerDifferential.D R (CoverAlgebra s)) (root_sq s)
  rw [pow_two, Derivation.leibniz, Derivation.map_algebraMap] at hd
  have ht : (2 : CoverAlgebra s) •
      (root s • KaehlerDifferential.D R (CoverAlgebra s) (root s)) = 0 := by
    rw [two_smul]
    exact hd
  have hu : IsUnit (2 : CoverAlgebra s) := by
    simpa only [map_ofNat] using h2.map (algebraMap R (CoverAlgebra s))
  exact hu.smul_eq_zero.mp ht

section Coordinates

variable [Nontrivial R]

/-- The actual coefficient derivation to the root quotient, sending the root to one. -/
def rootQuotientDerivation (s : R) :
    Derivation R (CoverAlgebra s) (CoverAlgebra s ⧸ rootIdeal s) :=
  Derivation.mk'
    ((Algebra.ofId R (CoverAlgebra s ⧸ rootIdeal s)).toLinearMap.comp (rootCoeff s)) (by
      intro x y
      obtain ⟨a, b, rfl⟩ : ∃ a b, ofCoeffs s a b = x :=
        ⟨constantCoeff s x, rootCoeff s x, ofCoeffs_coefficients s x⟩
      obtain ⟨c, d, rfl⟩ : ∃ c d, ofCoeffs s c d = y :=
        ⟨constantCoeff s y, rootCoeff s y, ofCoeffs_coefficients s y⟩
      change algebraMap R (CoverAlgebra s ⧸ rootIdeal s)
        (rootCoeff s (ofCoeffs s a b * ofCoeffs s c d)) =
          ofCoeffs s a b • algebraMap R (CoverAlgebra s ⧸ rootIdeal s)
              (rootCoeff s (ofCoeffs s c d)) +
            ofCoeffs s c d • algebraMap R (CoverAlgebra s ⧸ rootIdeal s)
              (rootCoeff s (ofCoeffs s a b))
      rw [ofCoeffs_mul, rootCoeff_ofCoeffs, rootCoeff_ofCoeffs, rootCoeff_ofCoeffs]
      simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
        rootQuotient_mk_ofCoeffs, map_add, map_mul, mul_comm])

@[simp]
theorem rootQuotientDerivation_apply (s : R) (x : CoverAlgebra s) :
    rootQuotientDerivation s x =
      algebraMap R (CoverAlgebra s ⧸ rootIdeal s) (rootCoeff s x) := rfl

@[simp]
theorem rootQuotientDerivation_root (s : R) :
    rootQuotientDerivation s (root s) = 1 := by
  rw [rootQuotientDerivation_apply, rootCoeff_root, map_one]

/-- Applying the existing universal lift to `dt` gives one in the actual root quotient. -/
@[simp]
theorem rootQuotientDerivation_lift_D_root (s : R) :
    (rootQuotientDerivation s).liftKaehlerDifferential
      (KaehlerDifferential.D R (CoverAlgebra s) (root s)) = 1 := by
  rw [Derivation.liftKaehlerDifferential_comp_D, rootQuotientDerivation_root]

/-- Every actual differential is a scalar multiple of the differential of the root. -/
theorem kaehler_D_eq_rootCoeff_smul (s : R) (x : CoverAlgebra s) :
    KaehlerDifferential.D R (CoverAlgebra s) x =
      algebraMap R (CoverAlgebra s) (rootCoeff s x) •
        KaehlerDifferential.D R (CoverAlgebra s) (root s) := by
  calc
    KaehlerDifferential.D R (CoverAlgebra s) x =
        KaehlerDifferential.D R (CoverAlgebra s)
          (ofCoeffs s (constantCoeff s x) (rootCoeff s x)) :=
      congrArg (KaehlerDifferential.D R (CoverAlgebra s)) (ofCoeffs_coefficients s x).symm
    _ = _ := kaehler_D_ofCoeffs s _ _

/-- The actual root-quotient derivation detects every intrinsic annihilator element. -/
theorem kaehler_annihilator_le_rootIdeal (s : R) :
    Module.annihilator (CoverAlgebra s) (KaehlerDifferential R (CoverAlgebra s)) ≤
      rootIdeal s := by
  intro a ha
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hz := Module.mem_annihilator.mp ha
    (KaehlerDifferential.D R (CoverAlgebra s) (root s))
  have hq := congrArg (rootQuotientDerivation s).liftKaehlerDifferential hz
  rw [map_smul, rootQuotientDerivation_lift_D_root, map_zero,
    Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq] at hq
  exact hq

/-- The root annihilates the entire intrinsic differential module, generated by the universal D. -/
theorem rootIdeal_le_kaehler_annihilator (s : R) (h2 : IsUnit (2 : R)) :
    rootIdeal s ≤
      Module.annihilator (CoverAlgebra s) (KaehlerDifferential R (CoverAlgebra s)) := by
  rw [rootIdeal, Ideal.span_singleton_le_iff_mem, Module.mem_annihilator]
  intro ω
  have hω : ω ∈ Submodule.span (CoverAlgebra s)
      (Set.range (KaehlerDifferential.D R (CoverAlgebra s))) := by
    rw [KaehlerDifferential.span_range_derivation]
    exact Submodule.mem_top
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hω
  · rintro _ ⟨x, rfl⟩
    rw [kaehler_D_eq_rootCoeff_smul, smul_comm, root_smul_kaehler_D_root s h2, smul_zero]
  · exact smul_zero _
  · intro x y _ _ hx hy
    rw [smul_add, hx, hy, add_zero]
  · intro a x _ hx
    rw [smul_comm, hx, smul_zero]

end Coordinates

/-- The intrinsic Kähler annihilator is exactly the actual root ideal whenever two is a unit.
The statement includes trivial coefficient rings. -/
theorem kaehler_annihilator_eq_rootIdeal (s : R) (h2 : IsUnit (2 : R)) :
    Module.annihilator (CoverAlgebra s) (KaehlerDifferential R (CoverAlgebra s)) =
      rootIdeal s := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · letI := hR
    letI : Subsingleton (CoverAlgebra s) := Module.subsingleton R (CoverAlgebra s)
    exact Subsingleton.elim _ _
  · letI := hR
    exact le_antisymm (kaehler_annihilator_le_rootIdeal s)
      (rootIdeal_le_kaehler_annihilator s h2)

end KltDP.Geometry.QuadraticCover

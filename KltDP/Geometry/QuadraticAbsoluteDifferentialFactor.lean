import KltDP.Geometry.QuadraticCoverAlgebra
import KltDP.LinearAlgebra.SplitConormalDeterminant
import Mathlib.RingTheory.Kaehler.Basic

/-!
# The original absolute differential of a quadratic cover

For the actual algebra B = R[t]/(t²-s), differentiating the original
equation over k gives d(s) = 2t dt. The actual exterior-square map
therefore sends d(s) wedge eta to 2t times dt wedge the image of eta.
This is the local ramification multiplier in the canonical formula.

No smoothness, basis, determinant factorization, or global canonical
formula is assumed. The normalized frames and their global comparison
are subsequent obligations; this file proves the original differential
identity, including in characteristic two and for nonreduced rings.
-/

noncomputable section

open scoped TensorProduct
open KltDP.LinearAlgebra.SplitConormalDeterminant

universe u

namespace KltDP.Geometry.QuadraticCover

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]

/-- The original absolute derivation differentiates the actual quadratic
relation, retaining its coefficient map and root. -/
theorem absoluteDifferential_branch (s : R) :
    KaehlerDifferential.D k (CoverAlgebra s) (algebraMap R (CoverAlgebra s) s) =
      (2 * root s) • KaehlerDifferential.D k (CoverAlgebra s) (root s) := by
  have h := congrArg (KaehlerDifferential.D k (CoverAlgebra s)) (root_sq s)
  rw [pow_two, Derivation.leibniz] at h
  simpa only [two_mul, add_smul] using h.symm

/-- The first absolute differential map in the original algebra tower
sends the pulled branch differential to twice the root times dt. -/
theorem mapBaseChange_branch (s : R) :
    KaehlerDifferential.mapBaseChange k R (CoverAlgebra s)
        (1 ⊗ₜ[R] KaehlerDifferential.D k R s) =
      (2 * root s) • KaehlerDifferential.D k (CoverAlgebra s) (root s) := by
  rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  exact absoluteDifferential_branch k R s

/-- The actual exterior differential has the original ramification
multiplier 2t on every branch-normalized pure wedge. -/
theorem exteriorDifferential_branch (s : R)
    (eta : CoverAlgebra s ⊗[R] KaehlerDifferential k R) :
    exteriorPower.map 2 (KaehlerDifferential.mapBaseChange k R (CoverAlgebra s))
        (exteriorPower.ιMulti (CoverAlgebra s) 2
          ![1 ⊗ₜ[R] KaehlerDifferential.D k R s, eta]) =
      (2 * root s) • exteriorPower.ιMulti (CoverAlgebra s) 2
        ![KaehlerDifferential.D k (CoverAlgebra s) (root s),
          KaehlerDifferential.mapBaseChange k R (CoverAlgebra s) eta] := by
  rw [exteriorPower.map_apply_ιMulti]
  have htuple : KaehlerDifferential.mapBaseChange k R (CoverAlgebra s) ∘
      ![1 ⊗ₜ[R] KaehlerDifferential.D k R s, eta] =
      ![KaehlerDifferential.mapBaseChange k R (CoverAlgebra s)
          (1 ⊗ₜ[R] KaehlerDifferential.D k R s),
        KaehlerDifferential.mapBaseChange k R (CoverAlgebra s) eta] := by
    funext i
    fin_cases i <;> rfl
  rw [htuple, mapBaseChange_branch, ← leftWedge_apply,
    leftWedge_smul_apply, leftWedge_apply]

end KltDP.Geometry.QuadraticCover

#check @KltDP.Geometry.QuadraticCover.exteriorDifferential_branch
#print axioms KltDP.Geometry.QuadraticCover.exteriorDifferential_branch

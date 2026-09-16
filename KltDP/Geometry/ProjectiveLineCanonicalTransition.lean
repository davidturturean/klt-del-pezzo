import KltDP.Geometry.ProjectiveLineCanonicalInvertible
import KltDP.Geometry.TransitionUnitRecovery

/-!
# The exponent of `Ω_{P¹}` is the overlap transition unit of the frames `dt`, `ds`

`ProjectiveLineCanonicalInvertible.localTrivializations` trivialises `Ω_{P¹}` on the two standard
opens by the frames `dt` and `ds` (through the pinned `polynomialEquiv`). By the accepted recovery
isomorphism (`TransitionUnitExtraction.recoveryIso`) and `exponent_eq_of_iso_to_glued`, the
transition exponent of the canonical sheaf is the `cocycleExponent` of the transition units of
these frames, i.e. the Laurent exponent of the single overlap unit `frameTransitionUnits k ⟨0⟩ ⟨1⟩`
(`exponent_canonicalSheaf_eq_overlapExponent`). Consequently **`deg K_{P¹}` equals that Laurent
exponent** (`canonicalDegree_eq_overlapExponent`, with `degree_eq_exponent`).

The frame relation needed to evaluate the unit is proved for the sheaf derivation in general:
for sections `t, s` on any open with `t * s = 1`, **`d s = −(s·s) • d t`**
(`baseRingDerivation_inv`, the Leibniz rule of the accepted `SchemeKaehlerSheaf.derivation_mul`).

**Not proved here:** the identification of `frameTransitionUnits k ⟨0⟩ ⟨1⟩`, read in the Laurent
ring of the overlap, with the coefficient of `ds` against `dt`, i.e. `−T⁻²` (hence `exponent = −2`
and `deg K_{P¹} = −2`); see `F04_CANONICAL_PLAN.md` §4.1.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open KltDP.Geometry.ModuleCohomology KltDP.Geometry.SchemeKaehlerSheaf
open KltDP.Geometry.ProjectiveLineSheafExponent KltDP.Geometry.ProjectiveLineTransitionExtension
open KltDP.Geometry.ProjectiveLineTransitionExponent

universe u

namespace KltDP.Geometry.ProjectiveLineCanonical

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section Leibniz

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

/-- `d 1 = 0` for the accepted base-ring differential. -/
theorem baseRingDerivation_one (U : X.Opens) :
    (baseRingDerivation f).d (1 : Γ(X, U)) = 0 :=
  (baseRingDerivation f).d_one (op U)

/-- **The inverse rule** for the accepted base-ring differential: if `t * s = 1` on an open then
`d s = −(s·s) • d t`. -/
theorem baseRingDerivation_inv (U : X.Opens) (t s : Γ(X, U)) (h : t * s = 1) :
    (baseRingDerivation f).d s = -((s * s) • (baseRingDerivation f).d t) := by
  have h0 : (baseRingDerivation f).d (t * s) = 0 := by
    rw [h]
    exact baseRingDerivation_one f U
  rw [derivation_mul] at h0
  have h1 := congrArg (fun m => s • m) h0
  simp only [smul_add, smul_zero, smul_smul] at h1
  rw [mul_comm s t, h, one_smul] at h1
  exact eq_neg_of_add_eq_zero_left h1

end Leibniz

variable (k : Type u) [Field k]

/-- The transition units of the explicit frames `dt`, `ds` of `Ω_{P¹}` on the standard opens. -/
abbrev frameTransitionUnits :
    ∀ i j : ULift.{u} (Fin 2),
      Γ(projectiveSpace k 1, standardOpens k i ⊓ standardOpens k j)ˣ :=
  TransitionUnitExtraction.transitionUnits (projectiveSpace k 1) (cotangent k)
    (localTrivializations k)

/-- **The exponent of `Ω_{P¹}` is the cocycle exponent of the frame transition units.** -/
theorem exponent_canonicalSheaf_eq_cocycleExponent :
    exponent k (canonicalSheaf k) = cocycleExponent k (frameTransitionUnits k) :=
  exponent_eq_of_iso_to_glued k (canonicalSheaf k) (frameTransitionUnits k)
    (TransitionUnitExtraction.transitionUnits_isCocycle (projectiveSpace k 1) (cotangent k)
      (localTrivializations k))
    (TransitionUnitExtraction.recoveryIso (projectiveSpace k 1) (cotangent k)
      (localTrivializations k))

/-- The exponent of `Ω_{P¹}` is the Laurent exponent of the single overlap unit
`frameTransitionUnits k ⟨0⟩ ⟨1⟩`. -/
theorem exponent_canonicalSheaf_eq_overlapExponent :
    exponent k (canonicalSheaf k) =
      overlapExponent k (overlapRestriction k (frameTransitionUnits k ⟨0⟩ ⟨1⟩)) := by
  rw [exponent_canonicalSheaf_eq_cocycleExponent, cocycleExponent]

/-- **`deg K_{P¹}` is the Laurent exponent of the overlap transition unit of the frames.** -/
theorem canonicalDegree_eq_overlapExponent :
    CurveCanonical.canonicalDegree (projectiveSpaceToSpec k 1) =
      overlapExponent k (overlapRestriction k (frameTransitionUnits k ⟨0⟩ ⟨1⟩)) :=
  (canonicalDegree_eq_exponent k).trans (exponent_canonicalSheaf_eq_overlapExponent k)

/-- The remaining computation, as a conditional: if the overlap unit has Laurent exponent `n`,
then `deg K_{P¹} = n`. -/
theorem canonicalDegree_eq_of_overlapExponent (n : ℤ)
    (h : overlapExponent k (overlapRestriction k (frameTransitionUnits k ⟨0⟩ ⟨1⟩)) = n) :
    CurveCanonical.canonicalDegree (projectiveSpaceToSpec k 1) = n :=
  (canonicalDegree_eq_overlapExponent k).trans h

/-- **The target in concrete form**: if the overlap transition unit of the frames, read in the
Laurent ring `k[T, T⁻¹]` of the overlap, is `c · T⁻²` for a scalar `c`, then `deg K_{P¹} = −2`. -/
theorem canonicalDegree_eq_neg_two_of_monomial (c : kˣ)
    (h : ((overlapLaurentUnit k (overlapRestriction k (frameTransitionUnits k ⟨0⟩ ⟨1⟩)) :
        (LaurentPolynomial k)ˣ) : LaurentPolynomial k) =
      LaurentPolynomial.C (c : k) * LaurentPolynomial.T (-2)) :
    CurveCanonical.canonicalDegree (projectiveSpaceToSpec k 1) = -2 :=
  canonicalDegree_eq_of_overlapExponent k (-2)
    (unitExponent_eq_of_monomial k
      (overlapLaurentUnit k (overlapRestriction k (frameTransitionUnits k ⟨0⟩ ⟨1⟩))) c (-2) h)

end KltDP.Geometry.ProjectiveLineCanonical

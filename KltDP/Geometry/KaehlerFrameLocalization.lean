import KltDP.Geometry.TopDifferentialFrameBaseChange

/-!
# Transporting the Jacobian to an overlap: the frame-change unit of the localised charts

F04 §4.3 route (b) needs, on the overlap of two standard-smooth charts, the unit by which the two
top-differential frames differ — the Jacobian of the coordinate change.  `TopDifferentialFrameChange`
compares two frames over one ring; `TopDifferentialFrameBaseChange` shows the comparison is natural in
a scalar change.  The remaining ingredient is that both frames may be carried into one and the same
module over the overlap ring, namely `Ω[B⁄k]`, and that doing so does not disturb the unit.

* **`det_map_eq`, `frameChangeUnit_map`**: transporting *both* frames along one linear equivalence
  leaves the frame-change determinant, hence the unit, unchanged (pinned `Basis.det_map`).
* **`presentationJacobian_transport`**: for an `A`-algebra `B` and an identification
  `e : B ⊗[A] Ω[A⁄k] ≃ₗ[B] Ω[B⁄k]`, the two chart frames of submersive presentations of relative
  dimension two, base-changed to `B` and carried across `e`, differ by the image of the Jacobian:
  `algebraMap A B (presentationJacobian k A P P')`.  This is the overlap unit of route (b).
* **`transport_self`, `transport_mul`**: the two `IsCocycle` fields for the transported frames.

The identification `e` is an argument rather than a construction: for an overlap `B = A_f` the pinned
Mathlib instances supply it — `KaehlerDifferential.map k k A (Localization.Away f)` is an
`IsLocalizedModule` for `Submonoid.powers f` (used exactly so in `Mathlib/RingTheory/Smooth/Locus.lean`
and `Mathlib/RingTheory/Unramified/Locus.lean`), and the accepted
`AffineKaehlerTildeLocalization.presheafComparison_basicOpen_bijective` uses the same fact on basic
opens of an affine chart.

Nothing is admitted here, and nothing in this file touches the over-site machinery on which
`deg K_{P¹} = −2` is blocked.
-/

noncomputable section

open scoped TensorProduct

open KltDP.Geometry.AffineTopDifferentialFrame KltDP.Geometry.TopDifferentialFrameChange
open KltDP.Geometry.TopDifferentialFrameBaseChange

universe u v w

namespace KltDP.Geometry.KaehlerFrameLocalization

section Transport

variable {A : Type u} [CommRing A] {M : Type w} [AddCommGroup M] [Module A M]
variable {N : Type w} [AddCommGroup N] [Module A N] {n : ℕ}

/-- Transporting both frames along one linear equivalence leaves the determinant unchanged. -/
theorem det_map_eq (b b' : Basis (Fin n) A M) (e : M ≃ₗ[A] N) :
    (b.map e).det (b'.map e) = b.det b' := by
  rw [Basis.det_map]
  congr 1
  funext i
  rw [Function.comp_apply, Basis.map_apply, LinearEquiv.symm_apply_apply]

/-- Hence the frame-change unit is unchanged. -/
theorem frameChangeUnit_map (b b' : Basis (Fin n) A M) (e : M ≃ₗ[A] N) :
    frameChangeUnit (b.map e) (b'.map e) = frameChangeUnit b b' := by
  apply Units.ext
  rw [frameChangeUnit_val, frameChangeUnit_val]
  exact det_map_eq b b' e

end Transport

section Charts

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
variable (B : Type u) [CommRing B] [Algebra A B] [Algebra k B]
variable (e : B ⊗[A] (KaehlerDifferential k A) ≃ₗ[B] KaehlerDifferential k B)

/-- The chart frame of a submersive presentation, carried to the overlap module `Ω[B⁄k]`. -/
def transportedFrame (P : Algebra.SubmersivePresentation k A) (hP : P.dimension = 2) :
    Basis (Fin 2) B (KaehlerDifferential k B) :=
  ((presentationDifferentialBasis k A P hP).baseChange B).map e

/-- **The overlap unit is the image of the Jacobian.** -/
theorem presentationJacobian_transport (P P' : Algebra.SubmersivePresentation k A)
    (hP : P.dimension = 2) (hP' : P'.dimension = 2) :
    frameChangeUnit (transportedFrame k A B e P hP) (transportedFrame k A B e P' hP') =
      Units.map (algebraMap A B).toMonoidHom (presentationJacobian k A P P' hP hP') := by
  rw [transportedFrame, transportedFrame, frameChangeUnit_map]
  exact frameChangeUnit_baseChange B _ _

/-- Normalisation — the first `IsCocycle` field, for the transported frames. -/
theorem transport_self (P : Algebra.SubmersivePresentation k A) (hP : P.dimension = 2) :
    frameChangeUnit (transportedFrame k A B e P hP) (transportedFrame k A B e P hP) = 1 :=
  frameChangeUnit_self _

/-- The triple-overlap identity — the second `IsCocycle` field, for the transported frames. -/
theorem transport_mul (P P' P'' : Algebra.SubmersivePresentation k A)
    (hP : P.dimension = 2) (hP' : P'.dimension = 2) (hP'' : P''.dimension = 2) :
    frameChangeUnit (transportedFrame k A B e P hP) (transportedFrame k A B e P' hP') *
        frameChangeUnit (transportedFrame k A B e P' hP') (transportedFrame k A B e P'' hP'') =
      frameChangeUnit (transportedFrame k A B e P hP) (transportedFrame k A B e P'' hP'') :=
  frameChangeUnit_mul _ _ _

end Charts

end KltDP.Geometry.KaehlerFrameLocalization

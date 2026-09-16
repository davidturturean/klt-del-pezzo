import KltDP.Geometry.TopDifferentialFrameChange
import KltDP.Geometry.TopExteriorBaseChange

/-!
# The chart-level Jacobian on an overlap: frame change under scalar extension

F04 §4.3 route (b) glues the chart line bundles of `AffineTopDifferentialFrame` along the Jacobian
transition determinants.  `TopDifferentialFrameChange` compares two frames over a *fixed* ring and
supplies the two `IsCocycle` fields.  The remaining local content — the genuinely new one — is the
comparison on an **overlap**, where the two charts are compared after a scalar change `A → B`.

The scalar change is the accepted `TopExteriorBaseChange.equiv`, whose forward map is the canonical
comparison `B ⊗[A] ⋀[A]^n M →ₗ[B] ⋀[B]^n (B ⊗[A] M)` (so it may be applied to the wedge of *any*
basis; the auxiliary basis it carries is only used for bijectivity).

* **`equiv_one_tmul_basis`**: the comparison takes `1 ⊗ ⋀ b₀` to the wedge of the base-changed basis
  `b₀.baseChange B` (pinned `Basis.baseChange_apply`).
* **`topWedge_baseChange`**: after scalar change the two frames are still proportional, with the
  *image* of the determinant: `⋀ (b'.baseChange B) = algebraMap A B (b.det b') • ⋀ (b.baseChange B)`.
* **`det_baseChange`**, **`frameChangeUnit_baseChange`**: the frame-change unit is natural in the
  scalar change, `frameChangeUnit (b.baseChange B) (b'.baseChange B) = algebraMap A B (frameChangeUnit b b')`.
  This is what makes the chart units restrict correctly to overlaps, which is exactly the
  compatibility `TransitionUnitGluing` needs of a cocycle family.
* **`presentationJacobian_baseChange`**: the same statement for two submersive presentations of
  relative dimension two — the Jacobian determinant of the coordinate change, restricted to the
  overlap.

Nothing is admitted here, and nothing in this file touches the over-site machinery on which
`deg K_{P¹} = −2` is blocked.
-/

noncomputable section

open scoped TensorProduct

open KltDP.Geometry.AffineTopDifferentialFrame KltDP.Geometry.TopDifferentialFrameChange

universe u v w

namespace KltDP.Geometry.TopDifferentialFrameBaseChange

section BaseChange

variable {A : Type u} [CommRing A] {M : Type w} [AddCommGroup M] [Module A M]
variable (B : Type v) [CommRing B] [Algebra A B] {n : ℕ}

/-- The canonical comparison takes `1 ⊗ ⋀ b₀` to the wedge of the base-changed basis. -/
theorem equiv_one_tmul_basis (b b₀ : Basis (Fin n) A M) :
    TopExteriorBaseChange.equiv B b (1 ⊗ₜ[A] exteriorPower.ιMulti A n b₀) =
      exteriorPower.ιMulti B n (b₀.baseChange B) := by
  rw [TopExteriorBaseChange.equiv_one_tmul_ιMulti]
  exact congrArg (fun v : Fin n → B ⊗[A] M => exteriorPower.ιMulti B n v)
    (funext fun i => (Basis.baseChange_apply B b₀ i).symm)

/-- **The two frames stay proportional after a scalar change**, by the image of the determinant. -/
theorem topWedge_baseChange (b b' : Basis (Fin n) A M) :
    exteriorPower.ιMulti B n (b'.baseChange B) =
      algebraMap A B (b.det b') • exteriorPower.ιMulti B n (b.baseChange B) := by
  rw [← equiv_one_tmul_basis B b b', ← equiv_one_tmul_basis B b b,
    topWedge_eq_det_smul b b', TensorProduct.tmul_smul, ← map_smul]
  congr 1
  exact (algebraMap_smul B (b.det b') _).symm

/-- **The frame-change determinant is natural in the scalar change.** -/
theorem det_baseChange (b b' : Basis (Fin n) A M) :
    (b.baseChange B).det (b'.baseChange B) = algebraMap A B (b.det b') := by
  have h := congrArg (determinantEquiv (b.baseChange B)) (topWedge_baseChange B b b')
  simp only [map_smul, determinantEquiv_apply_wedge, Basis.det_self, smul_eq_mul, mul_one] at h
  exact h

/-- **The frame-change unit is natural in the scalar change**: the chart transition units restrict
to overlaps, which is the compatibility a cocycle family needs. -/
theorem frameChangeUnit_baseChange (b b' : Basis (Fin n) A M) :
    frameChangeUnit (b.baseChange B) (b'.baseChange B) =
      Units.map (algebraMap A B).toMonoidHom (frameChangeUnit b b') := by
  apply Units.ext
  rw [frameChangeUnit_val, Units.coe_map]
  exact det_baseChange B b b'

end BaseChange

section Presentations

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
variable (B : Type v) [CommRing B] [Algebra A B]

/-- **The Jacobian of a change of submersive presentation, restricted to an overlap.** -/
theorem presentationJacobian_baseChange (P P' : Algebra.SubmersivePresentation k A)
    (hP : P.dimension = 2) (hP' : P'.dimension = 2) :
    ((presentationDifferentialBasis k A P hP).baseChange B).det
        ((presentationDifferentialBasis k A P' hP').baseChange B) =
      algebraMap A B (presentationJacobian k A P P' hP hP' : A) :=
  det_baseChange B _ _

end Presentations

end KltDP.Geometry.TopDifferentialFrameBaseChange

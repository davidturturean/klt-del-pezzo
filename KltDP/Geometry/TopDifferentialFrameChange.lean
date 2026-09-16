import KltDP.Geometry.AffineTopDifferentialFrame

/-!
# Change of top differential frame: the determinant unit and its cocycle identity

F04 §4.3 route (b) builds the canonical sheaf `ω_X = ∧²Ω_X` of a smooth surface by gluing the chart
line bundles of `AffineTopDifferentialFrame` along the Jacobian transition determinants.  The
accepted local input is already there: on a standard-smooth affine chart of relative dimension two,
`standardSmoothTopDifferentialSheafIso` trivialises the tilde of `⋀[A]^2 Ω_{A/k}` using
`determinantEquiv` of a Kähler basis.  What route (b) still needs is the *comparison* of two such
frames, and the cocycle identity that lets the comparison units feed `TransitionUnitGluing.IsCocycle`.

This module supplies exactly that, at the level of modules — no scheme, no sheaf, and in particular
none of the over-site machinery on which `deg K_{P¹} = −2` is blocked:

* **`topWedge_eq_det_smul`**: two bases have proportional top wedges,
  `⋀ b' = (b.det b') • ⋀ b`;
* **`det_mul_det_eq_one`**, hence **`frameChangeUnit b b' : Aˣ`**, the determinant of the change of
  basis, with inverse `b'.det b`;
* **`determinantEquiv_frameChange`**: the `b`-frame coordinate of the `b'`-frame is that unit —
  i.e. the transition unit of the two chart trivialisations, in the same "evaluate the other chart's
  `1`" form the atlas machinery uses;
* **`frameChangeUnit_self`** and **`frameChangeUnit_mul`** (`b.det b' * b'.det b'' = b.det b''`):
  normalisation and the triple-overlap identity, which are the two fields of `IsCocycle`.

For a standard-smooth algebra of relative dimension two these are the Jacobian determinants of a
coordinate change, `presentationJacobian`.

Nothing is admitted here; everything is proved from the accepted `determinantEquiv` API
(`determinantEquiv_apply_wedge`, `determinantEquiv_basis_wedge`, `determinantEquiv_symm_apply`) and
the pinned `Basis.det`.
-/

noncomputable section

open KltDP.Geometry.AffineTopDifferentialFrame

universe u v

namespace KltDP.Geometry.TopDifferentialFrameChange

section Frames

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M] {n : ℕ}

/-- The inverse frame map sends `1` to the wedge of the basis. -/
theorem determinantEquiv_symm_one (b : Basis (Fin n) A M) :
    (determinantEquiv b).symm 1 = exteriorPower.ιMulti A n b := by
  rw [determinantEquiv_symm_apply, one_smul]

/-- **Two frames are proportional**: the top wedge of `b'` is `b.det b'` times that of `b`. -/
theorem topWedge_eq_det_smul (b b' : Basis (Fin n) A M) :
    exteriorPower.ιMulti A n b' = (b.det b') • exteriorPower.ιMulti A n b := by
  apply (determinantEquiv b).injective
  simp only [map_smul, determinantEquiv_apply_wedge, Basis.det_self, smul_eq_mul, mul_one]

/-- The two determinants of a change of basis are inverse to each other. -/
theorem det_mul_det_eq_one (b b' : Basis (Fin n) A M) : b.det b' * b'.det b = 1 := by
  have h : exteriorPower.ιMulti A n b' = (b.det b' * b'.det b) • exteriorPower.ιMulti A n b' := by
    conv_lhs => rw [topWedge_eq_det_smul b b', topWedge_eq_det_smul b' b]
    rw [smul_smul]
  have h2 := congrArg (determinantEquiv b') h
  simp only [map_smul, determinantEquiv_apply_wedge, Basis.det_self, smul_eq_mul, mul_one] at h2
  exact h2.symm

/-- **The frame-change unit** (the Jacobian determinant, in the standard-smooth case). -/
def frameChangeUnit (b b' : Basis (Fin n) A M) : Aˣ where
  val := b.det b'
  inv := b'.det b
  val_inv := det_mul_det_eq_one b b'
  inv_val := det_mul_det_eq_one b' b

@[simp]
theorem frameChangeUnit_val (b b' : Basis (Fin n) A M) :
    (frameChangeUnit b b' : A) = b.det b' := rfl

/-- **The transition unit as a chart evaluation**: the `b`-frame coordinate of the `b'`-frame's `1`
is the frame-change unit. -/
theorem determinantEquiv_frameChange (b b' : Basis (Fin n) A M) :
    determinantEquiv b ((determinantEquiv b').symm 1) = (frameChangeUnit b b' : A) := by
  rw [determinantEquiv_symm_one, determinantEquiv_apply_wedge, frameChangeUnit_val]

/-- Normalisation: the first field of `IsCocycle`. -/
theorem frameChangeUnit_self (b : Basis (Fin n) A M) : frameChangeUnit b b = 1 := by
  apply Units.ext
  rw [frameChangeUnit_val, Units.val_one]
  exact b.det_self

/-- The triple-overlap identity for the determinants. -/
theorem det_mul_det_cocycle (b b' b'' : Basis (Fin n) A M) :
    b.det b' * b'.det b'' = b.det b'' := by
  have h : exteriorPower.ιMulti A n b'' =
      (b'.det b'' * b.det b') • exteriorPower.ιMulti A n b := by
    conv_lhs => rw [topWedge_eq_det_smul b' b'', topWedge_eq_det_smul b b']
    rw [smul_smul]
  have h2 := congrArg (determinantEquiv b) h
  simp only [map_smul, determinantEquiv_apply_wedge, Basis.det_self, smul_eq_mul, mul_one] at h2
  rw [h2]
  exact mul_comm _ _

/-- **The cocycle identity**: the second field of `TransitionUnitGluing.IsCocycle`. -/
theorem frameChangeUnit_mul (b b' b'' : Basis (Fin n) A M) :
    frameChangeUnit b b' * frameChangeUnit b' b'' = frameChangeUnit b b'' := by
  apply Units.ext
  rw [Units.val_mul, frameChangeUnit_val, frameChangeUnit_val, frameChangeUnit_val]
  exact det_mul_det_cocycle b b' b''

end Frames

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

/-- **The Jacobian of a change of submersive presentation**: the frame-change unit of the two
Kähler bases of relative dimension two. -/
def presentationJacobian (P P' : Algebra.SubmersivePresentation k A)
    (hP : P.dimension = 2) (hP' : P'.dimension = 2) : Aˣ :=
  frameChangeUnit (presentationDifferentialBasis k A P hP)
    (presentationDifferentialBasis k A P' hP')

theorem presentationJacobian_self (P : Algebra.SubmersivePresentation k A) (hP : P.dimension = 2) :
    presentationJacobian k A P P hP hP = 1 :=
  frameChangeUnit_self _

theorem presentationJacobian_mul (P P' P'' : Algebra.SubmersivePresentation k A)
    (hP : P.dimension = 2) (hP' : P'.dimension = 2) (hP'' : P''.dimension = 2) :
    presentationJacobian k A P P' hP hP' * presentationJacobian k A P' P'' hP' hP'' =
      presentationJacobian k A P P'' hP hP'' :=
  frameChangeUnit_mul _ _ _

end KltDP.Geometry.TopDifferentialFrameChange

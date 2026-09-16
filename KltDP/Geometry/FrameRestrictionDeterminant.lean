import KltDP.Geometry.TopDifferentialFrameChange
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Frame-change determinants under a semilinear restriction

F04 §4.3 route (b) glues the chart line bundles of a rank-`n` module family along the determinants of
the frame changes.  `TopDifferentialFrameChange` compares two frames over one ring and
`TopDifferentialFrameBaseChange` compares them after a *scalar extension* presented as a tensor
product.  The scheme-level assembly needs the same comparison for the restriction maps of a module
family, which are not tensor-product base changes but plain semilinear maps: for opens `V ≤ W` the
restriction `L W → L V` is additive and semilinear over the ring map `Γ(X, W) → Γ(X, V)`.

This module supplies exactly that, at the level of modules — no scheme, no sheaf:

* **`repr_restrict`**: if a semilinear `f : M →ₛₗ[φ] N` carries a basis `b` of `M` to a basis `c` of
  `N`, then it carries coordinates to coordinates, `c.repr (f x) t = φ (b.repr x t)`.
* **`toMatrix_restrict`**: the change-of-basis matrix of the images is the `φ`-image of the original
  change-of-basis matrix.
* **`det_restrict`**, **`frameChangeUnit_restrict`**: hence `c.det c' = φ (b.det b')` and
  `frameChangeUnit c c' = Units.map φ (frameChangeUnit b b')` — the frame-change unit is natural in a
  semilinear restriction, which is the compatibility a cocycle family of transition units needs.

Nothing is admitted here.  The proofs use only the pinned `Basis.sum_repr`, `Basis.repr_sum_self`,
`Basis.toMatrix_apply`, `Basis.det_apply` and `RingHom.map_det`, together with the accepted
`frameChangeUnit` API.
-/

noncomputable section

open KltDP.Geometry.TopDifferentialFrameChange

universe u v w z

namespace KltDP.Geometry.FrameRestrictionDeterminant

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] {φ : A →+* B}
variable {M : Type w} [AddCommGroup M] [Module A M]
variable {N : Type z} [AddCommGroup N] [Module B N]
variable {n : ℕ}

/-- A semilinear map carrying one frame to another carries coordinates to coordinates. -/
theorem repr_restrict (b : Basis (Fin n) A M) (c : Basis (Fin n) B N) (f : M →ₛₗ[φ] N)
    (hf : ∀ t, f (b t) = c t) (x : M) (t : Fin n) :
    c.repr (f x) t = φ (b.repr x t) := by
  have hx : f x = ∑ s : Fin n, φ (b.repr x s) • c s := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smulₛₗ, hf s]
  rw [hx]
  exact congrFun (c.repr_sum_self fun s => φ (b.repr x s)) t

/-- The change-of-basis matrix of the images is the image of the change-of-basis matrix. -/
theorem toMatrix_restrict (b b' : Basis (Fin n) A M) (c c' : Basis (Fin n) B N) (f : M →ₛₗ[φ] N)
    (hb : ∀ t, f (b t) = c t) (hb' : ∀ t, f (b' t) = c' t) :
    c.toMatrix c' = (b.toMatrix b').map φ := by
  ext s t
  rw [Basis.toMatrix_apply, Matrix.map_apply, Basis.toMatrix_apply, ← hb' t,
    repr_restrict b c f hb]

/-- **The frame-change determinant is natural in a semilinear restriction.** -/
theorem det_restrict (b b' : Basis (Fin n) A M) (c c' : Basis (Fin n) B N) (f : M →ₛₗ[φ] N)
    (hb : ∀ t, f (b t) = c t) (hb' : ∀ t, f (b' t) = c' t) :
    c.det c' = φ (b.det b') := by
  have h : c.toMatrix c' = φ.mapMatrix (b.toMatrix b') :=
    toMatrix_restrict b b' c c' f hb hb'
  rw [Basis.det_apply, Basis.det_apply, RingHom.map_det, h]

/-- **The frame-change unit is natural in a semilinear restriction**: the transition units of a
family of chart frames restrict correctly, which is the compatibility `IsCocycle` needs. -/
theorem frameChangeUnit_restrict (b b' : Basis (Fin n) A M) (c c' : Basis (Fin n) B N)
    (f : M →ₛₗ[φ] N) (hb : ∀ t, f (b t) = c t) (hb' : ∀ t, f (b' t) = c' t) :
    frameChangeUnit c c' = Units.map φ.toMonoidHom (frameChangeUnit b b') := by
  apply Units.ext
  rw [frameChangeUnit_val, Units.coe_map]
  exact det_restrict b b' c c' f hb hb'

end KltDP.Geometry.FrameRestrictionDeterminant

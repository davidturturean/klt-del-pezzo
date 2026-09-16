import KltDP.Geometry.AffineTopDifferentialFrame
import Mathlib.Algebra.Exact
import Mathlib.LinearAlgebra.Basis.Fin

/-!
# The determinant map of a split conormal sequence with a chosen equation

For an actual split exact sequence `0 → R → M → N → 0` and an actual
rank-one frame of `N`, this module constructs `N ≃ ∧² M`. Its defining
equation sends the projection of `m` to `f(1) ∧ m`. Consequently the map
is independent of the splitting and the quotient frame, and scaling the
original conormal generator scales the determinant map by the same scalar.

The construction uses the pinned splitting equivalence and the accepted
top-exterior basis equivalence. It does not assume a determinant or
adjunction isomorphism. The actual smooth quotient specialization is in
`SmoothPrincipalConormalDeterminant`; gluing its local maps is separate.
-/

noncomputable section

open KltDP.Geometry.AffineTopDifferentialFrame

universe u v w

namespace KltDP.LinearAlgebra.SplitConormalDeterminant

variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]

/-- Left exterior multiplication as a linear map into the actual exterior square. -/
def leftWedge (x : M) : M →ₗ[R] (⋀[R]^2 M) :=
  (AlternatingMap.ofSubsingleton R M (⋀[R]^2 M) (0 : Fin 1)).symm
    ((exteriorPower.ιMulti R 2).curryLeft x)

theorem leftWedge_apply (x y : M) :
    leftWedge (R := R) x y = exteriorPower.ιMulti R 2 ![x, y] := by
  change exteriorPower.ιMulti R 2 (Matrix.vecCons x (fun _ => y)) = _
  congr 1
  funext i
  fin_cases i <;> rfl

theorem leftWedge_self (x : M) : leftWedge (R := R) x x = 0 := by
  rw [leftWedge_apply]
  exact (exteriorPower.ιMulti R 2).map_eq_zero_of_eq ![x, x]
    (i := 0) (j := 1) rfl Fin.zero_ne_one

theorem leftWedge_smul_apply (r : R) (x y : M) :
    leftWedge (R := R) (r • x) y = r • leftWedge (R := R) x y := by
  change exteriorPower.ιMulti R 2 (Matrix.vecCons (r • x) (fun _ => y)) =
    r • exteriorPower.ιMulti R 2 (Matrix.vecCons x (fun _ => y))
  exact (exteriorPower.ιMulti R 2).map_vecCons_smul (fun _ => y) r x

variable (f : R →ₗ[R] M) (g : M →ₗ[R] N)
  (hex : Function.Exact f g) (hf : Function.Injective f)
  (s : N →ₗ[R] M) (hs : g ∘ₗ s = LinearMap.id) (a : N ≃ₗ[R] R)

/-- The pinned product splitting, retaining its normalization by the original maps. -/
def splitting :
    {e : M ≃ₗ[R] R × N //
      f = e.symm ∘ₗ LinearMap.inl R R N ∧ g = LinearMap.snd R R N ∘ₗ e} :=
  hex.splitSurjectiveEquiv hf ⟨s, hs⟩

/-- The ambient basis determined by the equation and a lifted quotient frame. -/
def basis : Basis (Fin 2) R M :=
  (Basis.finTwoProd R).map
    (((LinearEquiv.refl R R).prodCongr a.symm).trans
      (splitting f g hex hf s hs).val.symm)

theorem basis_zero : basis f g hex hf s hs a 0 = f 1 := by
  rw [basis, Basis.map_apply, Basis.finTwoProd_zero]
  change (splitting f g hex hf s hs).val.symm (1, a.symm 0) = f 1
  rw [map_zero]
  exact (LinearMap.congr_fun (splitting f g hex hf s hs).property.1 1).symm

theorem projection_basis_one : g (basis f g hex hf s hs a 1) = a.symm 1 := by
  rw [basis, Basis.map_apply, Basis.finTwoProd_one]
  change g ((splitting f g hex hf s hs).val.symm (0, a.symm 1)) = a.symm 1
  have h := LinearMap.congr_fun (splitting f g hex hf s hs).property.2
    ((splitting f g hex hf s hs).val.symm (0, a.symm 1))
  simpa only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearMap.snd_apply] using h

/-- The actual determinant equivalence, initially constructed using a splitting. -/
def equiv : N ≃ₗ[R] (⋀[R]^2 M) :=
  a.trans (determinantEquiv (basis f g hex hf s hs a)).symm

/-- The determinant map wedges an ambient lift with the actual conormal generator. -/
theorem equiv_comp_projection :
    (equiv f g hex hf s hs a).toLinearMap ∘ₗ g = leftWedge (f 1) := by
  apply (basis f g hex hf s hs a).ext
  intro i
  fin_cases i
  · change equiv f g hex hf s hs a (g (basis f g hex hf s hs a 0)) =
      leftWedge (f 1) (basis f g hex hf s hs a 0)
    have hzero : g (f 1) = 0 := congr_fun hex.comp_eq_zero 1
    simp only [basis_zero, hzero, map_zero, leftWedge_self]
  · change equiv f g hex hf s hs a (g (basis f g hex hf s hs a 1)) = _
    rw [projection_basis_one]
    change (determinantEquiv (basis f g hex hf s hs a)).symm (a (a.symm 1)) = _
    rw [a.apply_symm_apply, determinantEquiv_symm_apply, one_smul, leftWedge_apply]
    congr 1
    funext i
    fin_cases i
    · exact basis_zero f g hex hf s hs a
    · rfl

theorem equiv_projection_apply (m : M) :
    equiv f g hex hf s hs a (g m) = leftWedge (f 1) m :=
  LinearMap.congr_fun (equiv_comp_projection f g hex hf s hs a) m

/-- Neither the splitting nor the quotient frame changes the constructed map. -/
theorem equiv_eq (s' : N →ₗ[R] M) (hs' : g ∘ₗ s' = LinearMap.id) (a' : N ≃ₗ[R] R) :
    equiv f g hex hf s hs a = equiv f g hex hf s' hs' a' := by
  apply LinearEquiv.ext
  intro n
  have hsn : g (s n) = n := LinearMap.congr_fun hs n
  rw [← hsn, equiv_projection_apply, equiv_projection_apply]

/-- The equation-change law uses the original scalar multiplying the conormal generator. -/
theorem equiv_apply_of_generator_smul
    (f' : R →ₗ[R] M) (hex' : Function.Exact f' g) (hf' : Function.Injective f')
    (s' : N →ₗ[R] M) (hs' : g ∘ₗ s' = LinearMap.id) (a' : N ≃ₗ[R] R)
    (r : R) (hr : f' 1 = r • f 1) (n : N) :
    equiv f' g hex' hf' s' hs' a' n = r • equiv f g hex hf s hs a n := by
  have hsn : g (s n) = n := LinearMap.congr_fun hs n
  rw [← hsn, equiv_projection_apply, equiv_projection_apply, hr, leftWedge_smul_apply]

end KltDP.LinearAlgebra.SplitConormalDeterminant

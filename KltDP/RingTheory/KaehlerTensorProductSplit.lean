import KltDP.RingTheory.KaehlerTensorProductSplitBaseChange
import Mathlib.LinearAlgebra.Prod

/-!
# Absolute Kähler differentials of a tensor product

The two projections are induced by the original universal derivation and
relative base change. Their inverse is the sum of the original differential
maps for the two algebra inclusions. No smoothness, finite presentation,
freeness, field hypothesis or sheaf-level identification is assumed.

The binary module product is the binary direct sum. The general producer
uses an actual algebra pushout; its final specialization uses S tensor_R T.
Bounded reuse checked pinned Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b,
current official Kähler tensor-product source d0fb6fa74fb79fc5b44a1b0a1de55d5c1dda2372,
and targeted public Lean searches. The compatible relative base-change port
is isolated in the companion file; no absolute splitting was found there.
-/

noncomputable section

open TensorProduct KaehlerDifferential

namespace KltDP.KaehlerTensorProductSplit

section Generators

variable (R S B : Type*) [CommRing R] [CommRing S] [CommRing B]
variable [Algebra R S] [Algebra S B]
variable {M : Type*} [AddCommGroup M] [Module B M]

/-- Maps out of base-changed differentials are determined on the original
universal differential generators, with arbitrary actual target coefficients. -/
theorem baseChangeHom_ext (f g : B ⊗[S] Ω[S⁄R] →ₗ[B] M)
    (h : ∀ (b : B) (s : S), f (b ⊗ₜ D R S s) = g (b ⊗ₜ D R S s)) : f = g := by
  apply LinearMap.ext
  intro z
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b w =>
    obtain ⟨w, rfl⟩ := tensorProductTo_surjective R S w
    induction w with
    | zero => simp
    | add x y hx hy => simp only [map_add, tmul_add, hx, hy]
    | tmul a s =>
      simpa only [Derivation.tensorProductTo_tmul, tmul_smul, smul_tmul'] using h (a • b) s

end Generators

section Pushout

variable (R S T B : Type*) [CommRing R] [CommRing S] [CommRing T] [CommRing B]
variable [Algebra R S] [Algebra R T] [Algebra R B] [Algebra S B] [Algebra T B]
variable [IsScalarTower R S B] [IsScalarTower R T B]
variable [Algebra.IsPushout R S T B]

attribute [local instance] SMulCommClass.of_commMonoid

local instance : Algebra.IsPushout R T S B :=
  Algebra.IsPushout.symm (inferInstance : Algebra.IsPushout R S T B)

/-- The first projection of absolute differentials. -/
def toLeft : Ω[B⁄R] →ₗ[B] B ⊗[S] Ω[S⁄R] :=
  (relativeEquiv R T S B).symm.toLinearMap.comp (KaehlerDifferential.map R T B B)

/-- The second projection of absolute differentials. -/
def toRight : Ω[B⁄R] →ₗ[B] B ⊗[T] Ω[T⁄R] :=
  (relativeEquiv R S T B).symm.toLinearMap.comp (KaehlerDifferential.map R S B B)

@[simp]
theorem toLeft_D_left (s : S) :
    toLeft R S T B (D R B (algebraMap S B s)) = 1 ⊗ₜ D R S s := by
  simp [toLeft, KaehlerDifferential.map_D]

@[simp]
theorem toLeft_D_right (t : T) :
    toLeft R S T B (D R B (algebraMap T B t)) = 0 := by
  simp [toLeft, KaehlerDifferential.map_D]

@[simp]
theorem toRight_D_left (s : S) :
    toRight R S T B (D R B (algebraMap S B s)) = 0 := by
  simp [toRight, KaehlerDifferential.map_D]

@[simp]
theorem toRight_D_right (t : T) :
    toRight R S T B (D R B (algebraMap T B t)) = 1 ⊗ₜ D R T t := by
  simp [toRight, KaehlerDifferential.map_D]

/-- The canonical absolute splitting map. -/
def splitMap : Ω[B⁄R] →ₗ[B] (B ⊗[S] Ω[S⁄R]) × (B ⊗[T] Ω[T⁄R]) :=
  (toLeft R S T B).prod (toRight R S T B)

/-- The inverse candidate: the two original differential inclusion maps. -/
def mergeMap : (B ⊗[S] Ω[S⁄R]) × (B ⊗[T] Ω[T⁄R]) →ₗ[B] Ω[B⁄R] :=
  (KaehlerDifferential.mapBaseChange R S B).coprod
    (KaehlerDifferential.mapBaseChange R T B)

@[simp]
theorem splitMap_D_left (s : S) :
    splitMap R S T B (D R B (algebraMap S B s)) = (1 ⊗ₜ D R S s, 0) := by
  simp [splitMap]

@[simp]
theorem splitMap_D_right (t : T) :
    splitMap R S T B (D R B (algebraMap T B t)) = (0, 1 ⊗ₜ D R T t) := by
  simp [splitMap]

@[simp]
theorem mergeMap_left_tmul_D (b : B) (s : S) :
    mergeMap R S T B (b ⊗ₜ D R S s, 0) = b • D R B (algebraMap S B s) := by
  simp [mergeMap, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]

@[simp]
theorem mergeMap_right_tmul_D (b : B) (t : T) :
    mergeMap R S T B (0, b ⊗ₜ D R T t) = b • D R B (algebraMap T B t) := by
  simp [mergeMap, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]

theorem mergeMap_comp_splitMap :
    (mergeMap R S T B).comp (splitMap R S T B) = LinearMap.id := by
  apply Derivation.liftKaehlerDifferential_unique
  apply Derivation.ext
  intro b
  change mergeMap R S T B (splitMap R S T B (D R B b)) = D R B b
  obtain ⟨b, rfl⟩ := (Algebra.IsPushout.equiv R S T B).surjective b
  induction b with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s t =>
    rw [Algebra.IsPushout.equiv_tmul, Derivation.leibniz]
    simp only [map_add, map_smul, splitMap_D_left, splitMap_D_right,
      mergeMap_left_tmul_D, mergeMap_right_tmul_D, one_smul]

theorem splitMap_comp_mergeMap :
    (splitMap R S T B).comp (mergeMap R S T B) = LinearMap.id := by
  apply LinearMap.prod_ext
  · apply baseChangeHom_ext R S B
    intro b s
    simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.id_apply,
      mergeMap_left_tmul_D, map_smul, splitMap_D_left, Prod.smul_mk,
      smul_zero, smul_tmul', smul_eq_mul, mul_one]
  · apply baseChangeHom_ext R T B
    intro b t
    simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.id_apply,
      mergeMap_right_tmul_D, map_smul, splitMap_D_right, Prod.smul_mk,
      smul_zero, smul_tmul', smul_eq_mul, mul_one]

/-- Absolute differentials of an actual algebra pushout are the direct sum
of the two actual modules obtained by extending scalars. -/
def splitEquiv : Ω[B⁄R] ≃ₗ[B] (B ⊗[S] Ω[S⁄R]) × (B ⊗[T] Ω[T⁄R]) where
  __ := splitMap R S T B
  invFun := mergeMap R S T B
  left_inv := LinearMap.congr_fun (mergeMap_comp_splitMap R S T B)
  right_inv := LinearMap.congr_fun (splitMap_comp_mergeMap R S T B)

@[simp]
theorem splitEquiv_D_left (s : S) :
    splitEquiv R S T B (D R B (algebraMap S B s)) = (1 ⊗ₜ D R S s, 0) :=
  splitMap_D_left R S T B s

@[simp]
theorem splitEquiv_D_right (t : T) :
    splitEquiv R S T B (D R B (algebraMap T B t)) = (0, 1 ⊗ₜ D R T t) :=
  splitMap_D_right R S T B t

end Pushout

section TensorProduct

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Absolute Kähler splitting for the original tensor-product algebra. -/
def tensorProductEquiv :
    Ω[S ⊗[R] T⁄R] ≃ₗ[S ⊗[R] T]
      ((S ⊗[R] T) ⊗[S] Ω[S⁄R]) × ((S ⊗[R] T) ⊗[T] Ω[T⁄R]) :=
  splitEquiv R S T (S ⊗[R] T)

@[simp]
theorem tensorProductEquiv_D_tmul_one (s : S) :
    tensorProductEquiv R S T (D R (S ⊗[R] T) (s ⊗ₜ 1)) =
      (1 ⊗ₜ D R S s, 0) := by
  change splitEquiv R S T (S ⊗[R] T)
    (D R (S ⊗[R] T) (algebraMap S (S ⊗[R] T) s)) = _
  exact splitEquiv_D_left R S T (S ⊗[R] T) s

@[simp]
theorem tensorProductEquiv_D_one_tmul (t : T) :
    tensorProductEquiv R S T (D R (S ⊗[R] T) (1 ⊗ₜ t)) =
      (0, 1 ⊗ₜ D R T t) := by
  change splitEquiv R S T (S ⊗[R] T)
    (D R (S ⊗[R] T) (algebraMap T (S ⊗[R] T) t)) = _
  exact splitEquiv_D_right R S T (S ⊗[R] T) t

end TensorProduct

end KltDP.KaehlerTensorProductSplit

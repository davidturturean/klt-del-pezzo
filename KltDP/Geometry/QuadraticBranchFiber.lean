import KltDP.Geometry.QuadraticRamificationCharts
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# The actual branch fiber is defined by the squared root ideal

The pinned tensor-quotient equivalence identifies the actual categorical
pullback of the branch closed immersion with Spec(A/(t)^2). Both original
projections are retained. The root-zero quotient embeds into this fiber
and maps isomorphically to the original branch scheme.

Reuse: `quotIdealMapEquivTensorQuot` and `pullbackSpecIso`, also used in
the project's AffineBlowupFiber and ExtendedIdealFiber. Here only the
proved identity (b)A=(t)^2 is substituted in those actual universal maps.
The root-zero scheme and the squared-ideal fiber are distinct objects;
neither is silently replaced by a reduction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace KltDP.Geometry.QuadraticCover

variable {R : Type u} [CommRing R]

/-- The actual closed scheme defined by the square of the root ideal. -/
def squaredRootScheme (s : R) : Scheme.{u} :=
  Spec (.of (CoverAlgebra s ⧸ rootIdeal s ^ 2))

def squaredRootι (s : R) : squaredRootScheme s ⟶ affineScheme s :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (rootIdeal s ^ 2)))

instance squaredRootι_isClosedImmersion (s : R) : IsClosedImmersion (squaredRootι s) := by
  unfold squaredRootι
  exact IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk (rootIdeal s ^ 2))) Ideal.Quotient.mk_surjective

/-- The actual branch-base map after killing its pulled-back ideal. -/
def squaredRootToBranchHom (s : R) :
    (R ⧸ branchIdeal s) →+* (CoverAlgebra s ⧸ rootIdeal s ^ 2) :=
  Ideal.Quotient.lift (branchIdeal s)
    ((Ideal.Quotient.mk (rootIdeal s ^ 2)).comp (algebraMap R (CoverAlgebra s)))
    (by
      intro a ha
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [← map_branchIdeal_eq_rootIdeal_sq]
      exact Ideal.mem_map_of_mem _ ha)

def squaredRootToBranch (s : R) : squaredRootScheme s ⟶ branchScheme s :=
  Spec.map (CommRingCat.ofHom (squaredRootToBranchHom s))

/-- The quotient square retains the original quadratic map to the original base. -/
@[reassoc]
theorem squaredRootToBranch_toBase (s : R) :
    squaredRootToBranch s ≫ branchι s = squaredRootι s ≫ toBase s := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- The actual squared-root quotient is the original base-change tensor product. -/
def squaredRootTensorEquiv (s : R) :
    (CoverAlgebra s ⧸ rootIdeal s ^ 2) ≃+* CoverAlgebra s ⊗[R] (R ⧸ branchIdeal s) :=
  (Ideal.quotEquivOfEq (map_branchIdeal_eq_rootIdeal_sq s).symm).trans
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (CoverAlgebra s) (branchIdeal s)).toRingEquiv

@[simp]
theorem squaredRootTensorEquiv_mk (s : R) (a : CoverAlgebra s) :
    squaredRootTensorEquiv s (Ideal.Quotient.mk (rootIdeal s ^ 2) a) =
      a ⊗ₜ[R] (1 : R ⧸ branchIdeal s) := by
  change Algebra.TensorProduct.quotIdealMapEquivTensorQuot (CoverAlgebra s) (branchIdeal s)
    (Ideal.quotEquivOfEq (map_branchIdeal_eq_rootIdeal_sq s).symm
      (Ideal.Quotient.mk (rootIdeal s ^ 2) a)) = _
  rw [Ideal.quotEquivOfEq_mk]
  exact Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk _ _ a

@[simp]
theorem squaredRootTensorEquiv_symm_tmul (s r : R) (a : CoverAlgebra s) :
    (squaredRootTensorEquiv s).symm (a ⊗ₜ[R] (Ideal.Quotient.mk (branchIdeal s) r)) =
      Ideal.Quotient.mk (rootIdeal s ^ 2) (algebraMap R (CoverAlgebra s) r * a) := by
  change (Ideal.quotEquivOfEq (map_branchIdeal_eq_rootIdeal_sq s).symm).symm
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot (CoverAlgebra s) (branchIdeal s)).symm
      (a ⊗ₜ[R] (Ideal.Quotient.mk (branchIdeal s) r))) = _
  rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul,
    Algebra.smul_def, Ideal.quotEquivOfEq_symm]
  rfl

/-- The squared-root closed scheme is the actual categorical inverse image of the branch scheme. -/
def squaredRootFiberIso (s : R) :
    squaredRootScheme s ≅ pullback (toBase s) (branchι s) :=
  Scheme.Spec.mapIso (squaredRootTensorEquiv s).symm.toCommRingCatIso.op ≪≫
    (pullbackSpecIso R (CoverAlgebra s) (R ⧸ branchIdeal s)).symm

/-- The first original fiber projection is the original squared-root quotient inclusion. -/
@[reassoc]
theorem squaredRootFiberIso_hom_fst (s : R) :
    (squaredRootFiberIso s).hom ≫ pullback.fst _ _ = squaredRootι s := by
  change (Spec.map (CommRingCat.ofHom (squaredRootTensorEquiv s).symm.toRingHom) ≫
    (pullbackSpecIso R (CoverAlgebra s) (R ⧸ branchIdeal s)).inv) ≫ pullback.fst _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
  apply congrArg (fun f : CoverAlgebra s →+* (CoverAlgebra s ⧸ rootIdeal s ^ 2) =>
    Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro a
  change (squaredRootTensorEquiv s).symm (a ⊗ₜ[R] (1 : R ⧸ branchIdeal s)) = _
  apply (squaredRootTensorEquiv s).injective
  rw [RingEquiv.apply_symm_apply, squaredRootTensorEquiv_mk]

/-- The second original fiber projection is the original induced branch quotient map. -/
@[reassoc]
theorem squaredRootFiberIso_hom_snd (s : R) :
    (squaredRootFiberIso s).hom ≫ pullback.snd _ _ = squaredRootToBranch s := by
  change (Spec.map (CommRingCat.ofHom (squaredRootTensorEquiv s).symm.toRingHom) ≫
    (pullbackSpecIso R (CoverAlgebra s) (R ⧸ branchIdeal s)).inv) ≫ pullback.snd _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  apply congrArg (fun f : (R ⧸ branchIdeal s) →+* (CoverAlgebra s ⧸ rootIdeal s ^ 2) =>
    Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  change (squaredRootTensorEquiv s).symm
    ((1 : CoverAlgebra s) ⊗ₜ[R] (Ideal.Quotient.mk (branchIdeal s) r)) = _
  rw [squaredRootTensorEquiv_symm_tmul, mul_one]
  rfl

/-- The displayed square is the actual scheme-theoretic branch pullback. -/
theorem squaredRoot_isPullback (s : R) :
    IsPullback (squaredRootι s) (squaredRootToBranch s) (toBase s) (branchι s) :=
  IsPullback.of_iso_pullback ⟨(squaredRootToBranch_toBase s).symm⟩
    (squaredRootFiberIso s) (squaredRootFiberIso_hom_fst s) (squaredRootFiberIso_hom_snd s)

/-- The root-zero scheme is a closed subscheme of the actual squared-root fiber. -/
def rootZeroToSquared (s : R) : rootZeroScheme s ⟶ squaredRootScheme s :=
  Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.factor ((rootIdeal s).pow_le_self (by decide : (2 : ℕ) ≠ 0))))

instance rootZeroToSquared_isClosedImmersion (s : R) :
    IsClosedImmersion (rootZeroToSquared s) := by
  apply IsClosedImmersion.spec_of_surjective
  intro q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨Ideal.Quotient.mk (rootIdeal s ^ 2) a, rfl⟩

/-- The root-zero inclusion retains the actual inclusion in the cover. -/
@[reassoc]
theorem rootZeroToSquared_ι (s : R) :
    rootZeroToSquared s ≫ squaredRootι s = rootZeroι s := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- Its map to the original branch is exactly the already constructed branch isomorphism. -/
@[reassoc]
theorem rootZeroToSquared_toBranch (s : R) :
    rootZeroToSquared s ≫ squaredRootToBranch s = (rootZeroIsoBranch s).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  apply congrArg (fun f : (R ⧸ branchIdeal s) →+* (CoverAlgebra s ⧸ rootIdeal s) =>
    Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rfl

end KltDP.Geometry.QuadraticCover

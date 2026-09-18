import KltDP.Geometry.AffineProductKaehlerTilde
import KltDP.Geometry.AffineModuleTildeSemilinearSections
import KltDP.Geometry.AffineModuleTildePullbackComp

/-!
# Original affine product projections and differential maps

The two maps use the actual scheme-module pullbacks along the original Spec
projections. Their normalized affine transposes are the sections of the
original unit tensors. Composing with the inverse normalized differential
splitting gives maps from the actual pulled-back differential sheaves into
the actual differential sheaf on the product chart.

This bounded producer constructs the maps and fixes their generators.
It does not assume or assert the later global exterior/canonical identity.
Existing semilinear scalar extension avoids replacing the original algebra
scalar actions by definitionally convenient copies.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace KltDP.Geometry.AffineProductKaehler

open AffineKaehlerTildeDerivation AffineModuleTildeSemilinearMap

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

/-- The original first Spec projection. -/
def firstProjection : Spec (CommRingCat.of (S ⊗[R] T)) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] T)))

/-- The original second Spec projection. -/
def secondProjection : Spec (CommRingCat.of (S ⊗[R] T)) ⟶ Spec (CommRingCat.of T) :=
  Spec.map (CommRingCat.ofHom (algebraMap T (S ⊗[R] T)))

/-- The first original projection commutes with the original base morphism. -/
theorem firstProjection_comp :
    firstProjection R S T ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (S ⊗[R] T))) := by
  rw [firstProjection, AffineModuleTilde.specMap_comp_eq,
    ← IsScalarTower.algebraMap_eq R S (S ⊗[R] T)]

/-- The second original projection commutes with the original base morphism. -/
theorem secondProjection_comp :
    secondProjection R S T ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (S ⊗[R] T))) := by
  rw [secondProjection, AffineModuleTilde.specMap_comp_eq,
    ← IsScalarTower.algebraMap_eq R T (S ⊗[R] T)]

/-- The first tensor-unit inclusion is semilinear for the original scalar map. -/
def leftUnitSemilinear :
    differentialModule R S →ₛₗ[algebraMap S (S ⊗[R] T)] splitModule R S T where
  toFun m := (1 ⊗ₜ m, 0)
  map_add' m n := by simp [TensorProduct.tmul_add]
  map_smul' s m := by
    apply Prod.ext
    · change (1 : S ⊗[R] T) ⊗ₜ[S] (s • m) =
        algebraMap S (S ⊗[R] T) s • ((1 : S ⊗[R] T) ⊗ₜ[S] m)
      rw [TensorProduct.tmul_smul, algebraMap_smul]
    · exact (smul_zero _).symm

/-- The second tensor-unit inclusion is semilinear for the original scalar map. -/
def rightUnitSemilinear :
    differentialModule R T →ₛₗ[algebraMap T (S ⊗[R] T)] splitModule R S T where
  toFun m := (0, 1 ⊗ₜ m)
  map_add' m n := by simp [TensorProduct.tmul_add]
  map_smul' t m := by
    apply Prod.ext
    · exact (smul_zero _).symm
    · change (1 : S ⊗[R] T) ⊗ₜ[T] (t • m) =
        algebraMap T (S ⊗[R] T) t • ((1 : S ⊗[R] T) ⊗ₜ[T] m)
      rw [TensorProduct.tmul_smul, algebraMap_smul]

/-- The first original pullback maps to the first summand sheaf. -/
def leftTildeInclusion :
    (schemeModulePullback (firstProjection R S T)).obj (differentialModule R S).tilde ⟶
      (splitModule R S T).tilde :=
  pullbackMap (algebraMap S (S ⊗[R] T)) (leftUnitSemilinear R S T)

/-- The second original pullback maps to the second summand sheaf. -/
def rightTildeInclusion :
    (schemeModulePullback (secondProjection R S T)).obj (differentialModule R T).tilde ⟶
      (splitModule R S T).tilde :=
  pullbackMap (algebraMap T (S ⊗[R] T)) (rightUnitSemilinear R S T)

/-- The actual first pulled-back differential sheaf maps to the split sheaf. -/
def leftComparison :
    (schemeModulePullback (firstProjection R S T)).obj
        (SchemeKaehlerSheaf.baseRingSheaf
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))) ⟶
      (splitModule R S T).tilde :=
  (schemeModulePullback (firstProjection R S T)).map
      (AffineKaehlerTildeLocalization.iso R S).hom ≫ leftTildeInclusion R S T

/-- The actual second pulled-back differential sheaf maps to the split sheaf. -/
def rightComparison :
    (schemeModulePullback (secondProjection R S T)).obj
        (SchemeKaehlerSheaf.baseRingSheaf
          (Spec.map (CommRingCat.ofHom (algebraMap R T)))) ⟶
      (splitModule R S T).tilde :=
  (schemeModulePullback (secondProjection R S T)).map
      (AffineKaehlerTildeLocalization.iso R T).hom ≫ rightTildeInclusion R S T

/-- The first actual projection differential map on the affine chart. -/
def leftDifferentialMap :
    (schemeModulePullback (firstProjection R S T)).obj
        (SchemeKaehlerSheaf.baseRingSheaf
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))) ⟶
      SchemeKaehlerSheaf.baseRingSheaf
        (Spec.map (CommRingCat.ofHom (algebraMap R (S ⊗[R] T)))) :=
  leftComparison R S T ≫ (iso R S T).inv

/-- The second actual projection differential map on the affine chart. -/
def rightDifferentialMap :
    (schemeModulePullback (secondProjection R S T)).obj
        (SchemeKaehlerSheaf.baseRingSheaf
          (Spec.map (CommRingCat.ofHom (algebraMap R T)))) ⟶
      SchemeKaehlerSheaf.baseRingSheaf
        (Spec.map (CommRingCat.ofHom (algebraMap R (S ⊗[R] T)))) :=
  rightComparison R S T ≫ (iso R S T).inv

@[simp]
theorem leftDifferentialMap_comp_iso :
    leftDifferentialMap R S T ≫ (iso R S T).hom = leftComparison R S T := by
  simp [leftDifferentialMap]

@[simp]
theorem rightDifferentialMap_comp_iso :
    rightDifferentialMap R S T ≫ (iso R S T).hom = rightComparison R S T := by
  simp [rightDifferentialMap]

/-- The actual first pullback transpose agrees with d(s tensor 1). -/
theorem leftTildeInclusion_transpose_D (s : S) :
    (AffineModuleTilde.pulledTildeAdjunction (algebraMap S (S ⊗[R] T))).homEquiv
        (differentialModule R S) (splitModule R S T).tilde
        (leftTildeInclusion R S T) (KaehlerDifferential.D R S s) =
      (iso R S T).hom.val.app (op ⊤)
        ((SchemeKaehlerSheaf.baseRingDerivation
          (Spec.map (CommRingCat.ofHom (algebraMap R (S ⊗[R] T))))).d
            (StructureSheaf.toOpen (S ⊗[R] T) ⊤ (s ⊗ₜ 1))) := by
  rw [iso_d_tmul_one]
  exact pullbackMap_transpose_apply (algebraMap S (S ⊗[R] T))
    (leftUnitSemilinear R S T) (KaehlerDifferential.D R S s)

/-- The actual second pullback transpose agrees with d(1 tensor t). -/
theorem rightTildeInclusion_transpose_D (t : T) :
    (AffineModuleTilde.pulledTildeAdjunction (algebraMap T (S ⊗[R] T))).homEquiv
        (differentialModule R T) (splitModule R S T).tilde
        (rightTildeInclusion R S T) (KaehlerDifferential.D R T t) =
      (iso R S T).hom.val.app (op ⊤)
        ((SchemeKaehlerSheaf.baseRingDerivation
          (Spec.map (CommRingCat.ofHom (algebraMap R (S ⊗[R] T))))).d
            (StructureSheaf.toOpen (S ⊗[R] T) ⊤ (1 ⊗ₜ t))) := by
  rw [iso_d_one_tmul]
  exact pullbackMap_transpose_apply (algebraMap T (S ⊗[R] T))
    (rightUnitSemilinear R S T) (KaehlerDifferential.D R T t)

end KltDP.Geometry.AffineProductKaehler

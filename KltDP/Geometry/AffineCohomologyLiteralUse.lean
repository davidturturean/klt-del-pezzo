import KltDP.Literature.Stacks.AffineMorphismCohomology
import KltDP.Geometry.AffineSurfaceEulerSplitConditional

/-!
# Original affine cohomology and Euler values from the reviewed full source

The original scalar actions and every Euler identity below are ordinary
consequences of the full source family, using the already compiled adapters.
No source-comparison hypothesis remains in these public statements.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.NativeAffineCohomology

open ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]

/-- The original affine comparison is linear over the original base ring. -/
def baseRingLinearEquiv {A : Type u} [CommRing A]
    (g : Y ⟶ Spec (CommRingCat.of A)) (M : X.Modules)
    (hM : M.IsQuasicoherent) (n : ℕ) :
    letI := baseRingModule g ((schemeModulePushforward f).obj M) n
    letI := baseRingModule (f ≫ g) M n
    H ((schemeModulePushforward f).obj M) n ≃ₗ[A] H M n :=
  affinePushforwardHBaseRingLinearEquiv
    Literature.Stacks.affine_morphism_cohomology_literal f g M hM n

/-- Equality of the native Euler values for the original affine morphism. -/
theorem eulerCharacteristic_eq {k : Type u} [Field k]
    (g : Y ⟶ Spec (CommRingCat.of k)) (M : X.Modules) (hM : M.IsQuasicoherent) :
    eulerCharacteristic g ((schemeModulePushforward f).obj M) =
      eulerCharacteristic (f ≫ g) M :=
  eulerCharacteristic_affinePushforward
    Literature.Stacks.affine_morphism_cohomology_literal f g M hM

/-- An actual original structure-sheaf splitting gives the surface Euler formula. -/
theorem surfaceEulerOfSplit {k : Type u} [Field k]
    (S : NormalProjectiveSurface k) {Z : Scheme.{u}}
    (g : Z ⟶ S.toScheme) [IsAffineHom g]
    (N : S.toScheme.Modules) [IsCoherentModule N]
    (e : (schemeModulePushforward g).obj (_root_.SheafOfModules.unit Z.ringCatSheaf) ≅
      _root_.SheafOfModules.unit S.toScheme.ringCatSheaf ⊞ N) :
    eulerCharacteristic (g ≫ S.structureMorphism) (_root_.SheafOfModules.unit Z.ringCatSheaf) =
      eulerCharacteristic S.structureMorphism (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) +
        eulerCharacteristic S.structureMorphism N :=
  eulerCharacteristic_structureSheaf_of_pushforward_biprod
    Literature.Stacks.affine_morphism_cohomology_literal S g N e

end KltDP.Geometry.NativeAffineCohomology

#check @KltDP.Geometry.NativeAffineCohomology.baseRingLinearEquiv
#check @KltDP.Geometry.NativeAffineCohomology.surfaceEulerOfSplit
#print axioms KltDP.Geometry.NativeAffineCohomology.baseRingLinearEquiv
#print axioms KltDP.Geometry.NativeAffineCohomology.eulerCharacteristic_eq
#print axioms KltDP.Geometry.NativeAffineCohomology.surfaceEulerOfSplit

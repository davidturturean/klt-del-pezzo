import KltDP.Geometry.AffinePushforwardCohomologyConditional
import KltDP.Geometry.SurfaceBiprodEuler
import KltDP.Geometry.SchemePushforwardSplitTensor
import KltDP.Geometry.InvertibleSheafTensor
import KltDP.Geometry.PicardEulerValue
import KltDP.Geometry.CartierPicardComparison
import KltDP.Geometry.InvertibleCoherentModule
import KltDP.Geometry.SchemeInvertibleSheafPullback

/-!
# Original pulled-line Euler values from an actual affine splitting

The full natural affine cohomology comparison is retained as an explicit
source hypothesis. The original pushforward splitting and the proved
projection formula then give the Euler value of every original pulled
line, and hence of every class in the actual Picard group.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
universe u

namespace KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance splitLineEulerModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
local instance splitLineEulerSectionComm (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.val.obj U) := fun U => by
  change IsMulCommutative (X.presheaf.obj U)
  exact ⟨⟨fun a b => mul_comm a b⟩⟩

variable (hAffine : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsAffineHom f] (n : ℕ),
    ∃ e : ∀ (M : X.Modules), M.IsQuasicoherent →
      H ((schemeModulePushforward f).obj M) n ≃+ H M n,
      ∀ (M N : X.Modules) (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent)
        (φ : M ⟶ N) (x : H ((schemeModulePushforward f).obj M) n),
        e N hN ((zariskiFunctor Y n).map ((schemeModulePushforward f).map φ) x) =
          (zariskiFunctor X n).map φ (e M hM x))

include hAffine

variable {k : Type u} [Field k] (S : NormalProjectiveSurface k) {Y : Scheme.{u}}
  (f : Y ⟶ S.toScheme) [IsAffineHom f] (N : InvertibleSheaf S.toScheme)
  (e : (schemeModulePushforward f).obj (_root_.SheafOfModules.unit Y.ringCatSheaf) ≅
    _root_.SheafOfModules.unit S.toScheme.ringCatSheaf ⊞ N.obj)

include e

/-- The actual original twisted pushforward splitting gives its Euler sum. -/
theorem eulerCharacteristic_pullbackLine_of_split (L : InvertibleSheaf S.toScheme) :
    eulerCharacteristic (f ≫ S.structureMorphism) ((schemeModulePullback f).obj L.obj) =
      eulerCharacteristic S.structureMorphism L.obj +
        eulerCharacteristic S.structureMorphism (N.obj ⊗ L.obj) := by
  letI : IsLocallyNoetherian S.toScheme := S.isLocallyNoetherian
  letI : KltDP.SheafOfModules.IsInvertible (R := S.toScheme.ringCatSheaf) (N.obj ⊗ L.obj) :=
    InvertibleSheafTensor.isInvertible_tensor N L
  have hL : ((schemeModulePullback f).obj L.obj).IsQuasicoherent :=
    show (pullbackInvertibleSheaf f L).obj.IsQuasicoherent from inferInstance
  calc
    _ = eulerCharacteristic S.structureMorphism
        ((schemeModulePushforward f).obj ((schemeModulePullback f).obj L.obj)) :=
      (eulerCharacteristic_affinePushforward hAffine f S.structureMorphism _ hL).symm
    _ = eulerCharacteristic S.structureMorphism (L.obj ⊞ (N.obj ⊗ L.obj)) :=
      eulerCharacteristic_eq_of_iso S.structureMorphism (SchemePushforwardSplitTensor.iso f N.obj e L)
    _ = _ := S.eulerCharacteristic_biprod L.obj (N.obj ⊗ L.obj)

/-- The same formula descends to the original Picard classes. -/
theorem picardEulerValue_pullback_of_split (p : S.toScheme.Pic) :
    picardEulerValue (f ≫ S.structureMorphism) (schemePicardPullbackHom f p) =
      picardEulerValue S.structureMorphism p +
        picardEulerValue S.structureMorphism (N.toPic * p) := by
  obtain ⟨D, rfl⟩ := cartierPicardClass_surjective S.toScheme p
  let L := cartierDivisorInvertibleSheaf S.toScheme D
  change picardEulerValue (f ≫ S.structureMorphism) (schemePicardPullbackHom f L.toPic) =
    picardEulerValue S.structureMorphism L.toPic +
      picardEulerValue S.structureMorphism (N.toPic * L.toPic)
  have ht : picardEulerValue S.structureMorphism (N.toPic * L.toPic) =
      eulerCharacteristic S.structureMorphism (N.obj ⊗ L.obj) := by
    change skeletonEulerValue S.structureMorphism
      ((N.toPic : Skeleton S.toScheme.Modules) * (L.toPic : Skeleton S.toScheme.Modules)) = _
    rw [InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val, ← Skeleton.toSkeleton_tensorObj]
    rfl
  rw [schemePicardPullbackHom_toPic, picardEulerValue_toPic, picardEulerValue_toPic, ht]
  exact eulerCharacteristic_pullbackLine_of_split hAffine S f N e L

end KltDP.Geometry.ModuleCohomology

#print axioms KltDP.Geometry.ModuleCohomology.picardEulerValue_pullback_of_split

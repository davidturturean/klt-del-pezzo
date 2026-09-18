import KltDP.Geometry.AffinePushforwardCohomologyConditional
import KltDP.Geometry.SurfaceBiprodEuler
import KltDP.Geometry.PicardEulerValue
import KltDP.Geometry.FiniteTypeNoetherian
import KltDP.Geometry.InvertibleCoherentModule
import KltDP.Examples.FrobeniusExceptionalNormal

/-!
# Native cohomology and Euler characteristic from an original affine splitting

The full natural affine cohomology comparison remains an explicit source
hypothesis. An actual isomorphism of the original module pushforward with
a binary direct sum gives the corresponding original base-field cohomology
decomposition. On a normal projective surface, coherence supplies every
finiteness hypothesis for the Euler sum. The final specialization uses the
actual sheaf dual of the original invertible sheaf.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance originalStructureSectionsComm (Z : Scheme.{u}) :
    ∀ U, IsMulCommutative (Z.ringCatSheaf.val.obj U) :=
  fun U => by
    change IsMulCommutative (Z.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩

variable (hAffine : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsAffineHom f] (n : ℕ),
    ∃ e : ∀ (M : X.Modules), M.IsQuasicoherent →
      H ((schemeModulePushforward f).obj M) n ≃+ H M n,
      ∀ (M N : X.Modules) (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent)
        (φ : M ⟶ N) (x : H ((schemeModulePushforward f).obj M) n),
        e N hN ((zariskiFunctor Y n).map ((schemeModulePushforward f).map φ) x) =
          (zariskiFunctor X n).map φ (e M hM x))

include hAffine

variable {k : Type u} [Field k]

/-- An actual pushforward splitting gives a linear decomposition of the
native cohomology in every degree over the original base field. -/
def affinePushforwardSplitHLinearEquiv {Y X : Scheme.{u}}
    (f : Y ⟶ X) [IsAffineHom f] (g : X ⟶ Spec (CommRingCat.of k))
    (M : Y.Modules) (hM : M.IsQuasicoherent) (N P : X.Modules)
    (e : (schemeModulePushforward f).obj M ≅ N ⊞ P) (n : ℕ) :
    (baseFunctor (f ≫ g) n).obj M ≃ₗ[k]
      ((baseFunctor g n).obj N × (baseFunctor g n).obj P) := by
  exact (affinePushforwardHBaseRingLinearEquiv hAffine f g M hM n).symm.trans
    (((baseFunctor g n).mapIso e).toLinearEquiv.trans
      (baseCohomologyBiprodLinearEquiv g N P n))

variable (S : NormalProjectiveSurface k) {Y : Scheme.{u}}
  (f : Y ⟶ S.toScheme) [IsAffineHom f]

/-- The original structure-sheaf Euler value from its actual affine
pushforward splitting. This also accepts an original inverse-cocycle line. -/
theorem eulerCharacteristic_structureSheaf_of_pushforward_biprod
    (N : S.toScheme.Modules) [IsCoherentModule N]
    (e : (schemeModulePushforward f).obj (_root_.SheafOfModules.unit Y.ringCatSheaf) ≅
      _root_.SheafOfModules.unit S.toScheme.ringCatSheaf ⊞ N) :
    eulerCharacteristic (f ≫ S.structureMorphism) (_root_.SheafOfModules.unit Y.ringCatSheaf) =
      eulerCharacteristic S.structureMorphism (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) +
        eulerCharacteristic S.structureMorphism N := by
  letI : IsLocallyNoetherian S.toScheme := S.isLocallyNoetherian
  rw [eulerCharacteristic_structureSheaf_affine hAffine f S.structureMorphism,
    eulerCharacteristic_eq_of_iso S.structureMorphism e]
  exact S.eulerCharacteristic_biprod (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) N

/-- The requested actual-cover formula with the literal dual of the
original line. Its coherence is derived from its existing invertibility proof. -/
theorem eulerCharacteristic_structureSheaf_of_pushforward_unit_dual
    (L : InvertibleSheaf S.toScheme)
    (e : (schemeModulePushforward f).obj (_root_.SheafOfModules.unit Y.ringCatSheaf) ≅
      _root_.SheafOfModules.unit S.toScheme.ringCatSheaf ⊞
        KltDP.SheafOfModules.dual S.toScheme.ringCatSheaf L.obj) :
    eulerCharacteristic (f ≫ S.structureMorphism) (_root_.SheafOfModules.unit Y.ringCatSheaf) =
      eulerCharacteristic S.structureMorphism (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) +
        eulerCharacteristic S.structureMorphism
          (KltDP.SheafOfModules.dual S.toScheme.ringCatSheaf L.obj) := by
  letI : IsLocallyNoetherian S.toScheme := S.isLocallyNoetherian
  letI : KltDP.SheafOfModules.IsInvertible (R := S.toScheme.ringCatSheaf)
      (KltDP.SheafOfModules.dual S.toScheme.ringCatSheaf L.obj) :=
    schemeDualSheaf_isInvertible L
  exact eulerCharacteristic_structureSheaf_of_pushforward_biprod hAffine S f
    (KltDP.SheafOfModules.dual S.toScheme.ringCatSheaf L.obj) e

end KltDP.Geometry.ModuleCohomology

#check @KltDP.Geometry.ModuleCohomology.affinePushforwardSplitHLinearEquiv
#check @KltDP.Geometry.ModuleCohomology.eulerCharacteristic_structureSheaf_of_pushforward_unit_dual
#print axioms KltDP.Geometry.ModuleCohomology.affinePushforwardSplitHLinearEquiv
#print axioms KltDP.Geometry.ModuleCohomology.eulerCharacteristic_structureSheaf_of_pushforward_unit_dual
